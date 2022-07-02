// See LICENSE.SiFive for license details.

package freechips.rocketchip.rocket

import chisel3._
import chisel3.util.{Cat, log2Ceil}
import Chisel.ImplicitConversions._
import freechips.rocketchip.config._
import freechips.rocketchip.tile._
import freechips.rocketchip.util._

class PMPConfig extends Bundle {
  val l = Bool()
  val res = UInt(1.W)
  val t = Bool() //Table mode
  val a = UInt(2.W)
  val x = Bool()
  val w = Bool()
  val r = Bool()
}

object PMP {
  def lgAlign = 2

  def apply(reg: PMPReg): PMP = {
    val pmp = Wire(new PMP()(reg.p))
    pmp.cfg := reg.cfg
    pmp.addr := reg.addr
    pmp.mask := pmp.computeMask
    pmp
  }
}

class PMPReg(implicit p: Parameters) extends CoreBundle()(p) {
  val cfg = new PMPConfig
  val addr = UInt((paddrBits - PMP.lgAlign).W)

  def reset(): Unit = {
    cfg.a := 0
    cfg.l := 0
  }

  def readAddr = if (pmpGranularity.log2 == PMP.lgAlign) addr else {
    val mask = ((BigInt(1) << (pmpGranularity.log2 - PMP.lgAlign)) - 1).U
    Mux(napot, addr | (mask >> 1), ~(~addr | mask))
  }
  def napot = cfg.a(1)
  def torNotNAPOT = cfg.a(0)
  def tor = !napot && torNotNAPOT
  def cfgLocked = cfg.l
  def addrLocked(next: PMPReg) = cfgLocked || next.cfgLocked && next.tor
  def is_table = cfg.t
  /* 
   * is_table_all means, the PMP table will cover all region. It should use 0 as the lower bound, the table will mantain permissions 
   * for each 16GiB memory. Each 16GiB memory can have different permissions inside, but
   * having the same permission between two 16GiB regions.
   *
   * Normal usage: make the PMPcfg, t=1, A=NAPOT, addr=0xfffff, this will cover all perms in PMPs, and also PMPTable
   * */
  def is_table_all = is_table && napot 
}

class PMP(implicit p: Parameters) extends PMPReg {
  val mask = UInt(paddrBits.W)

  import PMP._
  def computeMask = {
    val base = Cat(addr, cfg.a(0)) | ((pmpGranularity - 1) >> lgAlign)
    Cat(base & ~(base + 1), ((1 << lgAlign) - 1).U)
  }
  private def comparand = ~(~(addr << lgAlign) | (pmpGranularity - 1))

  private def pow2Match(x: UInt, lgSize: UInt, lgMaxSize: Int) = {
    def eval(a: UInt, b: UInt, m: UInt) = ((a ^ b) & ~m) === 0
    /*
     * INFO(DD):
     *  - pmpGranularity, incase of no-hypervisor, is 4. So it's log2 is 2 in most cases
     *  - lgMaxSize is the largest size of a memory access, which is 3 (i.e., 8Bytes) in 64bit arch
     * */
    if (lgMaxSize <= pmpGranularity.log2) {
      eval(x, comparand, mask)
    } else {
      /*
       * INFO(DD): lgSize is the current size for the addr, it should equal or less to lgMaxSize
       *  UIntToOH1 will form something like 0001111, the number of 1 is lgSize, the number of
       *  0 is (lgMaxSize-lgSize)
       * */
      // break up the circuit; the MSB part will be CSE'd
      val lsbMask = mask | UIntToOH1(lgSize, lgMaxSize)
      val msbMatch = eval(x >> lgMaxSize, comparand >> lgMaxSize, mask >> lgMaxSize)
      val lsbMatch = eval(x(lgMaxSize-1, 0), comparand(lgMaxSize-1, 0), lsbMask(lgMaxSize-1, 0))
      msbMatch && lsbMatch
    }
  }

  private def boundMatch(x: UInt, lsbMask: UInt, lgMaxSize: Int) = {
    if (lgMaxSize <= pmpGranularity.log2) {
      x < comparand
    } else {
      // break up the circuit; the MSB part will be CSE'd
      val msbsLess = (x >> lgMaxSize) < (comparand >> lgMaxSize)
      val msbsEqual = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0
      val lsbsLess =  (x(lgMaxSize-1, 0) | lsbMask) < comparand(lgMaxSize-1, 0)
      msbsLess || (msbsEqual && lsbsLess)
    }
  }

  private def lowerBoundMatch(x: UInt, lgSize: UInt, lgMaxSize: Int) =
    !boundMatch(x, UIntToOH1(lgSize, lgMaxSize), lgMaxSize)

  private def upperBoundMatch(x: UInt, lgMaxSize: Int) =
    boundMatch(x, 0.U, lgMaxSize)

  private def rangeMatch(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP) =
    prev.lowerBoundMatch(x, lgSize, lgMaxSize) && upperBoundMatch(x, lgMaxSize)

  private def pow2Homogeneous(x: UInt, pgLevel: UInt) = {
    val maskHomogeneous = pgLevelMap { idxBits => if (idxBits > paddrBits) false.B else mask(idxBits - 1) } (pgLevel)
    maskHomogeneous || (pgLevelMap { idxBits => ((x ^ comparand) >> idxBits) =/= 0 } (pgLevel))
  }

  private def pgLevelMap[T](f: Int => T) = (0 until pgLevels).map { i =>
    f(pgIdxBits + (pgLevels - 1 - i) * pgLevelBits)
  }

  private def rangeHomogeneous(x: UInt, pgLevel: UInt, prev: PMP) = {
    val beginsAfterLower = !(x < prev.comparand)
    val beginsAfterUpper = !(x < comparand)

    val pgMask = pgLevelMap { idxBits => (((BigInt(1) << paddrBits) - (BigInt(1) << idxBits)) max 0).U } (pgLevel)
    val endsBeforeLower = (x & pgMask) < (prev.comparand & pgMask)
    val endsBeforeUpper = (x & pgMask) < (comparand & pgMask)

    endsBeforeLower || beginsAfterUpper || (beginsAfterLower && endsBeforeUpper)
  }

  // returns whether this PMP completely contains, or contains none of, a page
  def homogeneous(x: UInt, pgLevel: UInt, prev: PMP): Bool =
    Mux(napot, pow2Homogeneous(x, pgLevel), !torNotNAPOT || rangeHomogeneous(x, pgLevel, prev))

  // returns whether this matching PMP fully contains the access
  def aligned(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP): Bool = if (lgMaxSize <= pmpGranularity.log2) true.B else {
    val lsbMask = UIntToOH1(lgSize, lgMaxSize)
    val straddlesLowerBound = ((x >> lgMaxSize) ^ (prev.comparand >> lgMaxSize)) === 0 && (prev.comparand(lgMaxSize-1, 0) & ~x(lgMaxSize-1, 0)) =/= 0
    val straddlesUpperBound = ((x >> lgMaxSize) ^ (comparand >> lgMaxSize)) === 0 && (comparand(lgMaxSize-1, 0) & (x(lgMaxSize-1, 0) | lsbMask)) =/= 0
    val rangeAligned = !(straddlesLowerBound || straddlesUpperBound)
    val pow2Aligned = (lsbMask & ~mask(lgMaxSize-1, 0)) === 0
    Mux(napot, pow2Aligned, rangeAligned)
  }

  // returns the offset (ppn) related to the starting PPN of the PMP
  def offset_ppn(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP): UInt = {
    // TODO(DD): currently we only support TOR for PMP table
//    printf("[PMP] offset_ppn: offset_ppn: 0x%x\n",
//      (x - (prev.addr >> pgIdxBits)) )
    Mux(napot, 0.U, (x - ( (prev.addr <<2.U) >> pgIdxBits) ))

	// Note: the 2.U is the PMP_SHIFT
  }

  // returns the base of table related to the PMP table
  def table_base(next: PMP): UInt = {
    //printf("[PMP] table_base: is_table: 0x%x, next.addr: 0x%x\n",
      //is_table, next.addr)
    // return the next.addr only when current PMP is in table mode
    Mux(is_table, next.addr, 0.U)
  }
  def dd_log_addr(): UInt = {
    addr
  }

  // returns whether this PMP matches at least one byte of the access
  def hit(x: UInt, lgSize: UInt, lgMaxSize: Int, prev: PMP): Bool =
    Mux(napot, pow2Match(x, lgSize, lgMaxSize), torNotNAPOT && rangeMatch(x, lgSize, lgMaxSize, prev))
}

// INFO(DD): this is used to check whether PMPs can cover the full range of a page
//           If you do not familiar with foldLeft and case, learn it from Scala
class PMPHomogeneityChecker(pmps: Seq[PMP])(implicit p: Parameters) {
  def apply(addr: UInt, pgLevel: UInt): Bool = {
    pmps.foldLeft((true.B, 0.U.asTypeOf(new PMP))) { case ((h, prev), pmp) =>
      (h && pmp.homogeneous(addr, pgLevel, prev), pmp)
    }._1
  }
}

// INFO(DD): The basic idea is simple here, find a hit PMP, and returns the
//           r/w/x permissios back
//           Missing parts: check the permissions according to the priv-level
//            I guess it's handled by the upper layer
class PMPChecker(lgMaxSize: Int)(implicit val p: Parameters) extends Module
    with HasCoreParameters {
  val io = IO(new Bundle {
    val prv = Input(UInt(PRV.SZ.W))
    val pmp = Input(Vec(nPMPs, new PMP))
    val addr = Input(UInt(paddrBits.W))
    val size = Input(UInt(log2Ceil(lgMaxSize + 1).W))
    val r = Output(Bool())
    val w = Output(Bool())
    val x = Output(Bool())
    val t = Output(Bool()) // Indicate whether the addr is hit in a PMPTable
    val t_index = Output(UInt(log2Ceil(nPMPs + 1).W)) // Indicate the index of hited PMPTable
  })

  val default = if (io.pmp.isEmpty) true.B else io.prv > PRV.S
  val pmp0 = WireInit(0.U.asTypeOf(new PMP))
  pmp0.cfg.r := default
  pmp0.cfg.w := default
  pmp0.cfg.x := default
  /* DD: the below two states are used record the hit PMP index */
  //val count = RegInit(UInt(nPMPs))
  //val res_index = RegInit(0.U)

  /**
   * INFO(DD): this assignment is quitely complicated.
   * Basically, the res is the major of final results, including the permission and 
   * Table-mode bits.
   * Besides, res_index is the index for finnaly hitted index.
   * The temp_index is the guard for the current PMP entries (from nPMPs-1 to 0 basically)
   * */
  val (res, res_index, temp_index) = (io.pmp zip (pmp0 +: io.pmp)).reverse.foldLeft( (pmp0, 0.U, 15.U) ) { case ( (prev, pre_idx, now_idx), (pmp, prevPMP)) =>
    val hit = pmp.hit(io.addr, io.size, lgMaxSize, prevPMP)
    val ignore = default && !pmp.cfg.l
    val aligned = pmp.aligned(io.addr, io.size, lgMaxSize, prevPMP)

    for ((name, idx) <- Seq("no", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty)
      property.cover(pmp.cfg.a === idx, s"The cfg access is set to ${name} access ", "Cover PMP access mode setting")

    property.cover(pmp.cfg.l === 0x1, s"The cfg lock is set to high ", "Cover PMP lock mode setting")
   
    // Not including Write and no Read permission as the combination is reserved
    for ((name, idx) <- Seq("no", "RO", "", "RW", "X", "RX", "", "RWX").zipWithIndex; if name.nonEmpty)
      property.cover((Cat(pmp.cfg.x, pmp.cfg.w, pmp.cfg.r) === idx), s"The permission is set to ${name} access ", "Cover PMP access permission setting")

    for ((name, idx) <- Seq("", "TOR", if (pmpGranularity <= 4) "NA4" else "", "NAPOT").zipWithIndex; if name.nonEmpty) {
      property.cover(!ignore && hit && aligned && pmp.cfg.a === idx, s"The access matches ${name} mode ", "Cover PMP access")
      property.cover(pmp.cfg.l && hit && aligned && pmp.cfg.a === idx, s"The access matches ${name} mode with lock bit high", "Cover PMP access with lock bit")
    }

    val cur = WireInit(pmp)
    //TODO(DD): review the hacking here, we set the perm of the whole page table as r/w/x in the segment
    //          goal: in case the region is hit by someone not using translation (through Page Table)
    cur.cfg.r := Mux(pmp.cfg.t, true.B, aligned && (pmp.cfg.r || ignore))
    cur.cfg.w := Mux(pmp.cfg.t, true.B, aligned && (pmp.cfg.w || ignore))
    cur.cfg.x := Mux(pmp.cfg.t, true.B, aligned && (pmp.cfg.x || ignore))
    cur.cfg.t := aligned && (pmp.cfg.t || ignore)
    (Mux(hit, cur, prev), Mux(hit, now_idx, pre_idx), now_idx-1.U)
  }

  io.r := res.cfg.r
  io.w := res.cfg.w
  io.x := res.cfg.x
  io.t := res.cfg.t
  io.t_index := res_index
}
