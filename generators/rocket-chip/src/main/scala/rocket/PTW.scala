// See LICENSE.Berkeley for license details.
// See LICENSE.SiFive for license details.

package freechips.rocketchip.rocket

import Chisel._
import Chisel.ImplicitConversions._
import chisel3.withClock
import chisel3.internal.sourceinfo.SourceInfo
import chisel3.experimental.chiselName
import freechips.rocketchip.config.Parameters
import freechips.rocketchip.subsystem.CacheBlockBytes
import freechips.rocketchip.tile._
import freechips.rocketchip.tilelink._
import freechips.rocketchip.util._
import freechips.rocketchip.util.property
import freechips.rocketchip.diplomaticobjectmodel.model.OMSRAM
import scala.collection.mutable.ListBuffer

class PTWReq(implicit p: Parameters) extends CoreBundle()(p) {
  val addr = UInt(width = vpnBits)
  val need_gpa = Bool()
  val vstage1 = Bool() //DD: this certainly confusing for users, means vsatp should be used
  val stage2 = Bool()
}

class PTWResp(implicit p: Parameters) extends CoreBundle()(p) {
  val ae_ptw = Bool()
  val ae_final = Bool()
  val gf = Bool()
  val hr = Bool()
  val hw = Bool()
  val hx = Bool()
  val pte = new PTE
  val level = UInt(width = log2Ceil(pgLevels))
  val fragmented_superpage = Bool()
  val homogeneous = Bool()
  val gpa = Valid(UInt(vaddrBits.W))

  /* for PMPTW */
  val pmpt_hit = Bool() // Whether the ppn hit in the PMPTable
  val pmpt_r = Bool() // read permission
  val pmpt_w = Bool() // write permission
  val pmpt_x = Bool() // execute permission
  val pmpt_err = Bool() // Any error happend?
}

class TLBPTWIO(implicit p: Parameters) extends CoreBundle()(p)
    with HasCoreParameters {
  val req = Decoupled(Valid(new PTWReq))
  val resp = Valid(new PTWResp).flip
  val ptbr = new PTBR().asInput
  val hgatp = new PTBR().asInput
  val vsatp = new PTBR().asInput
  val status = new MStatus().asInput
  val hstatus = new HStatus().asInput
  val gstatus = new MStatus().asInput
  val pmp = Vec(nPMPs, new PMP).asInput
  val customCSRs = coreParams.customCSRs.asInput
}

class PTWPerfEvents extends Bundle {
  val l2miss = Bool()
  val l2hit = Bool()
  val pte_miss = Bool()
  val pte_hit = Bool()
}

class DatapathPTWIO(implicit p: Parameters) extends CoreBundle()(p)
    with HasCoreParameters {
  val ptbr = new PTBR().asInput
  val hgatp = new PTBR().asInput
  val vsatp = new PTBR().asInput
  val sfence = Valid(new SFenceReq).flip
  val status = new MStatus().asInput
  val hstatus = new HStatus().asInput
  val gstatus = new MStatus().asInput
  val pmp = Vec(nPMPs, new PMP).asInput
  val perf = new PTWPerfEvents().asOutput
  val customCSRs = coreParams.customCSRs.asInput
  val clock_enabled = Bool(OUTPUT)
}

/**
 * structure for a single PTE, it should always contain a ppn
 * */
class PTE(implicit p: Parameters) extends CoreBundle()(p) {
  val ppn = UInt(width = 54)
  val reserved_for_software = Bits(width = 2)
  val d = Bool()
  val a = Bool()
  val g = Bool()
  val u = Bool()
  val x = Bool()
  val w = Bool()
  val r = Bool()
  val v = Bool()

  def table(dummy: Int = 0) = v && !r && !w && !x && !d && !a && !u
  def leaf(dummy: Int = 0) = v && (r || (x && !w)) && a
  def ur(dummy: Int = 0) = sr() && u
  def uw(dummy: Int = 0) = sw() && u
  def ux(dummy: Int = 0) = sx() && u
  def sr(dummy: Int = 0) = leaf() && r
  def sw(dummy: Int = 0) = leaf() && w && d
  def sx(dummy: Int = 0) = leaf() && x
  def isFullPerm(dummy: Int = 0) = uw() && ux()
}

class L2TLBEntry(nSets: Int)(implicit p: Parameters) extends CoreBundle()(p)
    with HasCoreParameters {
  val idxBits = log2Ceil(nSets)
  val tagBits = maxSVAddrBits - pgIdxBits - idxBits + (if (usingHypervisor) 1 else 0)
  val tag = UInt(width = tagBits)
  val ppn = UInt(width = ppnBits)
  val d = Bool()
  val a = Bool()
  val u = Bool()
  val x = Bool()
  val w = Bool()
  val r = Bool()

}

@chiselName
class PTW(n: Int)(implicit edge: TLEdgeOut, p: Parameters) extends CoreModule()(p) {
  val io = new Bundle {
    val requestor = Vec(n, new TLBPTWIO).flip
    val mem = new HellaCacheIO
    val dpath = new DatapathPTWIO
  }

  /**
   * TODO(DD): what's omSRAM and the collection.mutable here? 
   * */
  val omSRAMs = collection.mutable.ListBuffer[OMSRAM]()

  /**
   * Possible states of PTW module
   * */
  val s_ready :: s_req :: s_wait1 :: s_dummy1 :: s_wait2 :: s_wait3 :: s_dummy2 :: s_fragment_superpage :: s_check_pmpt :: Nil = Enum(UInt(), 9)
  val state = Reg(init=s_ready)

  /* States for PMP Table begin ===== */
  val pmptable_flag = RegInit(false.B)
  val pmptable_counter = RegInit(0.U(8.W))
  // We have PMP in io.dpath.pmp
  val pmp = Module(new PMPChecker(3)) // 3 is the lgMaxSize, 8Bytes

  val pmpt_base  = RegInit(0.U((paddrBits).W)) // The base addr of a PMPTable
  val pmpt_offset = RegInit(0.U((ppnBits).W)) // The offset (ppn) of PMPtable's range
//  val pmpt_addr = Mux(pmptable_counter>1.U,
//    (pmpt_base << pgIdxBits) + ((pmpt_offset >> (4.U + 9.U)) & 511.U) * xBytes,  //in case pmptable_counter>1, we assume it is 1
//    (pmpt_base << pgIdxBits) + ((pmpt_offset >> (4.U + 9.U*pmptable_counter)) & 511.U) * xBytes)

  val pmpt_addr = (pmpt_base << pgIdxBits) + ((pmpt_offset >> (4.U + 9.U*(pmptable_counter & 1.U ))) & 511.U) * xBytes

  val pmp_less_index = Reg(UInt(log2Ceil(nPMPs + 1).W))
  val pmp_more_index = Reg(UInt(log2Ceil(nPMPs + 1).W))

  val pmptable_needed = pmp.io.t

  //val ae_ptw = Bool()
  //val ae_final = Bool()
  //val gf = Bool()
  //val hr = Bool()
  //val hw = Bool()
  //val hx = Bool()
  //val pte = new PTE
  //val level = UInt(width = log2Ceil(pgLevels))
  //val fragmented_superpage = Bool()
  //val homogeneous = Bool()
  //val gpa = Valid(UInt(vaddrBits.W))

  val dd_r_pte  = Reg(new PTE)
  val dd_resp_gf = Reg(Bool())
  val dd_resp_hr = Reg(Bool())
  val dd_resp_hw = Reg(Bool())
  val dd_resp_hx = Reg(Bool())
  val dd_resp_ae_ptw = Reg(Bool())
  val dd_resp_ae_final = Reg(Bool())
  val dd_level = Reg(UInt(width = log2Ceil(pgLevels)))
  val dd_homogeneous = Reg(Bool())
  val dd_fragmented_superpage = Reg(Bool())
  val dd_gpa_valid = Reg(Bool())
  val dd_gpa_bits = Reg(UInt(vaddrBits.W))

  val dd_pmpt_hit = RegInit(false.B) // Whether the ppn hit in the PMPTable
  val dd_pmpt_r = RegInit(true.B) // read permission
  val dd_pmpt_w = RegInit(true.B) // write permission
  val dd_pmpt_x = RegInit(true.B) // execute permission
  val dd_pmpt_err = RegInit(false.B) // Any error happend?

  // This is used to record addrsses for checking
  // Notably, we should only use upto 6 now (1 for data, and 5 for Sv59 ptes)
  // The width should always be paddrBits
  //val pmpt_check_addr = RegInit(Vec(8, UInt(width=paddrBits)))
  val pmpt_check_addr = Reg(Vec(8, UInt(width=ppnBits)))

  /* States for PMP Table end   ===== */

  /**
   * It seems l2_xx is related to L2TLB.
   * A quick question: why TLB structure is located in PTW module?
   *
   * l2_refill_wire/l2_refill seems to be a signal to: whether we shall update L2TLB
   * */
  val l2_refill_wire = Wire(Bool())

  val arb = Module(new Arbiter(Valid(new PTWReq), n))
  arb.io.in <> io.requestor.map(_.req)
  arb.io.out.ready := (state === s_ready) && !l2_refill_wire

  /**
   * Init the resp valid signals
   * Basically, resp_valid is a vector of registers, length is io.requestor.size
   * The init valid of resp_valid(i) is Bool(false).
   * */
  val resp_valid = Reg(next = Vec.fill(io.requestor.size)(Bool(false)))

  /**
   * What's clock_en and clock_enabled in dpath?
   * And how they are used?
   * What's ClockGate here?
   * */
  val clock_en = state =/= s_ready || l2_refill_wire || arb.io.out.valid || io.dpath.sfence.valid || io.dpath.customCSRs.disableDCacheClockGate
  io.dpath.clock_enabled := usingVM && clock_en
  val gated_clock =
    if (!usingVM || !tileParams.dcache.get.clockGate) clock
    else ClockGate(clock, clock_en, "ptw_clock_gate")
  withClock (gated_clock) { // entering gated-clock domain

  /**
   * Registers used in PTW. There many signals for response here
   * */
  val invalidated = Reg(Bool())
  val count = Reg(UInt(width = log2Ceil(pgLevels)))
  val resp_ae_ptw = Reg(Bool())
  val resp_ae_final = Reg(Bool())
  val resp_gf = Reg(Bool())
  val resp_hr = Reg(Bool())
  val resp_hw = Reg(Bool())
  val resp_hx = Reg(Bool())
  val resp_fragmented_superpage = Reg(Bool())

  val r_req = Reg(new PTWReq)
  val r_req_dest = Reg(Bits())
  val r_pte = Reg(new PTE)
  val r_hgatp = Reg(new PTBR)

  val aux_count = Reg(UInt(log2Ceil(pgLevels).W))
  val aux_pte = Reg(new PTE)
  val gpa_pgoff = Reg(UInt(pgIdxBits.W)) // only valid in resp_gf case
  val stage2 = Reg(Bool())
  val stage2_final = Reg(Bool())

  /**
   * choose satp according to request's vstage1
   * */
  val satp = Mux(arb.io.out.bits.bits.vstage1, io.dpath.vsatp, io.dpath.ptbr)
  // DD: I was confused about the initial_count, what's the meaning?
  val r_hgatp_initial_count = pgLevels - minPgLevels - r_hgatp.additionalPgLevels
  val do_both_stages = r_req.vstage1 && r_req.stage2
  /**
   * DD: I guess it will return max(count, aux_count), but not sure
   * why people use this confusing form.
   */
  val max_count = count max aux_count
  /**
   * It's not very clear to me now.
   * Some guess: the mux is only true when we finished the vstage1 translation,
   *  and we do need two stage translation. Therefore, the vpn should be the gpn.
   *
   *  Otherwise, we should use the r_req.addr, which is the HVA or GVA for stage1.
   */
  val vpn = Mux(r_req.vstage1 && stage2, aux_pte.ppn, r_req.addr)

  /**
   * mem_resp_valid/data is set to io.mem.resp.valid/data by default
   * however, it seems, there is a case that io.mem.uncached_resp
   * should be transferred to mem_resp_valid/data.
   * */
  val mem_resp_valid = RegNext(io.mem.resp.valid)
  val mem_resp_data = RegNext(io.mem.resp.bits.data)
  io.mem.uncached_resp.map { resp =>
    assert(!(resp.valid && io.mem.resp.valid))
    resp.ready := true
    when (resp.valid) {
      mem_resp_valid := true
      mem_resp_data := resp.bits.data
    }
  }

  /* PMP checking here */
  //pmp.io.addr := r_pte.ppn(ppnBits-1, 0) << pgIdxBits

  //Note(DD): we use pmptable_counter-1 because we need know the results of pmp.io
  // when we are in odd num, that means, for 7, 5, 3, 1, we shall get the results
  // instead, the pmp.io is not used when counter is 6, 4, ..
  // That means, when we are in 6, we can caculate the result for 5 in advance,
  // so we can get the results of 5 immediately when the counter turns to 5
  pmp.io.addr := Mux(pmptable_counter === 7.U, r_pte.ppn(ppnBits-1,0) << pgIdxBits, pmpt_check_addr( (pmptable_counter-1) >> 1)(ppnBits-1, 0) << pgIdxBits)
  pmp.io.size := 3 //hard coded the size to 2^3, i.e., 8 bytes
  pmp.io.pmp := (io.dpath.pmp: Seq[PMP])
  pmp.io.prv := PRV.S

  /**
   * Get pte from mem_resp_data
   * */
  val (pte, invalid_paddr) = {
    val tmp = new PTE().fromBits(mem_resp_data)
    val res = Wire(init = tmp)
    // get different valid bits for stage-1 and vstage-1 translation
    res.ppn := Mux(do_both_stages && !stage2, tmp.ppn(vpnBits-1, 0), tmp.ppn(ppnBits-1, 0))
    when (tmp.r || tmp.w || tmp.x) {
      // for superpage mappings, make sure PPN LSBs are zero
      for (i <- 0 until pgLevels-1)
        when (count <= i && tmp.ppn((pgLevels-1-i)*pgLevelBits-1, (pgLevels-2-i)*pgLevelBits) =/= 0) { res.v := false }
        //DD: not sure how above code handle superpages :(
    }
    (res, Mux(do_both_stages && !stage2, (tmp.ppn >> vpnBits) =/= 0, (tmp.ppn >> ppnBits) =/= 0))
  }

  /*
   * Check whether we shall traverse to next pte
   * */
  val traverse = pte.table() && !invalid_paddr && count < pgLevels-1
  val pte_addr = if (!usingVM) 0.U else {
    val vpn_idxs = (0 until pgLevels).map { i =>
      val width = pgLevelBits + (if (i <= pgLevels - minPgLevels) hypervisorExtraAddrBits else 0)
      (vpn >> (pgLevels - i - 1) * pgLevelBits)(width - 1, 0)
    }
    val mask     = Mux(stage2 && count === r_hgatp_initial_count, ((1 << (hypervisorExtraAddrBits + pgLevelBits)) - 1).U, ((1 << pgLevelBits) - 1).U)
    /*
     * From here, we can guess that count is used to counting which level
     * we are now.
     * */
    val vpn_idx  = vpn_idxs(count) & mask
    val size = if (usingHypervisor) vaddrBits else paddrBits
    (((r_pte.ppn << pgLevelBits) | vpn_idx) << log2Ceil(xLen / 8))(size - 1, 0)
  }

  val pte_cache_addr = if (!usingHypervisor) pte_addr else {
    val vpn_idxs = (0 until pgLevels-1).map(i => (aux_pte.ppn >> (pgLevels-i-1)*pgLevelBits)(pgLevelBits-1,0))
    val vpn_idx = vpn_idxs(count)
    (Cat(r_pte.ppn, vpn_idx) << log2Ceil(xLen/8))(vaddrBits-1, 0)
  }
  val stage2_pte_cache_addr = if (!usingHypervisor) 0.U else {
    val vpn_idxs = (0 until pgLevels - 1).map(i => (r_req.addr >> (pgLevels - i - 1) * pgLevelBits)(pgLevelBits - 1, 0))
    val vpn_idx  = vpn_idxs(aux_count)
    (Cat(aux_pte.ppn, vpn_idx) << log2Ceil(xLen / 8))(vaddrBits - 1, 0)
  }

  def makeFragmentedSuperpagePPN(ppn: UInt): Seq[UInt] = {
    (pgLevels-1 until 0 by -1).map(i => Cat(ppn >> (pgLevelBits*i), r_req.addr(((pgLevelBits*i) min vpnBits)-1, 0).padTo(pgLevelBits*i)))
  }

  def makePTECache(s2: Boolean): (Bool, UInt) = {
    val plru = new PseudoLRU(coreParams.nPTECacheEntries)
    val valid = RegInit(0.U(coreParams.nPTECacheEntries.W))
    val tags = Reg(Vec(coreParams.nPTECacheEntries, UInt((if (usingHypervisor) 1 + vaddrBits else paddrBits).W)))
    val data = Reg(Vec(coreParams.nPTECacheEntries, UInt((if (usingHypervisor && s2) vpnBits else ppnBits).W)))
    val can_hit =
      if (s2) count === r_hgatp_initial_count && aux_count < pgLevels-1 && r_req.vstage1 && stage2 && !stage2_final
      else count < pgLevels-1 && Mux(r_req.vstage1, stage2, !r_req.stage2)
    val can_refill =
      if (s2) do_both_stages && !stage2 && !stage2_final
      else can_hit
    val tag =
      if (s2) Cat(true.B, stage2_pte_cache_addr)
      else Cat(r_req.vstage1, pte_cache_addr)

    val hits = tags.map(_ === tag).asUInt & valid
    val hit = hits.orR && can_hit
    when (mem_resp_valid && traverse && can_refill && !hits.orR && !invalidated) {
      val r = Mux(valid.andR, plru.way, PriorityEncoder(~valid))
      valid := valid | UIntToOH(r)
      tags(r) := tag
      data(r) := pte.ppn
      plru.access(r)
    }
    when (hit && state === s_req) { plru.access(OHToUInt(hits)) }
    when (io.dpath.sfence.valid && (!io.dpath.sfence.bits.rs1 || usingHypervisor && io.dpath.sfence.bits.hg)) { valid := 0.U }

    val lcount = if (s2) aux_count else count
    for (i <- 0 until pgLevels-1) {
      ccover(hit && state === s_req && lcount === i, s"PTE_CACHE_HIT_L$i", s"PTE cache hit, level $i")
    }

    (hit, Mux1H(hits, data))
  }

  val (pte_cache_hit, pte_cache_data) = makePTECache(false)
  val (stage2_pte_cache_hit, stage2_pte_cache_data) = makePTECache(true)

  val pte_hit = RegNext(false.B)
  /*
   * Some updates on the performance counters
   * */
  io.dpath.perf.pte_miss := false
  io.dpath.perf.pte_hit := pte_hit && (state === s_req) && !io.dpath.perf.l2hit
  assert(!(io.dpath.perf.l2hit && (io.dpath.perf.pte_miss || io.dpath.perf.pte_hit)),
    "PTE Cache Hit/Miss Performance Monitor Events are lower priority than L2TLB Hit event")

  val l2_refill = RegNext(false.B)
  l2_refill_wire := l2_refill
  io.dpath.perf.l2miss := false
  io.dpath.perf.l2hit := false
  val (l2_hit, l2_error, l2_pte, l2_tlb_ram) = if (coreParams.nL2TLBEntries == 0) (false.B, false.B, Wire(new PTE), None) else {
    val code = new ParityCode
    require(isPow2(coreParams.nL2TLBEntries))
    require(isPow2(coreParams.nL2TLBWays))
    require(coreParams.nL2TLBEntries >= coreParams.nL2TLBWays)
    val nL2TLBSets = coreParams.nL2TLBEntries / coreParams.nL2TLBWays
    require(isPow2(nL2TLBSets))
    val idxBits = log2Ceil(nL2TLBSets)

    val l2_plru = new SetAssocLRU(nL2TLBSets, coreParams.nL2TLBWays, "plru")

    val (ram, omSRAM) =  DescribedSRAM(
      name = "l2_tlb_ram",
      desc = "L2 TLB",
      size = nL2TLBSets,
      data = Vec(coreParams.nL2TLBWays, UInt(width = code.width(new L2TLBEntry(nL2TLBSets).getWidth)))
    )

    val g = Reg(Vec(coreParams.nL2TLBWays, UInt(width = nL2TLBSets)))
    val valid = RegInit(Vec(Seq.fill(coreParams.nL2TLBWays)(0.U(nL2TLBSets.W))))
    val (r_tag, r_idx) = Split(Cat(r_req.vstage1, r_req.addr(maxSVAddrBits-pgIdxBits-1, 0)), idxBits)
    val r_valid_vec = valid.map(_(r_idx)).asUInt
    val r_valid_vec_q = Reg(UInt(coreParams.nL2TLBWays.W))
    val r_l2_plru_way = Reg(UInt(log2Ceil(coreParams.nL2TLBWays max 1).W))
    r_valid_vec_q := r_valid_vec
    r_l2_plru_way := (if (coreParams.nL2TLBWays > 1) l2_plru.way(r_idx) else 0.U)
    when (l2_refill && !invalidated) {
      val entry = Wire(new L2TLBEntry(nL2TLBSets))
      entry := r_pte
      entry.tag := r_tag

      val wmask = if (coreParams.nL2TLBWays > 1) Mux(r_valid_vec_q.andR, UIntToOH(r_l2_plru_way, coreParams.nL2TLBWays), PriorityEncoderOH(~r_valid_vec_q)) else 1.U(1.W)
      ram.write(r_idx, Vec(Seq.fill(coreParams.nL2TLBWays)(code.encode(entry.asUInt))), wmask.asBools)

      val mask = UIntToOH(r_idx)
      for (way <- 0 until coreParams.nL2TLBWays) {
        when (wmask(way)) {
          valid(way) := valid(way) | mask
          g(way) := Mux(r_pte.g, g(way) | mask, g(way) & ~mask)
        }
      }
    }

    when (io.dpath.sfence.valid) {
      val hg = usingHypervisor && io.dpath.sfence.bits.hg
      for (way <- 0 until coreParams.nL2TLBWays) {
        valid(way) :=
          Mux(!hg && io.dpath.sfence.bits.rs1, valid(way) & ~UIntToOH(io.dpath.sfence.bits.addr(idxBits+pgIdxBits-1, pgIdxBits)),
          Mux(!hg && io.dpath.sfence.bits.rs2, valid(way) & g(way),
          0.U))
      }
    }

    val s0_valid = !l2_refill && arb.io.out.fire()
    val s0_suitable = arb.io.out.bits.bits.vstage1 === arb.io.out.bits.bits.stage2 && !arb.io.out.bits.bits.need_gpa
    val s1_valid = RegNext(s0_valid && s0_suitable && arb.io.out.bits.valid)
    val s2_valid = RegNext(s1_valid)
    val s1_rdata = ram.read(arb.io.out.bits.bits.addr(idxBits-1, 0), s0_valid)
    val s2_rdata = s1_rdata.map(s1_rdway => code.decode(RegEnable(s1_rdway, s1_valid)))
    val s2_valid_vec = RegEnable(r_valid_vec, s1_valid)
    val s2_g_vec = RegEnable(Vec(g.map(_(r_idx))), s1_valid)
    val s2_error = (0 until coreParams.nL2TLBWays).map(way => s2_valid_vec(way) && s2_rdata(way).error).orR
    when (s2_valid && s2_error) { valid.foreach { _ := 0.U }}

    val s2_entry_vec = s2_rdata.map(_.uncorrected.asTypeOf(new L2TLBEntry(nL2TLBSets)))
    val s2_hit_vec = (0 until coreParams.nL2TLBWays).map(way => s2_valid_vec(way) && (r_tag === s2_entry_vec(way).tag))
    val s2_hit = s2_valid && s2_hit_vec.orR
    io.dpath.perf.l2miss := s2_valid && !(s2_hit_vec.orR)
    io.dpath.perf.l2hit := s2_hit
    when (s2_hit) {
      l2_plru.access(r_idx, OHToUInt(s2_hit_vec))
      assert((PopCount(s2_hit_vec) === 1.U) || s2_error, "L2 TLB multi-hit")
    }

    val s2_pte = Wire(new PTE)
    s2_pte   := Mux1H(s2_hit_vec, s2_entry_vec)
    s2_pte.g := Mux1H(s2_hit_vec, s2_g_vec)
    s2_pte.v := true

    for (way <- 0 until coreParams.nL2TLBWays) {
      ccover(s2_hit && s2_hit_vec(way), s"L2_TLB_HIT_WAY$way", s"L2 TLB hit way$way")
    }

    omSRAMs += omSRAM
    (s2_hit, s2_error, s2_pte, Some(ram))
  }

  // if SFENCE occurs during walk, don't refill PTE cache or L2 TLB until next walk
  invalidated := io.dpath.sfence.valid || (invalidated && state =/= s_ready)

  /* This is the interfaces for accessing DRAM */
  io.mem.req.valid := state === s_req || state === s_dummy1
  io.mem.req.bits.phys := Bool(true)
  io.mem.req.bits.cmd  := M_XRD
  io.mem.req.bits.size := log2Ceil(xLen/8)
  io.mem.req.bits.signed := false
  io.mem.req.bits.addr := Mux(pmptable_flag, pmpt_addr, pte_addr)
  io.mem.req.bits.idx.foreach(_ := pte_addr)
  io.mem.req.bits.dprv := PRV.S.U   // PTW accesses are S-mode by definition
  io.mem.req.bits.dv := do_both_stages && !stage2
  io.mem.s1_kill := l2_hit || state =/= s_wait1
  io.mem.s2_kill := Bool(false)

  val pageGranularityPMPs = pmpGranularity >= (1 << pgIdxBits)
  require(!usingHypervisor || pageGranularityPMPs, s"hypervisor requires pmpGranularity >= ${1<<pgIdxBits}")

  val pmaPgLevelHomogeneous = (0 until pgLevels) map { i =>
    val pgSize = BigInt(1) << (pgIdxBits + ((pgLevels - 1 - i) * pgLevelBits))
    if (pageGranularityPMPs && i == pgLevels - 1) {
      require(TLBPageLookup.homogeneous(edge.manager.managers, pgSize), s"All memory regions must be $pgSize-byte aligned")
      true.B
    } else {
      TLBPageLookup(edge.manager.managers, xLen, p(CacheBlockBytes), pgSize)(r_pte.ppn << pgIdxBits).homogeneous
    }
  }
  val pmaHomogeneous = pmaPgLevelHomogeneous(count)
  val pmpHomogeneous = new PMPHomogeneityChecker(io.dpath.pmp).apply(r_pte.ppn << pgIdxBits, count)
  val homogeneous = pmaHomogeneous && pmpHomogeneous

  for (i <- 0 until io.requestor.size) {
    //DD: should use the saved data for return in case we also go to pmptable

    io.requestor(i).resp.valid := resp_valid(i)
    io.requestor(i).resp.bits.ae_ptw := Mux(pmptable_flag, dd_resp_ae_ptw, resp_ae_ptw)
    io.requestor(i).resp.bits.ae_final := Mux(pmptable_flag, dd_resp_ae_final, resp_ae_final)
    io.requestor(i).resp.bits.gf := Mux(pmptable_flag, dd_resp_gf, resp_gf)
    io.requestor(i).resp.bits.hr := Mux(pmptable_flag, dd_resp_hr, resp_hr)
    io.requestor(i).resp.bits.hw := Mux(pmptable_flag, dd_resp_hw, resp_hw)
    io.requestor(i).resp.bits.hx := Mux(pmptable_flag, dd_resp_hx, resp_hx)
    io.requestor(i).resp.bits.pte := Mux(pmptable_flag, dd_r_pte, r_pte)
    io.requestor(i).resp.bits.level := Mux(pmptable_flag, dd_level, max_count)
    io.requestor(i).resp.bits.homogeneous := Mux(pmptable_flag, dd_homogeneous, homogeneous || pageGranularityPMPs)
    io.requestor(i).resp.bits.fragmented_superpage := Mux(pmptable_flag, dd_fragmented_superpage, resp_fragmented_superpage && pageGranularityPMPs)
    io.requestor(i).resp.bits.gpa.valid := Mux(pmptable_flag, dd_gpa_valid, r_req.need_gpa)
    io.requestor(i).resp.bits.gpa.bits := Mux(pmptable_flag, dd_gpa_bits,
      Cat(Mux(!stage2_final || !r_req.vstage1 || aux_count === (pgLevels - 1), aux_pte.ppn, makeFragmentedSuperpagePPN(aux_pte.ppn)(aux_count)), gpa_pgoff))
    io.requestor(i).ptbr := io.dpath.ptbr
    io.requestor(i).hgatp := io.dpath.hgatp
    io.requestor(i).vsatp := io.dpath.vsatp
    io.requestor(i).customCSRs := io.dpath.customCSRs
    io.requestor(i).status := io.dpath.status
    io.requestor(i).hstatus := io.dpath.hstatus
    io.requestor(i).gstatus := io.dpath.gstatus
    io.requestor(i).pmp := io.dpath.pmp

    io.requestor(i).resp.bits.pmpt_hit := Mux(pmptable_flag, dd_pmpt_hit, false.B)
    io.requestor(i).resp.bits.pmpt_r := Mux(pmptable_flag, dd_pmpt_r, true.B)
    io.requestor(i).resp.bits.pmpt_w := Mux(pmptable_flag, dd_pmpt_w, true.B)
    io.requestor(i).resp.bits.pmpt_x := Mux(pmptable_flag, dd_pmpt_x, true.B)
    io.requestor(i).resp.bits.pmpt_err := Mux(pmptable_flag, dd_pmpt_err, false.B)

  }

  // control state machine
  val next_state = Wire(init = state)
  state := OptimizationBarrier(next_state)
  val do_switch = Wire(init = false.B)


  switch (state) {
    is (s_ready) {
      when (arb.io.out.fire()) {
        val satp_initial_count = pgLevels - minPgLevels - satp.additionalPgLevels
        val vsatp_initial_count = pgLevels - minPgLevels - io.dpath.vsatp.additionalPgLevels
        val hgatp_initial_count = pgLevels - minPgLevels - io.dpath.hgatp.additionalPgLevels

        r_req := arb.io.out.bits.bits
        r_req_dest := arb.io.chosen
        next_state := Mux(arb.io.out.bits.valid, s_req, s_ready)
        stage2       := arb.io.out.bits.bits.stage2
        stage2_final := arb.io.out.bits.bits.stage2 && !arb.io.out.bits.bits.vstage1
        count       := Mux(arb.io.out.bits.bits.stage2, hgatp_initial_count, satp_initial_count)
        aux_count   := Mux(arb.io.out.bits.bits.vstage1, vsatp_initial_count, 0.U)
        aux_pte.ppn := Mux(arb.io.out.bits.bits.vstage1, io.dpath.vsatp.ppn, arb.io.out.bits.bits.addr)
        resp_ae_ptw := false
        resp_ae_final := false
        resp_gf := false
        resp_hr := true
        resp_hw := true
        resp_hx := true
        resp_fragmented_superpage := false
        r_hgatp := io.dpath.hgatp

        /* Init PMPTable state for a translation */
       //pmptable_counter := 1.U //init with 1
       pmptable_counter := 7.U //init it with 1, so we have 6 times dummy memory ready to simulate PT-pages checking
       pmptable_flag := false

        assert(!arb.io.out.bits.bits.need_gpa || arb.io.out.bits.bits.stage2)
      }
    }
    is (s_req) {
  	printf("[PTW] coreParams.nPTECacheEntries:%d\n", coreParams.nPTECacheEntries)
      //printf("[PTW@s_req] PMPTable flag:%d, pmpt_base:0x%x, pmpt_offset:0x%x, pmpt_addr:0x%x, pmpt_counter:0x%x\n",
      //      pmptable_flag, pmpt_base, pmpt_offset, pmpt_addr, pmptable_counter)
      when (pmptable_flag === false){ // Normal routine
        when(stage2 && count === r_hgatp_initial_count) {
          gpa_pgoff := Mux(aux_count === pgLevels-1, r_req.addr << (xLen/8).log2, stage2_pte_cache_addr)
        }

        pmpt_check_addr(count) := pte_addr >> pgIdxBits
        //printf("[PTW-results] count:0x%x, pte_cache_hit:%d, pte_addr:0x%x\n",
         //   count, pte_cache_hit, pte_addr)
        when (stage2_pte_cache_hit) {
          aux_count := aux_count + 1
          aux_pte.ppn := stage2_pte_cache_data
          pte_hit := true
        }.elsewhen (pte_cache_hit) {
          count := count + 1
          pte_hit := true
        }.otherwise {
          next_state := Mux(io.mem.req.ready, s_wait1, s_req)
        }
      }.otherwise{ // PMPT checking, just checking mem states
          next_state := Mux(io.mem.req.ready, s_wait1, s_req)
      }
    }
    is (s_wait1) {
      //printf("[PTW@s_wait1] here\n")
      // This Mux is for the l2_error case; the l2_hit && !l2_error case is overriden below
      when (pmptable_flag === false) {
        next_state := Mux(l2_hit, s_req, s_wait2)
      }.otherwise{ // PMPT checking, just goto s_wait2
        next_state := s_wait2
      }
    }
    is (s_wait2) {
      //printf("[PTW@s_wait2] here\n")
      next_state := s_wait3
      io.dpath.perf.pte_miss := count < pgLevels-1
      when (io.mem.s2_xcpt.ae.ld) {
        resp_ae_ptw := true
        next_state := s_ready
        resp_valid(r_req_dest) := true
        printf("[PTW] go ready because io.mem.s2_xcpt.ae.ld\n")
      }
    }
    is (s_fragment_superpage) {
      //printf("[PTW] go ready because s_fragment_superpage\n")
      next_state := s_ready
      resp_valid(r_req_dest) := true
      when (!homogeneous) {
        count := pgLevels-1
        resp_fragmented_superpage := true
      }
      when (do_both_stages) {
        resp_fragmented_superpage := true
      }
    }
    // we need yet another state to waiting for PMP return
    is (s_check_pmpt){
          // save the last addr here
          pmpt_check_addr(count+1) := r_pte.ppn(ppnBits-1, 0)
          //printf("[PTW-results] count:0x%x, data_addr:0x%x\n",
          //  count+1, r_pte.ppn(ppnBits-1, 0) << pgIdxBits)
      //printf("[PTW@s_check_pmpt] here\n")
          when (pmptable_needed) {
            next_state := s_req
            pmptable_flag := true

            // update pmpt_base and pmpt_offset, not sure they will be the correct value
            pmpt_base := Mux(pmp.io.t_index >= 15, 0.U,
              io.dpath.pmp(pmp.io.t_index).table_base(io.dpath.pmp(pmp.io.t_index + 1)) )

            pmpt_offset := Mux( pmp.io.t_index === 0 || pmp.io.t_index > 15, 0.U,
              io.dpath.pmp(pmp.io.t_index).offset_ppn(r_pte.ppn(ppnBits-1, 0), 3, 3, io.dpath.pmp(pmp.io.t_index - 1)) )
              //io.dpath.pmp(pmp.io.t_index).offset_ppn(pmpt_check_addr(pmptable_counter >> 1)(ppnBits-1, 0), 3, 3, io.dpath.pmp(pmp.io.t_index - 1)) )

            // DD: we do not have pmpt_base and pmpt_offset now
            //pmpt_addr := (Mux(pmp.io.t_index >= 15, 0.U, io.dpath.pmp(pmp.io.t_index).table_base(io.dpath.pmp(pmp.io.t_index + 1)) ) << pgIdxBits) +  ((Mux( pmp.io.t_index === 0 || pmp.io.t_index > 15, 0.U, io.dpath.pmp(pmp.io.t_index).offset_ppn(r_pte.ppn(ppnBits-1, 0), 3, 3, io.dpath.pmp(pmp.io.t_index-1))) >> 13) & 511.U) * xBytes

            pmp_less_index := pmp.io.t_index - 1
            pmp_more_index := pmp.io.t_index + 1

            //printf("[PTW] detect pmptable needed, pmp.io.t_index:%d, pmpt_base:0x%x, pmpt_offset:0x%x\n lower_bound:0x%x, upper_bound:0x%x, t_base:0x%x\n",
//            printf("[PTW] detect pmptable needed, pmp.io.t_index:%d, pmpt_base:0x%x, pmpt_offset:0x%x\n\n",
//              pmp.io.t_index-1, pmpt_base, pmpt_offset//, pmp_less_index, pmp_more_index
//	       //0, 0, 0
//             // Mux( (pmp.io.t_index-1)>15, 0, io.dpath.pmp(pmp.io.t_index-1).dd_log_addr()),
//             // Mux( (pmp.io.t_index)>15, 0, io.dpath.pmp(pmp.io.t_index).dd_log_addr()),
//             // Mux( (pmp.io.t_index+1)>15, 0, io.dpath.pmp(pmp.io.t_index+1).dd_log_addr()),
//              )
//
            //DD: should also save the current registers for return
            dd_r_pte := r_pte
            dd_resp_gf := resp_gf
            dd_resp_hr := resp_hr
            dd_resp_hw := resp_hw
            dd_resp_hx := resp_hx
            dd_resp_ae_ptw := resp_ae_ptw
            dd_resp_ae_final := resp_ae_final
            dd_level := max_count
            dd_homogeneous := homogeneous || pageGranularityPMPs
            dd_fragmented_superpage := resp_fragmented_superpage && pageGranularityPMPs
            dd_gpa_valid := r_req.need_gpa
            dd_gpa_bits :=
              Cat(Mux(!stage2_final || !r_req.vstage1 || aux_count === (pgLevels - 1), aux_pte.ppn, makeFragmentedSuperpagePPN(aux_pte.ppn)(aux_count)), gpa_pgoff)

          }.otherwise{
            printf("[PTW] go ready because no PMP checking needed\n")
            next_state := s_ready
            resp_valid(r_req_dest) := true
          }
          //printf("[PTW] PMPTable needed:0x%x, pmp.io.t:0x%x, pmpt_base:0x%x, pmpt_offset:0x%x\n", pmptable_needed,
          //  pmp.io.t, pmpt_base, pmpt_offset)
    }
  }

  val merged_pte = {
    val superpage_masks = (0 until pgLevels).map(i => ((BigInt(1) << pte.ppn.getWidth) - (BigInt(1) << (pgLevels-1-i)*pgLevelBits)).U)
    val superpage_mask = superpage_masks(Mux(stage2_final, max_count, (pgLevels-1).U))
    val stage1_ppns = (0 until pgLevels-1).map(i => Cat(pte.ppn(pte.ppn.getWidth-1, (pgLevels-i-1)*pgLevelBits), aux_pte.ppn((pgLevels-i-1)*pgLevelBits-1,0))) :+ pte.ppn
    val stage1_ppn = stage1_ppns(count)
    makePTE(stage1_ppn & superpage_mask, aux_pte)
  }

  r_pte := OptimizationBarrier(
    Mux(l2_hit && !l2_error, l2_pte,
    Mux(state === s_req && !stage2_pte_cache_hit && pte_cache_hit, makePTE(pte_cache_data, l2_pte),
    Mux(do_switch, makeHypervisorRootPTE(r_hgatp, pte.ppn, r_pte),
    Mux(mem_resp_valid, Mux(!traverse && (r_req.vstage1 && stage2), merged_pte, pte),
    Mux(state === s_fragment_superpage && !homogeneous, makePTE(makeFragmentedSuperpagePPN(r_pte.ppn)(count), r_pte),
    Mux(arb.io.out.fire(), Mux(arb.io.out.bits.bits.stage2, makeHypervisorRootPTE(io.dpath.hgatp, io.dpath.vsatp.ppn, r_pte), makePTE(satp.ppn, r_pte)),
    r_pte)))))))

  when (l2_hit && !l2_error) {
    assert(state === s_req || state === s_wait1)
    next_state := s_ready
    resp_valid(r_req_dest) := true
    count := pgLevels-1
    printf("[PTW] go ready because l2_hit && !l2_error\n")
  }
  when (mem_resp_valid) {
    assert(state === s_wait3)
    next_state := s_req
    //printf("[PTW@mem_resp_valid] pmptable_flag:%d, counter:%d\n", pmptable_flag, pmptable_counter)
    when (pmptable_flag){
     // printf("[PTW PMPChecking] got mem_resp_data: 0x%x\n", mem_resp_data)

      //when (pmptable_counter>0.U) {
	  when ( (pmptable_counter & 1.U) === 1.U){
          //1. In odd no, just goto next stage
	        pmpt_base := mem_resp_data>>5.U
            pmptable_counter:= pmptable_counter - 1
      }.elsewhen (pmptable_counter>0.U && pmptable_needed) {
          // 2. In this case, we know that we are not achieving the end,
          //    and the PT pages is also protected by PMPT
          //    So just goto a new round of checking
          val page_index = pmpt_offset & 15.U

          // update PMP perms
          dd_pmpt_r := dd_pmpt_r | mem_resp_data(page_index *4 + 0)
          dd_pmpt_w := dd_pmpt_w | mem_resp_data(page_index *4 + 1)
          dd_pmpt_x := dd_pmpt_x | mem_resp_data(page_index *4 + 2)

          // update the pmpt base & offset so we can start checking the next addr
          // TODO(DD): what if the next is not covered by PMPT?
          pmpt_base := Mux(pmp.io.t_index >= 15, 0.U,
              io.dpath.pmp(pmp.io.t_index).table_base(io.dpath.pmp(pmp.io.t_index + 1)) )

          pmpt_offset := Mux( pmp.io.t_index === 0 || pmp.io.t_index > 15, 0.U,
            io.dpath.pmp(pmp.io.t_index).offset_ppn(pmpt_check_addr((pmptable_counter-1) >> 1)(ppnBits-1, 0), 3, 3, io.dpath.pmp(pmp.io.t_index - 1)) )
	//  printf("[PTW@Debug] t_index:0x%x, pmpt_base:0x%x, pmpt_offset:0x%x, addr: 0x%x\n",
	//	pmp.io.t_index, pmpt_base, pmpt_offset, pmpt_check_addr((pmptable_counter-1) >>1))
        pmptable_counter:= pmptable_counter - 1
        //}
        // update to leaf pmpte_addr
        //pmpt_addr := ((mem_resp_data >> 5.U) << pgIdxBits) + ((pmpt_offset >> 4.U) & 511.U) *xBytes
      }.otherwise {
        // Either we checking both data/PT pages using PMPT, or checkign data pages
        //   only as PT pages are not protected by PMPT
        // Now, we already goto all the data we want, just lemem_resp_dataave
        val page_index = pmpt_offset & 15.U

        dd_pmpt_hit := true.B
        dd_pmpt_r := mem_resp_data(page_index *4 + 0)
        dd_pmpt_w := mem_resp_data(page_index *4 + 1)
        dd_pmpt_x := mem_resp_data(page_index *4 + 2)
        dd_pmpt_err := false.B

    	printf("[PTW@pmpt_ready to leave] pmptable_flag:%d, page_index:%d, pmpt_r:%d, pmpt_w:%d, pmpt_x:%d, pmpt_offset:0x%x\n", pmptable_flag, page_index, dd_pmpt_r, dd_pmpt_w, dd_pmpt_x, pmpt_offset)
        next_state := s_ready
        resp_valid(r_req_dest) := true
      }
    }.elsewhen (traverse) {
      when (do_both_stages && !stage2) { do_switch := true }
      count := count + 1
    }.otherwise {
      val gf = stage2 && !stage2_final && !pte.ur()
      val ae = pte.v && invalid_paddr
      val success = pte.v && !ae && !gf

      when (do_both_stages && !stage2_final && success) {
        when (stage2) {
          stage2 := false
          count := aux_count
        }.otherwise {
          stage2_final := true
          do_switch := true
        }
      }.otherwise {
        // DD: we are ready to leave, and all the data are well-prepared :)
        l2_refill := success && count === pgLevels-1 && !r_req.need_gpa &&
          (!r_req.vstage1 && !r_req.stage2 ||
           do_both_stages && aux_count === pgLevels-1 && pte.isFullPerm())
        count := max_count

        when (pageGranularityPMPs && !(count === pgLevels-1 && (!do_both_stages || aux_count === pgLevels-1))) {
          next_state := s_fragment_superpage
        }.otherwise {
          // got checking pmptable first
          next_state := s_check_pmpt
        }

        resp_ae_final := ae
        resp_gf := gf
        resp_hr := !stage2 || !gf && pte.ur()
        resp_hw := !stage2 || !gf && pte.uw()
        resp_hx := !stage2 || !gf && pte.ux()
      }
    }
  }
  when (io.mem.s2_nack) {
    assert(state === s_wait2)
    next_state := s_req
    printf("[PTW] go back to s_req as s2_nack is triggerd\n")
  }

  when (do_switch) {
    aux_count := Mux(traverse, count + 1, count)
    count := r_hgatp_initial_count
    aux_pte := Mux(traverse, pte, {
      val s1_ppns = (0 until pgLevels-1).map(i => Cat(pte.ppn(pte.ppn.getWidth-1, (pgLevels-i-1)*pgLevelBits), r_req.addr(((pgLevels-i-1)*pgLevelBits min vpnBits)-1,0).padTo((pgLevels-i-1)*pgLevelBits))) :+ pte.ppn
      makePTE(s1_ppns(count), pte)
    })
    stage2 := true
  }

  for (i <- 0 until pgLevels) {
    val leaf = mem_resp_valid && !traverse && count === i
    ccover(leaf && pte.v && !invalid_paddr, s"L$i", s"successful page-table access, level $i")
    ccover(leaf && pte.v && invalid_paddr, s"L${i}_BAD_PPN_MSB", s"PPN too large, level $i")
    ccover(leaf && !mem_resp_data(0), s"L${i}_INVALID_PTE", s"page not present, level $i")
    if (i != pgLevels-1)
      ccover(leaf && !pte.v && mem_resp_data(0), s"L${i}_BAD_PPN_LSB", s"PPN LSBs not zero, level $i")
  }
  ccover(mem_resp_valid && count === pgLevels-1 && pte.table(), s"TOO_DEEP", s"page table too deep")
  ccover(io.mem.s2_nack, "NACK", "D$ nacked page-table access")
  ccover(state === s_wait2 && io.mem.s2_xcpt.ae.ld, "AE", "access exception while walking page table")

  } // leaving gated-clock domain

  private def ccover(cond: Bool, label: String, desc: String)(implicit sourceInfo: SourceInfo) =
    if (usingVM) property.cover(cond, s"PTW_$label", "MemorySystem;;" + desc)

  private def makePTE(ppn: UInt, default: PTE) = {
    val pte = Wire(init = default)
    pte.ppn := ppn
    pte
  }

  private def makeHypervisorRootPTE(hgatp: PTBR, vpn: UInt, default: PTE) = {
    val count = pgLevels - minPgLevels - hgatp.additionalPgLevels
    val idxs = (0 to pgLevels-minPgLevels).map(i => (vpn >> (pgLevels-i)*pgLevelBits))
    val lsbs = Wire(t = UInt(maxHypervisorExtraAddrBits.W), init = idxs(count))
    val pte = Wire(init = default)
    pte.ppn := Cat(hgatp.ppn >> maxHypervisorExtraAddrBits, lsbs)
    pte
  }
}

/** Mix-ins for constructing tiles that might have a PTW */
trait CanHavePTW extends HasTileParameters with HasHellaCache { this: BaseTile =>
  val module: CanHavePTWModule
  val utlbOMSRAMs = collection.mutable.ListBuffer[OMSRAM]()
  var nPTWPorts = 1
  nDCachePorts += usingPTW.toInt
  // configure PMPTW here
  var nPMPTWPorts = 1
  nDCachePorts += 1

}

trait CanHavePTWModule extends HasHellaCacheModule {
  val outer: CanHavePTW
  val ptwPorts = ListBuffer(outer.dcache.module.io.ptw)
  val pmptwPorts = ListBuffer(outer.dcache.module.io.pmptw)
  val ptw = Module(new PTW(outer.nPTWPorts)(outer.dcache.node.edges.out(0), outer.p))
  val pmptw = Module(new PMPTW(outer.nPMPTWPorts)(outer.dcache.node.edges.out(0), outer.p))
  if (outer.usingPTW) {
    dcachePorts += ptw.io.mem
    outer.utlbOMSRAMs ++= ptw.omSRAMs
  }
  dcachePorts += pmptw.io.mem
}

/*
 * The following is the implementation of PMPTable Walker, short as PMPTW.
 * */
class PMPTWReq(implicit p: Parameters) extends CoreBundle()(p) {
  val ppn = UInt(width = ppnBits) //Assume the input is a PPN (4KB-aligned now)
  val prv = UInt(PRV.SZ.W) //The current privilege
  val pmpt_base  = UInt(width = paddrBits) // The base addr of a PMPTable
  val pmpt_offset = UInt(width = ppnBits) // The offset (ppn) of PMPtable's range
  //val pmpt_start = UInt(width = paddrBits) // The start ppn of PMPtable's range
  //val pmpt_end   = UInt(width = paddrBits) // The end ppn of PMPTable's range
}

class PMPTWResp(implicit p: Parameters) extends CoreBundle()(p) {
  val hit = Bool() // Whether the ppn hit in the PMPTable
  val r = Bool() // read permission
  val w = Bool() // write permission
  val x = Bool() // execute permission
  val err = Bool() // Any error happend?
}

class PMPTWIO(implicit p: Parameters) extends CoreBundle()(p)
    with HasCoreParameters {
  val req = Decoupled(Valid(new PMPTWReq))
  val resp = Valid(new PMPTWResp).flip
}

@chiselName
class PMPTW(n: Int)(implicit edge: TLEdgeOut, p: Parameters) extends CoreModule()(p) {
  val io = new Bundle {
    val requestor = Vec(n, new PMPTWIO).flip
    val mem = new HellaCacheIO
  }

  // States for PMPTable walking, two states for one memory access operations
  val s_ready :: s_getRootPMPTE :: s_waitRootPMPTE :: s_getLeafPMPTE :: s_waitLeafPMPTE :: s_done :: Nil = Enum(UInt(), 6)

  /**
   * Registers used in PMPTable Walker
   * */
  val state = Reg(init=s_ready)
  val r_root_pmpte = Reg(UInt(width=vaddrBitsExtended))
  val r_leaf_pmpte = Reg(UInt(width=vaddrBitsExtended))
  val count = Reg(UInt(width = xLen))
  val leaf_pmpte_addr = Reg(UInt(width=vaddrBitsExtended))
  val root_pmpte_addr = Reg(UInt(width=vaddrBitsExtended))

  /**
   * Dispatch multiple requests by Arbiter
   * */
  val arb = Module(new Arbiter(Valid(new PMPTWReq), n))
  arb.io.in <> io.requestor.map(_.req)
  arb.io.out.ready := (state === s_ready)



  /**
   * Initialize some states of PMPTW
   * */
  //io.core.req.ready := Bool(true)

  // The hit is easy to check by checking the boundary
  // val resp_hit = (arb.io.out.bits.bits.pmpt_start <= arb.io.out.bits.bits.ppn) && (arb.io.out.bits.bits.pmpt_end > arb.io.out.bits.bits.ppn)
  val resp_hit = Bool(true) //It's no need to check hitness in this module, we just hardwired to 1
  val resp_r = Reg(Bool(false))
  val resp_w = Reg(Bool(false))
  val resp_x = Reg(Bool(false))
  val resp_err = Reg(Bool(false))

  /* PMPTable: prepare requests to fetch real data from mem */
  io.mem.req.valid := state === s_getRootPMPTE || state === s_getLeafPMPTE
  io.mem.req.bits.phys := Bool(true)
  io.mem.req.bits.cmd  := M_XRD
  io.mem.req.bits.size := log2Ceil(xLen/8)
  io.mem.req.bits.signed := false
  io.mem.req.bits.addr := Mux(state=== s_getRootPMPTE, root_pmpte_addr,
                              leaf_pmpte_addr)
  io.mem.req.bits.idx.foreach(_ := Mux(state=== s_getRootPMPTE, root_pmpte_addr, leaf_pmpte_addr))
  io.mem.req.bits.dprv := PRV.M   // PMPTW accesses are M-mode by definition
  io.mem.req.bits.dv := Bool(false)
  io.mem.s1_kill := Bool(false)
  io.mem.s2_kill := Bool(false)

  /* We should also check uncached_resp here in PMPTW */
  io.mem.uncached_resp.map { resp =>
    assert(!(resp.valid && io.mem.resp.valid))
    resp.ready := true
    when (resp.valid) {
      printf("[PMPTW] Warning! detect uncached_resp in io.mem!\n");
    }
  }
  /* PMPTable: prepare response signals */
  //io.core.resp.valid := Bool(false)
  //io.core.resp.bits.hit := resp_hit
  //io.core.resp.bits.r := resp_r
  //io.core.resp.bits.w := resp_w
  //io.core.resp.bits.x := resp_x
  //io.core.resp.bits.err := resp_err
  
  /**
   * Init the resp valid signals
   * Basically, resp_valid is a vector of registers, length is io.requestor.size
   * The init valid of resp_valid(i) is Bool(false).
   * */
  val resp_valid = Reg(next = Vec.fill(io.requestor.size)(Bool(false)))
  val r_req_dest = Reg(Bits())

  for (i <- 0 until io.requestor.size) {
    io.requestor(i).resp.valid := resp_valid(i)
    io.requestor(i).resp.bits.hit := resp_hit
    io.requestor(i).resp.bits.r := resp_r
    io.requestor(i).resp.bits.w := resp_w
    io.requestor(i).resp.bits.x := resp_x
    io.requestor(i).resp.bits.err := resp_err
  }

  // State machine of PMPTW
  switch (state) {
    is (s_ready) {
      //io.core.resp.valid := Bool(false)
      /* FIXME(DD): here, we hardcoded the shift to 13, which is 9 bits for leaf PMPTE
       * and 4 bits for page index in the leaf PMPTE.
       * As a result, we assume that the hardware must be 64-bits ARCH
       * */
      root_pmpte_addr := (arb.io.out.bits.bits.pmpt_base << pgIdxBits) + (((arb.io.out.bits.bits.pmpt_offset) >> 13.U) & 511.U) *xBytes

      when (arb.io.out.fire()) { //when the request is valid
        r_req_dest := arb.io.chosen
        state := s_getRootPMPTE
        //io.core.req.ready := Bool(false)
        printf("[PMPTW] request is valid, goto getRootPMPTE\n");
      }
    }

    is (s_getRootPMPTE) {
      when (!resp_hit) {
        // not hit, directly goto done
        state := s_done
        printf("[PMPTW] getRootPMPTE: not hit, goto done\n");
      }.otherwise {
        //Now, fetch the root PMPTE first
        when (io.mem.req.ready) {
          state := s_waitRootPMPTE
          // cerntaily, the request will be issued in this cycle,
          // let's wait in another state now
          printf("[PMPTW] getRootPMPTE: io.mem.req is ready (root_pmpte_addr:0x%x, goto waitRoot\n", root_pmpte_addr);
        }
      }
    }

    is (s_waitRootPMPTE) {
      when (io.mem.resp.valid) {
        when (io.mem.resp.bits.has_data) {
          printf("[PMPTW] waitRootPMPTE: resp valid and got data\n");
          r_root_pmpte := io.mem.resp.bits.data
        }.otherwise{
          printf("[PMPTW] waitRootPMPTE: resp valid and no data\n");
        }
        val root_pmpte_v = r_root_pmpte(0)
        val root_pmpte_r = r_root_pmpte(1)
        val root_pmpte_w = r_root_pmpte(2)
        val root_pmpte_x = r_root_pmpte(3)

        when (root_pmpte_v === 0.U){
          //huge page, return no-permission back
          resp_r := false
          resp_w := false
          resp_x := false
          state := s_done
          printf("[PMPTW] waitRootPMPTE: huge page (no-perm), goto done\n");
        }.elsewhen (root_pmpte_r =/= 0 || root_pmpte_w =/= 0 || root_pmpte_x =/= 0){
          //huge page, return permission in rootPTE back
          resp_r := root_pmpte_r
          resp_w := root_pmpte_w
          resp_x := root_pmpte_x
          state := s_done
          printf("[PMPTW] waitRootPMPTE: huge page, goto done\n");
        }.otherwise{
          //Goto leaf PMPTE now!
          leaf_pmpte_addr := ((r_root_pmpte >> 5.U) << pgIdxBits) + (((arb.io.out.bits.bits.pmpt_offset) >> 4.U) & 511.U) *xBytes
          state := s_getLeafPMPTE
          printf("[PMPTW] waitRootPMPTE: goto getLeafPMPTE\n");
        }
      }.elsewhen (io.mem.s2_xcpt.ma.ld || io.mem.s2_xcpt.ma.st || io.mem.s2_xcpt.pf.ld || io.mem.s2_xcpt.pf.st || io.mem.s2_xcpt.gf.ld || io.mem.s2_xcpt.gf.st || io.mem.s2_xcpt.ae.ld || io.mem.s2_xcpt.ae.st) {
        resp_err := true
        state := s_done
        printf("[PMPTW] waitRootPMPTE: error detected, goto done\n");
      }
    }

    is (s_getLeafPMPTE) {
      //Now, fetch the root PMPTE first
      when (io.mem.req.ready) {
        state := s_waitLeafPMPTE
        printf("[PMPTW] getLeaf: io.mem is ready, goto wait\n");
        // cerntaily, the request will be issued in this cycle,
        // let's wait in another state now
      }
    }

    is (s_waitLeafPMPTE) {
      when (io.mem.resp.valid && io.mem.resp.bits.has_data) {
        r_leaf_pmpte := io.mem.resp.bits.data

        /* Let index the real permissions */
        val page_index =  (arb.io.out.bits.bits.pmpt_offset & 16.U)
        val leaf_pmpte_r = r_root_pmpte(page_index*4 + 0)
        val leaf_pmpte_w = r_root_pmpte(page_index*4 + 1)
        val leaf_pmpte_x = r_root_pmpte(page_index*4 + 2)
        val leaf_pmpte_v = r_root_pmpte(page_index*4 + 3) //this is reserved now

        resp_r := leaf_pmpte_r
        resp_w := leaf_pmpte_w
        resp_x := leaf_pmpte_x
        state := s_done
        printf("[PMPTW] waitLeaf: goto done, resp_r:%d, resp_w:%d, resp_x:%d\n",
          resp_r, resp_x, resp_x);
      }.elsewhen (io.mem.s2_xcpt.ma.ld || io.mem.s2_xcpt.ma.st || io.mem.s2_xcpt.pf.ld || io.mem.s2_xcpt.pf.st || io.mem.s2_xcpt.gf.ld || io.mem.s2_xcpt.gf.st || io.mem.s2_xcpt.ae.ld || io.mem.s2_xcpt.ae.st) {
        resp_err := true
        state := s_done
        printf("[PMPTW] waitLeaf: error! goto done\n");
      }
    }

    //TODO(DD): shall we consider s2_nack cases?
    // when (io.mem.s2_nack) {}

    is (s_done) {
      // Now, every thing is ready and prepared
      // Just configure the status accordingly
      //io.core.resp.valid := true
      //io.core.req.ready := true
      resp_valid(r_req_dest) := true
      state := s_ready
    }
  }


} /* End of PMPTable Walker Module */
