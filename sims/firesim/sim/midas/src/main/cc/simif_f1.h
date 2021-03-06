#ifndef __SIMIF_F1_H
#define __SIMIF_F1_H

#include "simif.h"    // from midas

#ifndef SIMULATION_XSIM
#include <fpga_pci.h>
#include <fpga_mgmt.h>
#endif

class simif_f1_t: public virtual simif_t
{
  public:
    simif_f1_t(int argc, char** argv);
    virtual ~simif_f1_t();

    // Unused by F1 since initialization / deinitization is done in the constructor
    virtual void host_init(int argc, char** argv) {};
    virtual int host_finish() { return 0; };

    virtual void write(size_t addr, uint32_t data);
    virtual uint32_t read(size_t addr);
    virtual ssize_t pull(size_t addr, char* data, size_t size);
    virtual ssize_t push(size_t addr, char* data, size_t size);
    uint32_t is_write_ready();
    void check_rc(int rc, char * infostr);
    void fpga_shutdown();
    void fpga_setup(int slot_id);
  private:
    char in_buf[CTRL_BEAT_BYTES];
    char out_buf[CTRL_BEAT_BYTES];
#ifdef SIMULATION_XSIM
    char * driver_to_xsim = "/tmp/driver_to_xsim";
    char * xsim_to_driver = "/tmp/xsim_to_driver";
    int driver_to_xsim_fd;
    int xsim_to_driver_fd;
#else
//    int rc;
    int slot_id;
    int edma_write_fd;
    int edma_read_fd;
    pci_bar_handle_t pci_bar_handle;
#endif
};

#endif // __SIMIF_F1_H
