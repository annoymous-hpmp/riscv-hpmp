.PHONY: $(POWER_CONF)
power-par: $(POWER_CONF) sim-par-debug
power-par-$(VLSI_TOP): $(POWER_CONF) sim-par-debug-$(VLSI_TOP)
power-par: override HAMMER_POWER_EXTRA_ARGS += -p $(POWER_CONF)
power-par-$(VLSI_TOP): override HAMMER_POWER_EXTRA_ARGS += -p $(POWER_CONF)
redo-power-par: $(POWER_CONF)
redo-power-par-$(VLSI_TOP): $(POWER_CONF)
redo-power-par: override HAMMER_EXTRA_ARGS += -p $(POWER_CONF)
redo-power-par-$(VLSI_TOP): override HAMMER_EXTRA_ARGS += -p $(POWER_CONF)
$(OBJ_DIR)/power-par-%/power-output-full.json: private override HAMMER_EXTRA_ARGS += $(HAMMER_POWER_EXTRA_ARGS)
