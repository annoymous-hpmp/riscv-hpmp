Power
===============================

Hammer supports post-P&R power analysis. It provides a simple API to add flags to the power tool call and automatically passes in collateral to the power tool from the place-and-route and post-place-and-route simulation outputs.
This action requires a tool plugin to implement ``HammerPowerTool``.

Power Setup Keys
-------------------------------

* Namespace: ``vlsi.core``

    * ``power_tool_path``
        * Set to the directory containing the tool plugin directory for the power tool, typically ``/path/to/tool_plugin/power``. This will be the parent directory of the directory containing ``__init__.py`` and ``defaults.yml``.
    * ``power_tool``
        * Actual name of the power tool that is setup in the directory ``power_tool_path``, e.g. ``voltus``

Simulation Input Keys
-------------------------------

* Namespace: ``power.inputs``

    * ``database`` (str)

        * Path to the place and route database of the design to be analyzed. This path may be relative to the directory in which ``hammer-vlsi`` is called.

    * ``tb_name`` (str)

        * The name of the testbench/test driver in the simulation.

    * ``tb_dut`` (str)

        * Hierarchical path to the to top level instance of the "dut" from the testbench.

    * ``spefs`` ([str])

        * List of paths to all spef (parasitic extraction) files for the design. This list may include a spef file per MMMC corner. Paths may be relative to the directory in which ``hammer-vlsi`` is called.

    * ``waveforms`` ([str])

        * List of paths to waveforms to be used for dynamic power analysis. Paths may be relative to the directory in which ``hammer-vlsi`` is called.

    * ``start_times`` ([TimeValue])

        * List of analysis start times corresponding to each of the ``waveforms`` used for dynamic power analysis.

    * ``end_times`` ([TimeValue])

        * List of analysis end times corresponding to each of the ``waveforms`` used for dynamic power analysis.

    * ``saifs`` ([str])

        *  List of paths to SAIF (activity files) for dynamic power analysis. Generally generated by a gate-level simulation. Paths may be relative to the directory in which ``hammer-vlsi`` is called.

    * ``extra_corners_only`` (bool)

        * If overridden to ``true``, the power tool will report for only the extra MMMC corners, saving runtime. The typical use case is to only report power and rail analysis for a typical/nominal corner.

Power Inputs
-------------------------------

Currently, Hammer's power analysis requires that place-and-route and post-place-and-route gate-level simulation are run, in addition to setting the keys that are described above. Auto-translation of of Hammer IR to the power tool from those outputs are accomplished using the ``par-to-power`` and ``sim-to-power`` actions, as demonstrated in the "Post-PAR Power Analysis" command below.  The required files for power analysis 
(database, SAIF, SPEF, etc.) are generated and piped to the power tool from the pre-requisite action's outputs.

Power Outputs
-------------------------------

The power tool outputs static and active power estimations into the ``OBJ_DIR/power-rundir/`` directory. Exact report format may vary by tool used.

Power Commands
-------------------------------

Assuming you have finished place-and-route (P&R):

* P&R to Power

    * ``hammer-vlsi -e env.yml -p config.yml -p OBJ_DIR/par-rundir/par-output.json -o OBJ_DIR/par-to-power_input.json --obj_dir OBJ_DIR par-to-power``

* P&R to Simulation

    * ``hammer-vlsi -e env.yml -p config.yml -p OBJ_DIR/par-rundir/par-output.json -o OBJ_DIR/par-to-sim_input.json --obj_dir OBJ_DIR par-to-sim``

* Post-P&R Gate Level Sim

    * ``hammer-vlsi -e env.yml -p config.yml -p OBJ_DIR/par-to-sim_input.json --obj_dir OBJ_DIR sim``

* Simulation to Power

    * ``hammer-vlsi -e env.yml -p config.yml -p OBJ_DIR/sim-rundir/sim-output.json -o OBJ_DIR/sim-to-power_input.json --obj_dir OBJ_DIR sim-to-power``

* Power

    * ``hammer-vlsi -e env.yml -p config.yml -p OBJ_DIR/par-to-power_input.json -p OBJ_DIR/sim-to-power_input.json --obj_dir OBJ_DIR power``
