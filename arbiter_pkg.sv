package arbiter_pkg;
  import uvm_pkg::*;

  // Parameter declarations.
  parameter HOSTS         = 4;
  parameter AW            = 32;
  parameter DW            = 32;
  parameter BW            = 4;
  parameter TW            = 16;
  parameter TIMEOUT_LIMIT = ({TW{1'b1}});

  `include "uvm_macros.svh"
  `include "arbiter_transaction.sv"
  `include "idel_host_sequence.sv"
  `include "finish_host_sequence.sv"
  `include "random_host_sequence.sv"
  `include "arbiter_host_sequence.sv"
  `include "arbiter_host_sequencer.sv"
  `include "arbiter_host_monitor.sv"
  `include "arbiter_host_driver.sv"
  `include "arbiter_host_agent.sv"
  `include "arbiter_resp_monitor.sv"
  `include "arbiter_resp_driver.sv"
  `include "arbiter_resp_agent.sv"
  `include "arbiter_scoreboard.sv"
  `include "arbiter_config.sv"
  `include "arbiter_env.sv"
  `include "arbiter_test.sv"
  `include "arbiter_test_one_host.sv"
  `include "arbiter_test_two_host.sv"
endpackage : arbiter_pkg
