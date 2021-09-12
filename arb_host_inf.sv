///////////////////////////////////////////////////////////////////////////
// MODULE               : arb_host_inf                                   //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// The interface of the arbiter host interface.                          //
///////////////////////////////////////////////////////////////////////////
import uvm_pkg::*;
`include "uvm_macros.svh"

interface arb_host_inf #(
  // Parameter declarations.
  parameter AW            = 32,
  parameter DW            = 32,
  parameter BW            = 4
)
(
  input logic clk, rst
);

  // Declare the signals.
  logic                 wr;
  logic                 rd;
  logic        [AW-1:0] addr;
  logic        [BW-1:0] be;
  logic        [DW-1:0] dwr;
  logic        [DW-1:0] drd;
  logic        [   1:0] ack;
  logic                 cpu;

//******************************************************************************
// Assertions
//******************************************************************************
  default clocking DEFCLK @(posedge clk);
  endclocking

  property ack_after_write_or_read;
    ack inside{1,3} |-> wr || rd;
  endproperty
  assert property (ack_after_write_or_read)
  else `uvm_fatal("assert","THE HOST GOT ACK WITHOUT SENDING WRITE/READ SIGNALS")

  // Check that the ack was send for one cycle from the DUT.
  property ack_for_one_cycle;
    $rose(ack) |=> !ack;
  endproperty
  assert property (ack_for_one_cycle)
  else `uvm_error("assert", "The host got ack for more then one cycle")
//******************************************************************************
// End assertions
//******************************************************************************

endinterface : arb_host_inf
