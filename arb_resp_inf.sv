///////////////////////////////////////////////////////////////////////////
// MODULE               : arb_resp_inf                                   //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// The interface of the arbiter response slave interface.                //
///////////////////////////////////////////////////////////////////////////
import uvm_pkg::*;
`include "uvm_macros.svh"

interface arb_resp_inf #(
  // Parameter declarations.
  parameter AW            = 32,
  parameter DW            = 32,
  parameter BW            = 4,
  parameter TW            = 16,
  parameter TIMEOUT_LIMIT = ({TW{1'b1}})
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
  logic                 ack;
  logic                 cpu;

//******************************************************************************
// Assertions
//******************************************************************************
  // Auxiliary code to handle the timeout count.
  bit [TW-1:0]  timeout_cnt;
  always @(posedge clk or negedge rst)
  begin
    if (!rst || $rose(wr) || $rose(rd))
      timeout_cnt = 'b0;
    else if (wr || rd)
      timeout_cnt++;
  end

  default clocking DEFCLK @(posedge clk);
  endclocking

  // The signals for read and write turn to 1 together in the response slave.
  property write_and_read;
    $onehot0({wr,rd});
  endproperty
  assert property (write_and_read)
  else `uvm_fatal("assert", "DUT SEND WRITE AND READ SIGNALS TOGETHER")

  // Check that the signals are stable while request is processed until ack
  //  or timeout.
  property stable_signals;
    disable iff
    (
      $rose(wr, @(posedge clk))    ||
      $rose(rd, @(posedge clk))    ||
      ack                          ||
      timeout_cnt==TIMEOUT_LIMIT
    )

    wr || rd |-> $stable(wr)    &&
                 $stable(rd)    &&
                 $stable(addr)  &&
                 $stable(be)    &&
                 $stable(dwr)   &&
                 $stable(cpu);

  endproperty
  assert property (stable_signals)
  else `uvm_fatal("assert","THE SIGNALS CHANGED IN THE RESPONSE BEFORE ACK/TIMEOUT")
//******************************************************************************
// End assertions
//******************************************************************************

endinterface : arb_resp_inf
