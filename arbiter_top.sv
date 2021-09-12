///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_top                                    //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// The top file, in which DUT is set and the test is called.             //
///////////////////////////////////////////////////////////////////////////
`include "arbiter_pkg.sv"
`include "arbiter.v"
`include "arb_host_inf.sv"
`include "arb_resp_inf.sv"

module arbiter_top;
  import uvm_pkg::*;
  import arbiter_pkg::*;

  // Variable declarations.
  bit clk;
  bit rst;

  // Interface handlers in order to connect DUT and to set them in the uvm
  //  configuration block.
  arb_host_inf #(AW, DW, BW)                    m_inf(clk, rst);
  arb_host_inf #(AW, DW, BW)                    s_inf(clk, rst);
  arb_host_inf #(AW, DW, BW)                    t_inf(clk, rst);
  arb_host_inf #(AW, DW, BW)                    e_inf(clk, rst);
  arb_resp_inf #(AW, DW, BW, TW, TIMEOUT_LIMIT) r_inf(clk, rst);

  // DUT instance. Connects the Interfaces to the DUT.
  arbiter dut 
  (
    // Master Host
    .mcpu        (m_inf.cpu),
    .maddr       (m_inf.addr),
    .mrd         (m_inf.rd),
    .mwr         (m_inf.wr),
    .mbe         (m_inf.be),
    .mdwr        (m_inf.dwr),
    .mdrd        (m_inf.drd),
    .mack        (m_inf.ack),

     // Slave Host
    .scpu        (s_inf.cpu),
    .saddr       (s_inf.addr),
    .srd         (s_inf.rd),
    .swr         (s_inf.wr),
    .sbe         (s_inf.be),
    .sdwr        (s_inf.dwr),
    .sdrd        (s_inf.drd),
    .sack        (s_inf.ack),

     // Test Host
    .tcpu        (t_inf.cpu),
    .taddr       (t_inf.addr),
    .trd         (t_inf.rd),
    .twr         (t_inf.wr),
    .tbe         (t_inf.be),
    .tdwr        (t_inf.dwr),
    .tdrd        (t_inf.drd),
    .tack        (t_inf.ack),

     // Extra Host
    .ecpu        (e_inf.cpu),
    .eaddr       (e_inf.addr),
    .erd         (e_inf.rd),
    .ewr         (e_inf.wr),
    .ebe         (e_inf.be),
    .edwr        (e_inf.dwr),
    .edrd        (e_inf.drd),
    .eack        (e_inf.ack),

     // device
    .cpu_bus     (r_inf.cpu),
    .add_bus     (r_inf.addr),
    .rd_bus      (r_inf.rd),
    .wr_bus      (r_inf.wr),
    .byte_en     (r_inf.be),
    .data_bus_wr (r_inf.dwr),
    .data_bus_rd (r_inf.drd),
    .ack_bus     (r_inf.ack),

     // General
    .clk         (clk),
    .reset_n     (rst)
  );


  // Clock generation.
  always #5 clk = !clk;

  // Send the reset signal.
  initial begin
    rst = 1;
    #10 rst = 0;
    #20 rst = 1;
  end

  // Set the cpu signals for all the hosts.
  initial begin
    m_inf.cpu = 1;
    s_inf.cpu = 0;
    t_inf.cpu = 0;
    e_inf.cpu = 0;
  end

  initial begin
    // Registers the Interfaces in the configuration block so that other blocks
    //  can use them.
    uvm_config_db#(virtual arb_host_inf)::set(null,"*.host_0.*", "vif",m_inf);
    uvm_config_db#(virtual arb_host_inf)::set(null,"*.host_1.*", "vif",s_inf);
    uvm_config_db#(virtual arb_host_inf)::set(null,"*.host_2.*", "vif",t_inf);
    uvm_config_db#(virtual arb_host_inf)::set(null,"*.host_3.*", "vif",e_inf);
    uvm_config_db#(virtual arb_resp_inf)::set(null,"*.response_slave.*","vif",r_inf);
    
    //Executes the test
    run_test("arbiter_test");
  end


//******************************************************************************
// Assertions
//******************************************************************************
  default clocking DEFCLK @(posedge clk);
  endclocking

  // Check that write/read is 1 only when it's 1 in at least one host.
  property write_resp_is_write_host;
    r_inf.wr |-> m_inf.wr || s_inf.wr || t_inf.wr || e_inf.wr;
  endproperty
  assert property (write_resp_is_write_host)
  else `uvm_fatal("assert", "THERE IS NO HOST THAT SIGNAL TO WRITE")

  property read_resp_is_read_host;
    r_inf.rd |-> m_inf.rd || s_inf.rd || t_inf.rd || e_inf.rd;
  endproperty
  assert property (read_resp_is_read_host)
  else `uvm_fatal("assert", "THERE IS NO HOST THAT SIGNAL TO READ")

  // Check that the DUT set all it's field to zero in the response slave
  //  when ack occur.
  property zero_when_ack;
    $rose(m_inf.ack[0]) ||
    $rose(s_inf.ack[0]) ||
    $rose(t_inf.ack[0]) ||
    $rose(e_inf.ack[0]) |-> !r_inf.addr &&
                            !r_inf.be   &&
                            !r_inf.dwr  &&
                            !r_inf.cpu  &&
                            !r_inf.wr   &&
                            !r_inf.rd;
  endproperty
  assert property (zero_when_ack)
  else `uvm_error("assert", "DUT did not it's field to zero when ack")

  // Check that only one host got the ack send from the response slave.
  property ack_mean_one_ack;
    $onehot0({m_inf.ack[0],s_inf.ack[0],t_inf.ack[0],e_inf.ack[0]});
  endproperty
  assert property (ack_mean_one_ack)
  else `uvm_fatal("assert", "AN ACK WAS SENT TO MULTIPLE HOSTS")

  // Check that ack is send properly from the response to the host.
  property respone_ack_before_host_ack;
    $rose(r_inf.ack) |=> $rose(m_inf.ack) ||
                         $rose(s_inf.ack) ||
                         $rose(t_inf.ack) ||
                         $rose(e_inf.ack);
  endproperty
  assert property (respone_ack_before_host_ack)
  else `uvm_fatal("assert", "RESPONSE SEND ACK BUT NO HOST RECEIVED IT")
//******************************************************************************
// End assertions
//******************************************************************************


endmodule : arbiter_top
