///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_host_monitor                           //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Get the signals from the DUT using the interface and send them as     //
//  transaction to the scoreboard.                                       //
///////////////////////////////////////////////////////////////////////////
class arbiter_host_monitor extends uvm_monitor;
  // Register the agent with the factory.
  `uvm_component_utils(arbiter_host_monitor)

  // Set the handle for the analysis port.
  uvm_analysis_port#(arbiter_transaction) mon_host_ap;

  // Set the handels for the transaction monitoring.
  virtual arb_host_inf vinf;
  arbiter_transaction arbiter_tran;

  covergroup host_coverage();
    option.per_instance = 1;
    option.name = {get_name(),"_coverage"};
    wr_cp   : coverpoint vinf.wr;
    rd_cp   : coverpoint vinf.rd;
    wrXrd   : cross wr_cp, rd_cp
      {
        bins write       = wrXrd with  ({ wr_cp && !rd_cp });
        bins read        = wrXrd with  ({!wr_cp &&  rd_cp });
        bins idel        = wrXrd with  ({!wr_cp && !rd_cp });
        // Since we push them so we know they OK.
        ignore_bins both = wrXrd with  ({ wr_cp &&  rd_cp });
      }

    addr_cp : coverpoint vinf.addr iff (vinf.wr || vinf.rd)
    {bins addr_range [5] = {['b0:$]};}
    be_cp   : coverpoint vinf.be   iff (vinf.wr || vinf.rd)
    {bins be_range   [2] = {['b0:$]};}
    dwr_cp  : coverpoint vinf.dwr  iff (vinf.wr           )
    {bins dwr_range  [5] = {['b0:$]};}
    drd_cp  : coverpoint vinf.drd  iff (           vinf.rd)
    {bins drd_range  [5] = {['b0:$]};}

    ack_cp  : coverpoint vinf.ack
      {
        // When idel no ack will be received.
        bins no_ack      = {'b00};
        bins ack_resp    = {'b01};
        bins ack_timeout = {'b11};
        // Mean nothing in the arbiter hence ignored.
        ignore_bins timeout_without_ack = {'b10};
      }

    cpu_cp  : coverpoint vinf.cpu iff (vinf.wr || vinf.rd);

  endgroup  : host_coverage


  // arbiter_host_monitor constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);

    // Initiate the covergroup.
    host_coverage = new();
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the arbiter interface.
    uvm_config_db#(virtual arb_host_inf)::get(this, "", "vif", vinf);

    // Initiate the analysis port.
    mon_host_ap = new("mon_host_ap" , this);
  endfunction : build_phase

  // Set the run phase.
  task run_phase(uvm_phase phase);
    arbiter_tran = arbiter_transaction::type_id::create("arbiter_tran", this);

    // Catch any signals that are for write or read.
    forever begin
      @(posedge vinf.clk)
      if(vinf.wr || vinf.rd) begin
        arbiter_tran.wr      = vinf.wr;
        arbiter_tran.rd      = vinf.rd;
        arbiter_tran.addr    = vinf.addr;
        arbiter_tran.be      = vinf.be;
        arbiter_tran.dwr     = vinf.dwr;
        arbiter_tran.cpu     = vinf.cpu;
        arbiter_tran.drd     = vinf.drd;
        arbiter_tran.ack     = vinf.ack;

        // Add the description of the transaction to UVM log file.
        `uvm_info(get_name(), arbiter_tran.sprint(), UVM_MEDIUM);

        // Send the transaction to the analysis port.
        mon_host_ap.write(arbiter_tran);

        // Wait for the ack signal which indicates the DUT send signals back
        wait(vinf.ack[0]);
        @(posedge vinf.clk)
        host_coverage.sample();
        arbiter_tran.drd     = vinf.drd;
        arbiter_tran.ack     = vinf.ack;

        // Add the description of the transaction to UVM log file.
        `uvm_info(get_name(), arbiter_tran.sprint(), UVM_MEDIUM);

        // Send the transaction to the analysis port.
        mon_host_ap.write(arbiter_tran);
      end
      else
        host_coverage.sample();
    end
  endtask : run_phase

endclass : arbiter_host_monitor
