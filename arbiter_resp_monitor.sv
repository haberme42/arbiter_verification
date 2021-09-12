///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_resp_monitor                           //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Get the signals from the DUT using the interface and send them as     //
//  transaction to the scoreboard.                                       //
///////////////////////////////////////////////////////////////////////////
class arbiter_resp_monitor extends uvm_monitor;
  // Register the agent with the factory.
  `uvm_component_utils(arbiter_resp_monitor)

  // Set the handle for the analysis port.
  uvm_analysis_port#(arbiter_transaction) mon_resp_ap;

  // Set the handels for the transaction monitoring.
  virtual arb_resp_inf vinf;
  arbiter_transaction arbiter_tran;

  // Variable declarations.
  bit [TW-1:0]  timeout_cnt;

  // arbiter_resp_monitor constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the arbiter interface.
    uvm_config_db#(virtual arb_resp_inf)::get(this, "", "vif", vinf);

    // Initiate the analysis port.
    mon_resp_ap = new("mon_resp_ap" , this);
  endfunction : build_phase

  // Set the run phase.
  task run_phase(uvm_phase phase);
    arbiter_tran = arbiter_transaction::type_id::create("arbiter_tran", this);

    // Catch any signals that are for write, read or ack.
    forever begin
      @(posedge vinf.clk)
      #1
      if (vinf.wr || vinf.rd) begin
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
        mon_resp_ap.write(arbiter_tran);

        // Wait for the ack signal which indicates the DUT send signals back or
        //  a timeout
        timeout_cnt = 'b0;
        while (timeout_cnt < TIMEOUT_LIMIT && !vinf.ack) begin
          @(posedge vinf.clk)
          timeout_cnt++;
        end

        arbiter_tran.drd     = vinf.drd;
        arbiter_tran.ack     = vinf.ack;

        // Add the description of the transaction to UVM log file.
        `uvm_info(get_name(), arbiter_tran.sprint(), UVM_MEDIUM);

        // Send the transaction to the analysis port.
        mon_resp_ap.write(arbiter_tran);
      end
    end
  endtask : run_phase

endclass : arbiter_resp_monitor
