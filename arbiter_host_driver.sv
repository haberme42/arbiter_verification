///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_host_driver                            //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Gets a transaction from the sequencer and send it into a host side of //
//  the DUT using the interface.                                         //
///////////////////////////////////////////////////////////////////////////
class arbiter_host_driver extends uvm_driver#(arbiter_transaction);
  // Register the driver with the factory.
  `uvm_component_utils(arbiter_host_driver)

  // Virtual interface instance in order to connect the driver to it.
  virtual arb_host_inf vinf;

  // arbiter_host_driver constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the Interface from the configuration block so that the driver
    //  can use it.
    uvm_config_db#(virtual arb_host_inf)::get(this, "", "vif", vinf);
  endfunction : build_phase

  // Set the run phase.
  task run_phase(uvm_phase phase);
    drive();
  endtask : run_phase

  // Run the logic of the driver i.e. set how the driver push the signal to the
  //  DUT using the interface.
  virtual task drive();
    arbiter_transaction arbiter_tran;

    forever begin
      // Gets a transaction from the sequencer and stores it in the variable
      //  'arbiter_tran'.
      seq_item_port.get_next_item(arbiter_tran);

      // Add the description of the transaction to UVM log file.
      `uvm_info(get_name(), arbiter_tran.sprint(), UVM_LOW);

      // Push all the signals.
      @(negedge vinf.clk);
      vinf.wr        = arbiter_tran.wr;
      vinf.rd        = arbiter_tran.rd;
      vinf.addr      = arbiter_tran.addr;
      vinf.be        = arbiter_tran.be;
      vinf.dwr       = arbiter_tran.dwr;

      // Wait for ack if the transaction was write or read then push zero as
      //  write and read.
      if (vinf.wr || vinf.rd) begin
        wait(vinf.ack[0]);
        @(negedge vinf.clk);
      end

      // Informs the sequencer that the current operation with the transaction
      //  was finished.
      seq_item_port.item_done();
    end
  endtask : drive

endclass : arbiter_host_driver
