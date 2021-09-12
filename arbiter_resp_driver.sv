///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_resp_driver                            //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Gets a transaction from the sequencer and send it into the response   //
//  slave side of the DUT using the interface.                           //
///////////////////////////////////////////////////////////////////////////
class arbiter_resp_driver extends uvm_driver#(arbiter_transaction);
  // Register the driver with the factory.
  `uvm_component_utils(arbiter_resp_driver)

  // Virtual interface instance in order to connect the driver to it.
  virtual arb_resp_inf vinf;

  // Variable declarations.
  bit [DW-1:0] drd;
  bit [TW-1:0] rep;

  // arbiter_resp_driver constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get the Interface from the configuration block so that the driver
    //  can use it.
    uvm_config_db#(virtual arb_resp_inf)::get(this, "", "vif", vinf);
  endfunction : build_phase

  // Set the run phase.
  task run_phase(uvm_phase phase);
    drive();
  endtask : run_phase

  // Run the logic of the driver i.e. set how the driver push the signal to the
  //  DUT using the interface.
  virtual task drive();
  // Initialize the response slave ack.
    vinf.ack       = 'b0;
    forever begin
      // The response start to work when there is a write or read signal.
      wait(vinf.wr || vinf.rd)

      // Determine the number of cycles the response will be delayed.
      randcase
        50 : rep     = $urandom_range(1,29);
        40 : rep     = $urandom_range(30,99);
        4  : rep     = $urandom_range(100,999);
        2  : rep     = $urandom_range(1000,TIMEOUT_LIMIT-1);
        4  : rep     = TIMEOUT_LIMIT;
      endcase

      // send the ack if there isn't a timeout.
      repeat(rep) @(negedge vinf.clk);
      if (rep == TIMEOUT_LIMIT)
        @(negedge vinf.clk);

      else begin
        if (vinf.rd)
          vinf.drd   = $random();
        vinf.ack     = 'b1;

        // Set the ack to 0 after one cycle as per the DUT spec.
        @(negedge vinf.clk)
        vinf.ack     = 'b0;
      end
    end
  endtask : drive

endclass : arbiter_resp_driver
