///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_host_sequencer                         //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Send transactions from the sequence to the driver.                    //
///////////////////////////////////////////////////////////////////////////
class arbiter_host_sequencer extends uvm_sequencer #(arbiter_transaction);
  // Register the sequencer with the factory.
  `uvm_component_utils(arbiter_host_sequencer)

  // arbiter_host_sequencer constructor.
  function new(string name, uvm_component parent);
    super.new(name);
  endfunction : new
  
endclass : arbiter_host_sequencer
