///////////////////////////////////////////////////////////////////////////
// MODULE               : random_host_sequence                           //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create a randomize transaction.                                      //
///////////////////////////////////////////////////////////////////////////
class random_host_sequence extends uvm_sequence #(arbiter_transaction);
  // Register the sequence with the factory.
  `uvm_object_utils(random_host_sequence)

  // random_host_sequence constructor.
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Defines the sequence operation. The sequence create a random transaction.
  task body();
    arbiter_transaction arbiter_tran;
    `uvm_do_with(arbiter_tran, { wr + rd == 'b1; })
  endtask : body

endclass : random_host_sequence
