///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_host_sequence                          //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create a series of test for the arbiter using other sequences.        //
///////////////////////////////////////////////////////////////////////////
class arbiter_host_sequence extends uvm_sequence #(arbiter_transaction);
  // Register the sequence with the factory.
  `uvm_object_utils(arbiter_host_sequence)

  // The sequences that this sequence will use.
  random_host_sequence     rnd_seq;
  idel_host_sequence       idl_seq;
  finish_host_sequence     fin_seq;

  // Randomly choose the number of transaction.
  rand int num;
  constraint seq_num { num inside {[200:300]}; }

  // arbiter_host_sequence constructor.
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Defines the sequence operation. The sequence run other sequences to create
  //  series of tests for the DUT.
  task body();
    repeat(num) begin
      randcase
        7   : `uvm_do(rnd_seq)
        3   : `uvm_do(idl_seq)
      endcase
    end

    // End the sequence with idel state.
    `uvm_do(fin_seq)
  endtask : body

endclass : arbiter_host_sequence
