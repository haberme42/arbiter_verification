///////////////////////////////////////////////////////////////////////////
// MODULE               : idel_host_sequence                             //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create a random set of idel transaction i.e. the write and read       //
//  signals set to 0.                                                    //
///////////////////////////////////////////////////////////////////////////
class idel_host_sequence extends uvm_sequence #(arbiter_transaction);
  // Register the sequence with the factory.
  `uvm_object_utils(idel_host_sequence)

  // randomly choose the number of transactions.
  rand int num;
  constraint seq_num { num inside {[100:500]}; }

  // idel_host_sequence constructor.
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Defines the sequence operation. The sequence send random number of idel 
  //  transaction.
  task body();
    arbiter_transaction arbiter_tran;

    repeat(num) begin
      `uvm_do_with(arbiter_tran, { wr == 'b0; rd == 'b0; })
    end
  endtask : body

endclass : idel_host_sequence
