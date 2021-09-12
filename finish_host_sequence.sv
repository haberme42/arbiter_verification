///////////////////////////////////////////////////////////////////////////
// MODULE               : finish_host_sequence                           //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create a finish sequence with zero at all field.                      //
///////////////////////////////////////////////////////////////////////////
class finish_host_sequence extends uvm_sequence #(arbiter_transaction);
  // Register the sequence with the factory.
  `uvm_object_utils(finish_host_sequence)

  // finish_host_sequence constructor.
  function new(string name = "");
    super.new(name);
  endfunction : new

  // Defines the sequence operation. The sequence send random number of idel 
  //  transaction.
  task body();
    arbiter_transaction arbiter_tran;
    `uvm_do_with(arbiter_tran, { 
                                  wr   == 'b0;
                                  rd   == 'b0;
                                  addr == 'b0;
                                  be   == 'b0;
                                  dwr  == 'b0;
                                })
  endtask : body

endclass : finish_host_sequence
