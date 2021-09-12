///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_transaction                            //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Contain The packet information on the arbiter signals.                //
///////////////////////////////////////////////////////////////////////////
class arbiter_transaction extends uvm_sequence_item;
  // Declare the transaction fields.
  rand bit          wr;
  rand bit          rd;
  rand bit [AW-1:0] addr;
  rand bit [BW-1:0] be;
  rand bit [DW-1:0] dwr;
       bit [DW-1:0] drd;
       bit [1   :0] ack;
       bit          cpu;

  // arbiter_transaction constructor.
  function new(string name = "");
    super.new(name);
  endfunction: new

  // Register the transaction and its fields with the factory.
  `uvm_object_utils_begin(arbiter_transaction)
  `uvm_field_int(wr,   UVM_ALL_ON)
  `uvm_field_int(rd,   UVM_ALL_ON)
  `uvm_field_int(addr, UVM_ALL_ON)
  `uvm_field_int(be,   UVM_ALL_ON)
  `uvm_field_int(cpu,  UVM_ALL_ON)
  `uvm_field_int(dwr,  UVM_ALL_ON)
  `uvm_field_int(drd,  UVM_ALL_ON)
  `uvm_field_int(ack,  UVM_ALL_ON)
  `uvm_object_utils_end

endclass : arbiter_transaction
