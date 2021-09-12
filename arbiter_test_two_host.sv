///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_test_two_host                          //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create a test with two active host.                                   //
///////////////////////////////////////////////////////////////////////////
class arbiter_test_two_host extends arbiter_test #(2);
  `uvm_component_utils(arbiter_test_two_host)

  // arbiter_test_one_host constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new
endclass