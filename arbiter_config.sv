///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_configuration                          //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Set the configuration file.                                           //
///////////////////////////////////////////////////////////////////////////
class arbiter_configuration extends uvm_object;
  // Register the configuration with the factory.
  `uvm_object_utils(arbiter_configuration)

  // arbiter_configuration constructor.
  function new(string name = "");
    super.new(name);
  endfunction : new

endclass : arbiter_configuration
