///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_resp_agent                             //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Set the agent for the arbiter response slave with its components.     //
///////////////////////////////////////////////////////////////////////////
class arbiter_resp_agent extends uvm_agent;
  // Register the agent with the factory.
  `uvm_component_utils(arbiter_resp_agent)

  // Set the handle for the analysis port.
  uvm_analysis_port#(arbiter_transaction) agent_resp_ap;

  // Add the components handles to the agent.
  arbiter_resp_driver         arb_drv;
  arbiter_resp_monitor        arb_mon;

  // arbiter_resp_agent constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Initiate the analysis port.
    agent_resp_ap = new("agent_resp_ap", this);

    // Initiate the components using create.
    arb_drv = arbiter_resp_driver::type_id::create({get_name(),"_driver"},this);
    arb_mon=arbiter_resp_monitor::type_id::create({get_name(),"_monitor"},this);
  endfunction : build_phase

  // Set the connect phase. connct the analysis port.
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    arb_mon.mon_resp_ap.connect(agent_resp_ap);
  endfunction : connect_phase

endclass : arbiter_resp_agent
