///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_host_agent                             //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Set the agent for the arbiter host with its components.               //
///////////////////////////////////////////////////////////////////////////
class arbiter_host_agent extends uvm_agent;
  // Register the agent with the factory.
  `uvm_component_utils(arbiter_host_agent)

  // Set the handle for the analysis port.
  uvm_analysis_port#(arbiter_transaction) agent_host_ap;

  // Add the components handles to the agent.
  arbiter_host_sequencer     arb_seqer;
  arbiter_host_driver        arb_drv;
  arbiter_host_monitor       arb_mon;

  // arbiter_host_agent constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Initiate the analysis port.
    agent_host_ap = new("agent_host_ap", this);

    // Initiate the components using create.
    arb_seqer=arbiter_host_sequencer::type_id::create({get_name(),"_seq"},this);
    arb_drv = arbiter_host_driver::type_id::create({get_name(),"_driver"},this);
    arb_mon=arbiter_host_monitor::type_id::create({get_name(),"_monitor"},this);
  endfunction : build_phase

  // Set the connect phase. connct the port and the analysis port.
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    arb_drv.seq_item_port.connect(arb_seqer.seq_item_export);
    arb_mon.mon_host_ap.connect(agent_host_ap);
  endfunction : connect_phase

endclass : arbiter_host_agent
