///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_env                                    //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create and run the agents for the hosts and the response slave        //
///////////////////////////////////////////////////////////////////////////
class arbiter_env extends uvm_env;
  // Register the environment with the factory.
  `uvm_component_utils(arbiter_env)

  // Add the environment components handle to the environment.
  arbiter_host_agent     host_agent [HOSTS];
  arbiter_resp_agent     resp_agent;
  arbiter_scoreboard     arb_scb;

  // arbiter_env constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Initiate the environment components using create.
    foreach (host_agent[i]) begin
      host_agent[i] = arbiter_host_agent::type_id::create($sformatf("host_%0d",i),
                                                          this);
    end

    resp_agent   = arbiter_resp_agent::type_id::create("response_slave", this);
    arb_scb      = arbiter_scoreboard::type_id::create("arb_scb"       , this);
  endfunction : build_phase

  // Set the connect phase.
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // Connect agents analysis ports to the scoreboard.
    foreach (host_agent[i]) begin
      host_agent[i].agent_host_ap.connect(arb_scb.scb_host_export[i]);
    end

    resp_agent.agent_resp_ap.connect(arb_scb.scb_resp_export);
  endfunction : connect_phase

endclass : arbiter_env
