///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_test                                   //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Create the environment for the test and run the test. The test set    //
//  two kind of hosts active which have a sequence and non active which  //
//  send zero transaction. The default test class have all hosts active. //
///////////////////////////////////////////////////////////////////////////
class arbiter_test #(bit [2:0] ACTIVE = HOSTS) extends uvm_test;
  // Register the test with the factory.
  `uvm_component_utils(arbiter_test)

  bit [2:0] non_active;

  // Add the environment handle to the test.
  arbiter_env arb_env;

  // arbiter_test constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Initiate the environment component using create.
    arb_env = arbiter_env::type_id::create("arb_env" , this);
  endfunction : build_phase

  // Set the run phase.
  task run_phase(uvm_phase phase);
    arbiter_host_sequence active_seq[];
    finish_host_sequence  non_active_seq[];
    active_seq     = new [ACTIVE];
    if (HOSTS - ACTIVE)
      non_active_seq = new [HOSTS - ACTIVE];


    // Raise the objection, let the simulator know the test is running.
    phase.raise_objection(.obj(this));

    // Start the test by initiate and start the sequences.
    #50
    for (int i = 0; i < ACTIVE; i++) begin
      automatic int j = i;
      fork
        begin
          active_seq[j] = arbiter_host_sequence::type_id::create(
                                                        $sformatf("seq_%0d",j));
          assert(active_seq[j].randomize());
          active_seq[j].start(arb_env.host_agent[j].arb_seqer);
        end
      join_none
    end

    // Set the non active hosts sequences.
    for (int i = 0; i < HOSTS - ACTIVE; i++) begin
      automatic int j = i;
      fork
        begin
          non_active_seq[j] = finish_host_sequence::type_id::create(
                                                        $sformatf("seq_%0d",j));
          assert(non_active_seq[j].randomize());
          non_active_seq[j].start(arb_env.host_agent[ACTIVE + j].arb_seqer);
        end
      join_none
    end
    wait fork;

    // Drop the objection, let the simulator know the test is done.
    phase.drop_objection(.obj(this));
  endtask : run_phase

endclass : arbiter_test
