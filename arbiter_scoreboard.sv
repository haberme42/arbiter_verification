///////////////////////////////////////////////////////////////////////////
// MODULE               : arbiter_scoreboard                             //
//                                                                       //
// DESIGNER             : Haberme42                                      //
//                                                                       //
// Get the transactions from the monitors and compare them using round   //
//  robin as a reference model.                                          //
//                                                                       //
//  NOTE: the scoreboard assume that the DUT send data when it should    //
//  and check that the signals passed correctly through the DUT and      //
//  that the round robin order was maintained. (the correctness of the   //
//  sending process will be check via assertions.                        //
///////////////////////////////////////////////////////////////////////////
class arbiter_scoreboard extends uvm_scoreboard;
  // Register the agent with the factory.
  `uvm_component_utils(arbiter_scoreboard)

  // Set the handle for the analysis port.
  uvm_analysis_export #(arbiter_transaction) scb_host_export [HOSTS];
  uvm_analysis_export #(arbiter_transaction) scb_resp_export;

  // Set the fifo.
  uvm_tlm_analysis_fifo #(arbiter_transaction) scb_host_fifo [HOSTS];
  uvm_tlm_analysis_fifo #(arbiter_transaction) scb_resp_fifo;
  
  arbiter_transaction host_tran;
  arbiter_transaction resp_tran;

  // Variable declarations.
  bit [2   :0]  rr_index;

  // Cover the request status of the hosts. check that some status will occur
  //  such as idel status.
  covergroup request_coverage();
    request_cp : coverpoint $countones(
                                    {
                                      !scb_host_fifo[0].is_empty(),
                                      !scb_host_fifo[1].is_empty(),
                                      !scb_host_fifo[2].is_empty(),
                                      !scb_host_fifo[3].is_empty()
                                    })
                                    {
                                      bins hosts_with_request[HOSTS+1]={[0:HOSTS]};
                                    }
  endgroup : request_coverage

  // arbiter_scoreboard constructor.
  function new(string name, uvm_component parent);
    super.new(name, parent);

    // Initiate the covergroup.
    request_coverage = new();
  endfunction : new

  // Set the build phase.
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Initiate the scoreboard component using create.
    foreach (scb_host_export[i]) begin
      scb_host_export[i] = new($sformatf("scb_export[%d]", i), this);
      scb_host_fifo[i]   = new($sformatf("scb_fifo[%d]", i), this);
    end

    scb_resp_export      = new("scb_resp_export", this);
    scb_resp_fifo        = new("scb_resp_fifo", this);
  endfunction : build_phase

  // Set the connect phase.
  function void connect_phase(uvm_phase phase);
    foreach (scb_host_export[i]) begin
      scb_host_export[i].connect(scb_host_fifo[i].analysis_export);
    end

      scb_resp_export.connect(scb_resp_fifo.analysis_export);
  endfunction : connect_phase

  // The function get two transaction from the host and the response slave
  //  compere their signals (except the ack and drd signals) and print the
  //  result using UVM_info.
  virtual function void compare_signals(arbiter_transaction host_tran,resp_tran);
    if
    (
      host_tran.wr        == resp_tran.wr   &&
      host_tran.rd        == resp_tran.rd   &&
      host_tran.addr      == resp_tran.addr &&
      host_tran.be        == resp_tran.be   &&
      host_tran.dwr       == resp_tran.dwr  &&
      host_tran.cpu       == resp_tran.cpu
    )
      `uvm_info("compare equal OK", {"Test Equal Signals: OK!"}, UVM_LOW)
    else
      `uvm_info("compare equal fail",{"Test Equal Signals: Fail!"}, UVM_LOW)
  endfunction : compare_signals

  // The function get two transactions from the host and the response slave and
  //  check the ack that the response slave send.
  virtual function void compare_ack(arbiter_transaction host_tran,resp_tran);
    // Check for timeout i.e. transaction from the response without ack.
    if (!resp_tran.ack[0]) begin
      if (host_tran.ack == 'b11)
        `uvm_info("compare timeout OK", {"Test Timeout: OK!"}, UVM_LOW)
      else
        `uvm_info("compare timeout fail", {"Test Timeout: Fail!"}, UVM_LOW)
    end

    else if (host_tran.wr) begin
      if (host_tran.ack == 'b01)
        `uvm_info("compare write OK", {"Test Write: OK!"}, UVM_LOW)
      else
        `uvm_info("compare write fail", {"Test Write: Fail!"}, UVM_LOW)
    end

    else begin
      if (host_tran.ack == 'b01 && host_tran.drd == resp_tran.drd)
        `uvm_info("compare read OK", {"Test Read: OK!"}, UVM_LOW)
      else
        `uvm_info("compare read fail", {"Test Read: Fail!"}, UVM_LOW)
    end
  endfunction : compare_ack

  // The function serach for the next host from idel position i.e. all the
  //  hosts will be check until the first one that have a request is found.
  function bit [2:0] idel_to_host();
    for (bit [2:0] j = 0; j < HOSTS; j++) begin
      if (!scb_host_fifo[j].is_empty())
        return j;
    end
  endfunction : idel_to_host

  // The function serach for the next host from a host position i.e. all the
  //  hosts except the one that just got ack will be check until the first one
  //  that have a request is found if there is no host with request the idel
  //  mode will be set.
  function bit [2:0] host_to_host(bit [2:0] host);
    for (bit [2:0] j = 1; j < HOSTS; j++) begin
      host = (host + 1) % HOSTS;
      if (!scb_host_fifo[host].is_empty())
        return host;
    end

    return HOSTS;
  endfunction : host_to_host

  // Set the run phase.
  task run();
    // Deal with the problem where the DUT skip the master in first run.
    scb_resp_fifo.peek(resp_tran);
    request_coverage.sample();
    rr_index = host_to_host(0);

    forever begin
      // Start the comparison only when there is transaction from the response.
      scb_resp_fifo.get(resp_tran);

      // Deal with idel state.
      if (rr_index == HOSTS) begin
        request_coverage.sample();
        rr_index = idel_to_host();
      end

      // Compare the signals between the host and the response.
      scb_host_fifo[rr_index].get(host_tran);
      compare_signals(host_tran,resp_tran);

      // Compare the ack received from the response.
      scb_resp_fifo.get(resp_tran);
      scb_host_fifo[rr_index].get(host_tran);
      compare_ack(host_tran, resp_tran);

      // Serach the next host.
      rr_index = host_to_host(rr_index);
      request_coverage.sample();
    end
  endtask : run

endclass : arbiter_scoreboard
