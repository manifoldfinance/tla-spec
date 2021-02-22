A model of https://utcc.utoronto.ca/~cks/space/blog/programming/GoConcurrencyStillNotEasy

---- MODULE channels ----
EXTENDS Integers, TLC, Sequences

CONSTANTS NumWorkers, NumTokens

NULL == "NULL" \* Should be a constant, being lazy
Workers == 1..NumWorkers
Processes == Workers \union {0} \* Main

(* --algorithm channels

(**)

variables
  channels = [tokens |-> 0, found |-> 0];
  buffers = [tokens |-> NumTokens, found |-> 0];
  receiving_from = [p \in Processes |-> NULL];
  initialized = [w \in Workers |-> FALSE];

macro write_channel(chan, msg) begin
  \* First version doesn't use msg
  if buffers[chan] = 0 then
    \* unbuffered
    with p \in {p \in Processes: receiving_from[p] = chan} do
      \* Just drop the message in this draft, nobody cares
      receiving_from[p] := NULL;
    end with;
  else
    \* buffered
    await channels[chan] < buffers[chan];
  end if;

  channels[chan] := channels[chan] + 1;
end macro;

macro receive_channel(chan) begin
  await channels[chan] > 0;
  channels[chan] := channels[chan] - 1;
end macro;

\* This one has to be a procedure since the best way to represent
\* Unbuffered channels in pluscal is with state. In TLA+ it'd be easier
procedure receive_unbuffered(chan) begin
  Declare:
    receiving_from[self] := chan;
  Receive:
    await receiving_from[self] = NULL;
    return;
end procedure


process worker \in Workers
begin
  A:
    await initialized[self];
    write_channel("found", "");
  B:
    receive_channel("tokens");
end process;


process main = 0
variables i = 1;
begin
  Main:
    while i <= NumWorkers do
      write_channel("tokens", "");
      initialized[i] := TRUE;
      i := i + 1;
    end while;
  Get:
    while i > 1 do
      i := i - 1;
      call receive_unbuffered("found");
    end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-99569f9b3e19a6587d773dffae23a91c
CONSTANT defaultInitValue
VARIABLES channels, buffers, receiving_from, initialized, pc, stack, chan, i

vars == << channels, buffers, receiving_from, initialized, pc, stack, chan, i
        >>

ProcSet == (Workers) \cup {0}

Init == (* Global variables *)
        /\ channels = [tokens |-> 0, found |-> 0]
        /\ buffers = [tokens |-> NumTokens, found |-> 0]
        /\ receiving_from = [p \in Processes |-> NULL]
        /\ initialized = [w \in Workers |-> FALSE]
        (* Procedure receive_unbuffered *)
        /\ chan = [ self \in ProcSet |-> defaultInitValue]
        (* Process main *)
        /\ i = 1
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Workers -> "A"
                                        [] self = 0 -> "Main"]

Declare(self) == /\ pc[self] = "Declare"
                 /\ receiving_from' = [receiving_from EXCEPT ![self] = chan[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Receive"]
                 /\ UNCHANGED << channels, buffers, initialized, stack, chan, 
                                 i >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ receiving_from[self] = NULL
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ chan' = [chan EXCEPT ![self] = Head(stack[self]).chan]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << channels, buffers, receiving_from, 
                                 initialized, i >>

receive_unbuffered(self) == Declare(self) \/ Receive(self)

A(self) == /\ pc[self] = "A"
           /\ initialized[self]
           /\ IF buffers["found"] = 0
                 THEN /\ \E p \in {p \in Processes: receiving_from[p] = "found"}:
                           receiving_from' = [receiving_from EXCEPT ![p] = NULL]
                 ELSE /\ channels["found"] < buffers["found"]
                      /\ UNCHANGED receiving_from
           /\ channels' = [channels EXCEPT !["found"] = channels["found"] + 1]
           /\ pc' = [pc EXCEPT ![self] = "B"]
           /\ UNCHANGED << buffers, initialized, stack, chan, i >>

B(self) == /\ pc[self] = "B"
           /\ channels["tokens"] > 0
           /\ channels' = [channels EXCEPT !["tokens"] = channels["tokens"] - 1]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << buffers, receiving_from, initialized, stack, chan, 
                           i >>

worker(self) == A(self) \/ B(self)

Main == /\ pc[0] = "Main"
        /\ IF i <= NumWorkers
              THEN /\ IF buffers["tokens"] = 0
                         THEN /\ \E p \in {p \in Processes: receiving_from[p] = "tokens"}:
                                   receiving_from' = [receiving_from EXCEPT ![p] = NULL]
                         ELSE /\ channels["tokens"] < buffers["tokens"]
                              /\ UNCHANGED receiving_from
                   /\ channels' = [channels EXCEPT !["tokens"] = channels["tokens"] + 1]
                   /\ initialized' = [initialized EXCEPT ![i] = TRUE]
                   /\ i' = i + 1
                   /\ pc' = [pc EXCEPT ![0] = "Main"]
              ELSE /\ pc' = [pc EXCEPT ![0] = "Get"]
                   /\ UNCHANGED << channels, receiving_from, initialized, i >>
        /\ UNCHANGED << buffers, stack, chan >>

Get == /\ pc[0] = "Get"
       /\ IF i > 1
             THEN /\ i' = i - 1
                  /\ /\ chan' = [chan EXCEPT ![0] = "found"]
                     /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "receive_unbuffered",
                                                           pc        |->  "Get",
                                                           chan      |->  chan[0] ] >>
                                                       \o stack[0]]
                  /\ pc' = [pc EXCEPT ![0] = "Declare"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED << stack, chan, i >>
       /\ UNCHANGED << channels, buffers, receiving_from, initialized >>

main == Main \/ Get

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == main
           \/ (\E self \in ProcSet: receive_unbuffered(self))
           \/ (\E self \in Workers: worker(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-0eb3139158eb458ef4d648073ac8329b








====
