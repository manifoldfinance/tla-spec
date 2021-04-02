------------------- MODULE provisioning_load ---------------------
EXTENDS TLC, Integers, SequencesVMs == {1,2,3}
Incidents(set) == set \X set \X set \X set
Events == [size: 1..4](*--algorithm provisioning
variables
 incident \in Incidents(Events),
 Cluster = [v \in VMs |-> 4],
 curr = "", \* helper: current event
 rrobin = 1;define
 ServersHealthy == \A vm \in VMs: Cluster[vm] <= 9
end define;macro trigger_event(event) begin
 Cluster[rrobin] := Cluster[rrobin] + event.size;
 if rrobin = 3 then
    rrobin := 1
 else
    rrobin := rrobin + 1
 end if;
end macro;begin
 while incident /= <<>> do
  curr := Head(incident);
  incident := Tail(incident);
  trigger_event(curr)
 end while;end algorithm *)==================================================================
