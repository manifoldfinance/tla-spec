------------------ MODULE trigger_event --------------------
macro trigger_event(event) begin
 Cluster[event.target] := Cluster[event.target] + event.size
end macro;begin
 while incident /= <<>> do
  curr := Head(incident);
  incident := Tail(incident);
  trigger_event(curr)
 end while;end algorithm *)
