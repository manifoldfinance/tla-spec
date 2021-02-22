EXTENDS Integers, TLC, Sequences
CONSTANTS Devices

(* --algorithm BatchInstall
variables
  AppScope \in [Devices -> {0, 1}];
  Installs \in [Devices -> BOOLEAN];
  batch_pool = {};
  
define
  PoolNotEmpty == batch_pool # {}
end define

procedure ChangeAppScope()
begin
  Add:  
    AppScope := [d \in Devices |->
        IF d \in batch_pool THEN AppScope[d] + 1
        ELSE AppScope[d] 
     ]; 
  Clean:
    batch_pool := {};
  return;
end procedure

fair process SyncDevice \in Devices
begin 
  Sync:
    if Installs[self] then
        batch_pool := batch_pool \union {self};
    end if;
end process;

fair process TimeLoop = 0
begin 
  Start:
    while TRUE do
      await PoolNotEmpty;
      call ChangeAppScope();
    end while;
end process
end algorithm; *)