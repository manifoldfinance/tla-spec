---- MODULE logger ----
EXTENDS Integers, TLC, Sequences

Files == { "a" }
FileStruct == [ requested : BOOLEAN, uploaded : {FALSE}, logged : {FALSE}, downloaded : {FALSE}]
Range(F) == { F[x]: x \in DOMAIN F }
(* --algorithm logger
variables files \in [Files -> FileStruct];
define
  FileProc(proc) == [ f : Files, p : {proc} ]
end define;

process upload \in FileProc("upload")
begin
  Upload:
    if files[self.f].requested then
      files[self.f].uploaded := TRUE
    end if
end process;

process log \in FileProc("log")
begin
  Log:
    await files[self.f].uploaded;
    files[self.f].logged := TRUE
end process;

process download \in FileProc("download")
begin
  Download:
    await files[self.f].uploaded;
    files[self.f].downloaded := TRUE ||
    files[self.f].uploaded := FALSE
end process;

end algorithm; *)
\* BEGIN TRANSLATION
\* END TRANSLATION

DownloadInvariant == 
\A f \in Files:
  /\ files[f].downloaded => files[f].requested
  /\ files[f].downloaded => ~files[f].uploaded
  
LoggingInvariant ==
\A f \in Files:
  /\ files[f].downloaded => files[f].logged