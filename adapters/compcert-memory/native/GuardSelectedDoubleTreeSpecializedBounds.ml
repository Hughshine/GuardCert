(* The extracted service specializes singleton parameter intervals and keeps
   all newly bound iterators unknown. The source-aware producer and the final
   actual candidate/dependence checker still decide installation. *)
include GuardSelectedDoubleTreeResidualBounds
module Specialization = GuardMemoryDoubleParameterSpecialization.DoubleParameterSpecialization

let adapt intervals source (((raw,context),variables) as request) =
  let facts = Specialization.singleton_facts intervals in
  let specialized = if Sys.getenv_opt "GUARDCERT_PARAMETER_SPECIALIZATION" = Some "disabled"
    then raw else Specialization.statement facts raw in
  (match !current_path with
   | None -> ()
   | Some path ->
       emit (Filename.concat path "tree-original-codegen.loop") (statement "" raw);
       emit (Filename.concat path "tree-specialized-codegen.loop") (statement "" specialized);
       emit (Filename.concat path "tree-parameter-specialization.txt")
         (Printf.sprintf "changed=%b\nproducer=extracted-verified-function\nknown-parameters=%s\nfinal-check=pending\n"
           (raw<>specialized)
           (String.concat "," (List.map (function None->"unknown" | Some value->integer_text value) facts))));
  let proposed = if specialized=raw then request else ((specialized,context),variables) in
  GuardSelectedDoubleTreeResidualBounds.adapt intervals source proposed
