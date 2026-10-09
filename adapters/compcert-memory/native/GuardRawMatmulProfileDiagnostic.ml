(* Read-only evidence for profile refusals. This hook does not alter ASTs,
   source profiles, schedules, certificates, or executable conditions. *)
let ident value = Z.to_string (GuardMemoryNumbers.export_positive value)
let trace_clight program =
  let live = ClightTempFootprint.program_temps OriginalMatmul.prog in
  let outside = List.sort_uniq compare (List.filter (fun identifier -> not (List.mem identifier live))
    (ClightTempFootprint.program_temps program)) in
  Printf.eprintf "GUARDCERT_RAW_PROFILE environment=%b scope=%b no_shadow=%b outside_temps=%s\n%!"
    (ClightProgramEnvironment.program_environment_check OriginalMatmul.prog program)
    (ClightProgramEnvironment.program_temp_scope_check live program)
    (ClightGlobalScope.program_avoids_check OriginalMatmulProgramBindings.original_matmul_globals program)
    (String.concat "," (List.map ident outside));
  let rec statement = function
    | Clight.Slabel (label,body) ->
        if List.mem label (GuardScopFrontend.chosen_labels ()) then
          Printf.eprintf "GUARDCERT_RAW_MATCH label=%s exact=%b\n%!" (ident label)
            (body = OriginalMatmulRawSource.raw_original_matmul_region);
        statement body
    | Clight.Ssequence (first,second) | Clight.Sloop (first,second) -> statement first; statement second
    | Clight.Sifthenelse (_,yes,no) -> statement yes; statement no
    | Clight.Sswitch (_,cases) -> statements cases
    | _ -> ()
  and statements = function
    | Clight.LSnil -> () | Clight.LScons (_,body,rest) -> statement body; statements rest in
  List.iter (fun (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> statement fn.Clight.fn_body
    | _ -> ()) program.Ctypes.prog_defs
