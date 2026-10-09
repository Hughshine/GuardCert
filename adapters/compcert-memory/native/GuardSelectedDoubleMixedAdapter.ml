(* Preserve actual affine parameter bounds for zero-link candidates.
   The final Loop checker and machine lowering check this proposal as usual. *)
include GuardSelectedDoubleRectangular

let rec damage_point = function
  | L.Instr (instruction,first::rest) -> L.Instr (instruction,add first one::rest)
  | L.Loop (a,b,body) -> L.Loop (a,b,damage_point body)
  | L.Guard (test,body) -> L.Guard (test,damage_point body)
  | L.Seq sequence -> L.Seq (damage_point_sequence sequence)
  | code -> code
and damage_point_sequence = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (damage_point head,damage_point_sequence tail)

let rec damage_bound = function
  | L.Loop (lower,_,body) -> L.Loop (lower,L.Constant (small 0),body)
  | L.Guard (test,body) -> L.Guard (test,damage_bound body)
  | L.Seq sequence -> L.Seq (damage_bound_sequence sequence)
  | code -> code
and damage_bound_sequence = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (damage_bound head,damage_bound_sequence tail)

let adapt caps (((raw,context),variables) as input) =
  if !current_witnesses=[] || not (List.for_all (fun witness ->
      witness.TilingWitness.stw_links=[]) !current_witnesses) then
    GuardSelectedDoubleRectangular.adapt caps input
  else (
    incr adaptations;
    try
      if List.length context <> List.length caps then
        invalid_arg "untiled parameter layout differs from captures";
      let path = match !current_path with Some path -> path | None -> failwith "missing phase receipt" in
      emit (Filename.concat path "rectangular-raw-generated.loop") (statement "" raw);
      let without_singletons,singletons = singleton_eliminate raw in
      let generated,translations = recover_points without_singletons in
      emit (Filename.concat path "rectangular-point-normalized.loop") (statement "" generated);
      let generated = if Sys.getenv_opt "GUARDCERT_POINT_NORMALIZATION"=Some "wrong-coordinate" then
        damage_point generated else generated in
      let generated = if Sys.getenv_opt "GUARDCERT_BOUND_NORMALIZATION"=Some "wrong-bound" then
        damage_bound generated else generated in
      emit (Filename.concat path "rectangular-caps.txt")
        (String.concat "," (List.map integer_text caps)^"\n");
      emit (Filename.concat path "rectangular-bounded-proposals.txt")
        "zero-link-affine-bounds=retained\nextra-cap-enumeration=false\nfinal-check=pending\n";
      emit (Filename.concat path "rectangular-generated.loop") (statement "" generated);
      emit (Filename.concat path "rectangular-normalization.txt")
        (Printf.sprintf "singleton-loops=%d point-translations=%d zero-links=true\nfinal-check=pending\n"
          singletons translations);
      Result.Okk ((generated,context),variables)
    with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
      (match !current_path with Some path -> emit (Filename.concat path "rectangular-adaptation-refusal.txt")
        (Printexc.to_string error^"\n") | None -> ());
      Result.Err (Printexc.to_string error))
