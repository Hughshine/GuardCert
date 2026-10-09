(* The leading instruction argument is the observed header parameter, not an
   iterator. Strip it while proposing iterator bounds, then restore it in the
   actual candidate. The unchanged final checker verifies the full argument list. *)
include GuardSelectedDoubleHeaderQuotient

let rec strip_header depth = function
  | L.Instr (instruction,first::coordinates) ->
    let expected = L.Var (nat (depth+1)) in
    (match linear first,linear expected with
     | Some first,Some expected when form_equal first expected -> L.Instr (instruction,coordinates)
     | _ -> invalid_arg "instruction header argument is not the captured parameter")
  | L.Instr (_,[]) -> invalid_arg "missing instruction header argument"
  | L.Loop (lower,upper,body) -> L.Loop (lower,upper,strip_header (depth+1) body)
  | L.Guard (test,body) -> L.Guard (test,strip_header depth body)
  | L.Seq sequence -> L.Seq (strip_header_sequence depth sequence)
and strip_header_sequence depth = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (strip_header depth head,strip_header_sequence depth tail)

let rec restore_header depth = function
  | L.Instr (instruction,coordinates) -> L.Instr (instruction,L.Var (nat (depth+1))::coordinates)
  | L.Loop (lower,upper,body) -> L.Loop (lower,upper,restore_header (depth+1) body)
  | L.Guard (test,body) -> L.Guard (test,restore_header depth body)
  | L.Seq sequence -> L.Seq (restore_header_sequence depth sequence)
and restore_header_sequence depth = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (restore_header depth head,restore_header_sequence depth tail)

let header_adapt limit divisor ((raw,context),variables) =
  try
    let path = match !current_path with Some path -> path | None -> failwith "missing header phase receipt" in
    emit (Filename.concat path "header-actual-raw.loop") (statement "" raw);
    let stripped = strip_header 0 raw in
    emit (Filename.concat path "header-iterator-proposal-input.loop") (statement "" stripped);
    match GuardSelectedDoubleQuotientPartitioned.quotient_adapt limit divisor ((stripped,context),variables) with
    | Result.Err reason -> Result.Err reason
    | Result.Okk ((generated,context),variables) ->
      let actual = restore_header 0 generated in
      emit (Filename.concat path "header-actual-generated.loop") (statement "" actual);
      emit (Filename.concat path "header-coordinate-proposal.txt")
        "leading-argument=captured-original-bound\niterator-proposal=temporary-argument-projection\nactual-candidate=parameter-restored\nfinal-candidate-check=required\n";
      Result.Okk ((actual,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "header-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)
