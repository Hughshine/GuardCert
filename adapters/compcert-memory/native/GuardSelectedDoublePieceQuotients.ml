(* Untrusted quotient coordinates for modulo-zero boundary pieces.
   The actual source/candidate piece checker remains the installation authority. *)
include GuardSelectedDoubleTreeSpecializedCoordinates

let rec insert_expression cutoff = function
  | L.Constant _ as value -> value
  | L.Var index ->
      let index=GuardOpenScopDoubleIO.nat_to_int index in
      L.Var (nat (if index>=cutoff then index+1 else index))
  | L.Sum (a,b) -> add (insert_expression cutoff a) (insert_expression cutoff b)
  | L.Mult (factor,value) -> normalize (L.Mult (factor,insert_expression cutoff value))
  | L.Div (value,divisor) -> L.Div (insert_expression cutoff value,divisor)
  | L.Mod (value,divisor) -> L.Mod (insert_expression cutoff value,divisor)
  | L.Max (a,b) -> L.Max (insert_expression cutoff a,insert_expression cutoff b)
  | L.Min (a,b) -> L.Min (insert_expression cutoff a,insert_expression cutoff b)
let rec insert_test cutoff = function
  | L.LE (a,b) -> L.LE (insert_expression cutoff a,insert_expression cutoff b)
  | L.EQ (a,b) -> L.EQ (insert_expression cutoff a,insert_expression cutoff b)
  | L.And (a,b) -> L.And (insert_test cutoff a,insert_test cutoff b)
  | L.Or (a,b) -> L.Or (insert_test cutoff a,insert_test cutoff b)
  | L.Not test -> L.Not (insert_test cutoff test)
  | L.TConstantTest _ as test -> test
let rec insert_statement cutoff = function
  | L.Loop (lo,hi,body) -> L.Loop (insert_expression cutoff lo,
      insert_expression cutoff hi,insert_statement (cutoff+1) body)
  | L.Guard (test,body) -> L.Guard (insert_test cutoff test,insert_statement cutoff body)
  | L.Instr (instruction,args) -> L.Instr (instruction,List.map (insert_expression cutoff) args)
  | L.Seq sequence -> L.Seq (insert_sequence cutoff sequence)
and insert_sequence cutoff = function
  | L.SNil -> L.SNil
  | L.SCons (head,tail) -> L.SCons (insert_statement cutoff head,insert_sequence cutoff tail)

let zero = function
  | L.Constant value -> Z.equal (GuardMemoryNumbers.export_integer value) Z.zero
  | _ -> false
let rec modulo_zero = function
  | L.EQ (L.Mod (numerator,divisor),value)
  | L.EQ (value,L.Mod (numerator,divisor)) when zero value ->
      if Z.sign (GuardMemoryNumbers.export_integer divisor)>0 && Option.is_some (linear numerator)
      then Some (numerator,divisor) else None
  | L.And (a,b) -> (match modulo_zero a with Some _ as found->found | None->modulo_zero b)
  | _ -> None

let replace_quotient numerator divisor code =
  let same depth candidate factor =
    factor=divisor && match linear candidate,linear (lift_by depth numerator) with
    | Some a,Some b -> form_equal a b | _ -> false in
  let rec value depth = function
    | L.Div (candidate,factor) when same depth candidate factor -> L.Var (nat depth)
    | L.Mod (candidate,factor) when same depth candidate factor -> L.Constant (small 0)
    | L.Sum (a,b) -> add (value depth a) (value depth b)
    | L.Mult (factor,a) -> normalize (L.Mult (factor,value depth a))
    | L.Div (a,factor) -> L.Div (value depth a,factor)
    | L.Mod (a,factor) -> L.Mod (value depth a,factor)
    | L.Max (a,b) -> L.Max (value depth a,value depth b)
    | L.Min (a,b) -> L.Min (value depth a,value depth b)
    | a -> a in
  let rec test depth = function
    | L.EQ (L.Mod (candidate,factor),a)
    | L.EQ (a,L.Mod (candidate,factor)) when zero a && same depth candidate factor ->
        L.EQ (candidate,L.Mult (divisor,L.Var (nat depth)))
    | L.LE (a,b) -> L.LE (value depth a,value depth b)
    | L.EQ (a,b) -> L.EQ (value depth a,value depth b)
    | L.And (a,b) -> L.And (test depth a,test depth b)
    | L.Or (a,b) -> L.Or (test depth a,test depth b)
    | L.Not a -> L.Not (test depth a)
    | L.TConstantTest _ as a -> a in
  let rec body depth = function
    | L.Loop (lo,hi,child) -> L.Loop (value depth lo,value depth hi,body (depth+1) child)
    | L.Guard (condition,child) -> L.Guard (test depth condition,body depth child)
    | L.Instr (instruction,args) -> L.Instr (instruction,List.map (value depth) args)
    | L.Seq children -> L.Seq (sequence depth children)
  and sequence depth = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (body depth head,sequence depth tail) in
  body 0 code

let materialize_quotients intervals code =
  let proposals=ref [] in
  let rec visit depth bounds = function
    | L.Guard (test,body) as code -> (match modulo_zero test with
        | None -> L.Guard (test,visit depth bounds body)
        | Some (numerator,divisor) ->
            let lo,hi=match interval bounds numerator with
              | Some (lo,hi) ->
                  let divisor=GuardMemoryNumbers.export_integer divisor in
                  Z.ediv lo divisor,Z.ediv hi divisor
              | None -> invalid_arg "quotient numerator has no finite captured enclosure" in
            proposals:=(Printf.sprintf "depth=%d numerator=%s divisor=%s lower=%s upper-inclusive=%s"
              depth (loop_expression numerator) (integer_text divisor) (Z.to_string lo) (Z.to_string hi))::!proposals;
            let inserted=insert_statement 0 code in
            let replaced=replace_quotient (lift_by 1 numerator) divisor inserted in
            L.Loop (L.Constant (integer lo),L.Constant (integer (Z.succ hi)),
              visit (depth+1) (Some (lo,hi)::bounds) replaced))
    | L.Loop (lo,hi,body) ->
        let range=match interval bounds lo,interval bounds hi with
          | Some (lo,_),Some (_,hi) -> Some (lo,Z.max lo (Z.pred hi))
          | _ -> None in
        L.Loop (lo,hi,visit (depth+1) (range::bounds) body)
    | L.Seq children -> L.Seq (sequence depth bounds children)
    | code -> code
  and sequence depth bounds = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (visit depth bounds head,sequence depth bounds tail) in
  let bounds=List.map (fun (lo,hi)->Some
    (GuardMemoryNumbers.export_integer lo,GuardMemoryNumbers.export_integer hi)) intervals in
  let result=visit 0 bounds code in
  result,String.concat "\n" (List.rev !proposals) ^ "\n"

let adapt intervals source ((raw,context),variables) =
  incr adaptations;
  verified_predicates:=0;cleared_floor_nodes:=0;
  try
    if List.length context<>List.length intervals then invalid_arg "source interval layout";
    let path=match !current_path with Some path->path | None->failwith "missing phase receipt" in
    emit (Filename.concat path "tree-source.loop") (statement "" (fst (fst source)));
    emit (Filename.concat path "tree-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons=singleton_eliminate raw in
    let facts=Specialization.singleton_facts intervals in
    let specialized=if Sys.getenv_opt "GUARDCERT_PARAMETER_SPECIALIZATION"=Some "disabled"
      then without_singletons else Specialization.statement facts without_singletons in
    emit (Filename.concat path "tree-original-codegen.loop") (statement "" raw);
    emit (Filename.concat path "tree-specialized-codegen.loop") (statement "" specialized);
    emit (Filename.concat path "tree-parameter-specialization.txt")
      (Printf.sprintf "changed=%b\nproducer=extracted-verified-function\nknown-parameters=%s\norder=original-singleton-cleanup-before-specialization\nfinal-check=pending\n"
        (without_singletons<>specialized)
        (String.concat "," (List.map (function None->"unknown" | Some value->integer_text value) facts)));
    let recovered,translations=recover_points specialized in
    emit (Filename.concat path "tree-point-normalized.loop") (statement "" recovered);
    let proposed,reason=try
      let body,count=source_mixed_candidate intervals source in
      body,"source-mixed-box-points=" ^ string_of_int count
    with Invalid_argument _ | Not_found ->
      let body,count=coalesce_prefix recovered in
      body,"coalesced-prefixes=" ^ string_of_int count in
    emit (Filename.concat path "tree-coalesced.loop") (statement "" proposed);
    let proposed,quotients=materialize_quotients intervals proposed in
    emit (Filename.concat path "tree-quotient-coordinates.loop") (statement "" proposed);
    emit (Filename.concat path "tree-quotient-proposals.txt")
      ("scope=untrusted-data-proposal\nfinal-check=pending\n" ^ quotients);
    let generated,proposals=enclosing_bounds intervals proposed in
    let generated,moved=hoist_independent generated in
    let extraction=match E.extractor ((generated,context),variables) with
      | Result.Okk ((instructions,_),_)->"accepted points=" ^ string_of_int (List.length instructions)
      | Result.Err reason->"refused reason=" ^ reason in
    emit (Filename.concat path "tree-candidate-extraction.txt") (extraction ^ "\n");
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d %s hoisted=%d\nfinal-check=pending\n"
        singletons translations reason moved);
    let bounds=List.map (fun (lower,upper)->{B.A.lower=lower;B.A.upper=upper}) intervals in
    let residual_bounds=List.map (fun (lower,upper)->{R.A.lower=lower;R.A.upper=upper}) intervals in
    let pruned=B.prune bounds generated in
    let actual=F.factor_statement (R.residual_statement residual_bounds [] pruned) in
    emit (Filename.concat path "tree-runtime-pruned.loop") (statement "" pruned);
    emit (Filename.concat path "tree-runtime-residual.loop") (statement "" actual);
    emit (Filename.concat path "tree-runtime-residual.txt")
      (Printf.sprintf "changed=%b\nreference-check=pending\nactual-postpass=extracted-verified-function\n" (pruned<>actual));
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error->
    (match !current_path with Some path->emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None->());
    Result.Err (Printexc.to_string error)

let propose = GuardSelectedDoublePieceProducer.propose
