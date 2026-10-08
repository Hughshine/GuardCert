(* Untrusted bound and guard proposals. Raw prepared codegen, tiling witnesses,
   and the final verified source/candidate checker remain the authority. *)
include GuardTiledPreparedTensorCandidate
module Coefficients = Map.Make(Int)
let zero = L.Constant(small 0)
let rec max_leaves = function L.Max(a,b)->max_leaves a @ max_leaves b | e->[e]
let rec min_leaves = function L.Min(a,b)->min_leaves a @ min_leaves b | e->[e]
let rec loop_score depth = function
  | L.Var n -> if GuardOpenScopIO.nat_to_int n < depth then 1 else 0
  | L.Sum(a,b) -> loop_score depth a + loop_score depth b
  | L.Mult(_,e) -> loop_score depth e
  | _ -> 0
let choose depth fallback leaves =
  fst(List.fold_left(fun (best,score) e ->
    let current = if affine e then loop_score depth e else 0 in
    if current > score then e,current else best,score)(fallback,0)leaves)
let merge a b = Coefficients.merge(fun _ x y->
  let z=Z.add(Option.value x ~default:Z.zero)(Option.value y ~default:Z.zero)in
  if Z.equal z Z.zero then None else Some z)a b
let scale k values = Coefficients.filter(fun _ c->not(Z.equal c Z.zero))
  (Coefficients.map(Z.mul k)values)
let rec linear = function
  | L.Constant c -> GuardMemoryNumbers.export_integer c,Coefficients.empty
  | L.Var n -> Z.zero,Coefficients.singleton(GuardOpenScopIO.nat_to_int n)Z.one
  | L.Sum(a,b) -> let ac,av=linear a in let bc,bv=linear b in Z.add ac bc,merge av bv
  | L.Mult(k,e) -> let c,v=linear e in let k=GuardMemoryNumbers.export_integer k in Z.mul k c,scale k v
  | _ -> invalid_arg "non-affine guard normalization"
let inequality a b =
  let ac,av=linear a in let bc,bv=linear b in Z.sub bc ac,merge bv(scale Z.minus_one av)
let rec conjunction = function L.And(a,b)->conjunction a @ conjunction b | t->[t]
let same_coefficients a b = Coefficients.equal Z.equal a b
let expression_nonnegative known expr =
  let c,v=linear expr in Z.sign c>=0 && Coefficients.for_all(fun id k->
    Z.sign k>=0 && id<List.length known && List.nth known id)v
let simplify_test known guaranteed test =
  let facts=List.filter_map(function L.LE(a,b)->Some(inequality a b)|_->None)guaranteed in
  let terms=List.fold_left(fun kept term -> match term with
    | L.TConstantTest true -> kept
    | L.LE(a,b) when affine a && affine b ->
      let c,v=inequality a b in
      let always=Z.sign c>=0 && Coefficients.for_all(fun id k->
        Z.sign k>=0 && id<List.length known && List.nth known id)v in
      let entailed=List.exists(fun (fc,fv)->same_coefficients v fv && Z.compare c fc>=0)facts in
      if always || entailed then kept else
      let stronger=List.exists(function
        | L.LE(x,y) when affine x && affine y ->let kc,kv=inequality x y in same_coefficients v kv && Z.compare kc c<=0
        | _->false)kept in
      if stronger then kept else
      List.filter(function
        | L.LE(x,y) when affine x && affine y ->let kc,kv=inequality x y in not(same_coefficients v kv && Z.compare c kc<0)
        | _->true)kept @ [term]
    | _->kept @ [term])[](conjunction test) in
  match terms with []->L.TConstantTest true | first::rest->List.fold_left(fun a b->L.And(a,b))first rest
let guard test body = match test with L.TConstantTest true->body|_->L.Guard(test,body)
let rec adapt_at depth known = function
  | L.Loop(lower,upper,body) when affine lower && affine upper ->
    L.Loop(lower,upper,adapt_at(depth+1)(expression_nonnegative known lower::known)body)
  | L.Loop(lower,upper,body) ->
    let lo=choose depth (if affine lower then lower else zero)(max_leaves lower)in
    let hi=choose depth (upper_enclosure upper)(min_leaves upper)in
    let iterator=L.Var(nat 0)in
    let inner_known=expression_nonnegative known lo::known in
    let facts=[L.LE(shift lo,iterator);L.LE(L.Sum(iterator,one),shift hi)]in
    let membership=L.And(lower_membership(shift lower)iterator,upper_membership iterator(shift upper))in
    L.Loop(lo,hi,guard(simplify_test inner_known facts membership)(adapt_at(depth+1)inner_known body))
  | L.Guard(test,body) ->guard(simplify_test known []test)(adapt_at depth known body)
  | L.Instr _ as body ->body
  | L.Seq sequence ->L.Seq(adapt_sequence_at depth known sequence)
and adapt_sequence_at depth known = function
  | L.SNil ->L.SNil
  | L.SCons(head,tail)->L.SCons(adapt_at depth known head,adapt_sequence_at depth known tail)
let adapt_bounds body=adapt_at 0 []body

let propose instructions =
  if mode () = "disabled" then None else try
    incr invocations;
    let path = Filename.concat (root ()) (Printf.sprintf "guardcert-phase-%d-%d" (Unix.getpid ()) !invocations) in
    mkdir path;
    let path = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
    let arrays = List.sort_uniq compare (List.concat_map (fun instruction ->
      List.map fst (instruction.M.instruction_write::instruction.M.instruction_reads)) instructions) in
    let maximum = List.fold_left (fun maximum id -> Z.max maximum (GuardMemoryNumbers.export_positive id)) Z.one arrays in
    let context = List.init 5 (fun index -> GuardMemoryNumbers.import_positive (Z.add maximum (Z.of_int (index+1)))) in
    (* Export the parametric canonical source, without the host's machine-word
       profile guard. The final certified source/candidate factory supplies
       that profile to BOTH models; it does not rely on scheduler arithmetic.
       In particular, Pluto's signed-int matrix reader cannot represent the
       +2147483648 bias of a signed32 minimum-bound constraint. *)
    let code = GuardMemoryScalarLoops.memory_scalar_rectangle (nat 0) (nat 3) (nat 2) instructions in
    let source = ((code,context),List.map (fun id -> id,()) (context@arrays)) in
    emit (Filename.concat path "source.loop") (statement "" code);
    let outcome = ref None in
    ImpureConfig.Core.Base.bind (Pipeline.checked_memory_tiled_prepared_loop (run path) source)
      (fun result -> outcome := Some result; ());
    match !outcome with
    | Some (Some (((generated,_),_),witnesses),true) ->
      emit (Filename.concat path "raw-generated.loop") (statement "" generated);
      let generated=adapt_bounds generated in
      emit (Filename.concat path "generated.loop") (statement "" generated);
      emit (Filename.concat path "pipeline-result.txt") "phase-validation=accepted\nprepared-codegen=successful\n";
      if Sys.getenv_opt "GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS"=Some "1" then begin
        diagnose path instructions context arrays generated witnesses;
        let checked=ref None in
        ImpureConfig.Core.Base.bind
          (Pipeline.checked_memory_scalar_generated_tiling (nat 3) (small 32) (nat 2)
            instructions context arrays generated witnesses)
          (fun result -> checked:=Some result; ());
        emit(Filename.concat path "candidate-domain-check.txt")
          (match !checked with Some(valid,alarm_free)->Printf.sprintf "valid=%b alarm-free=%b\n" valid alarm_free
            | None->"no result\n")
      end;
      if List.exists(fun w -> w.TilingWitness.stw_links <> [])witnesses then begin
        emit (Filename.concat path "receipt.txt") "affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nbound-adaptation=proposed\nactual-candidate-check=pending\n";
        Some (ClightTensorGeneratedCandidates.TensorGeneratedTiled (generated,witnesses))
      end else (match reindex generated with
        | Some steps -> Some (ClightTensorGeneratedCandidates.TensorGeneratedMapped (generated,steps))
        | None -> emit (Filename.concat path "refusal.txt") "generated coordinate reindex outside current bridge\n"; None)

    | _ -> emit (Filename.concat path "refusal.txt") "pipeline refused or alarmed\n"; None
  with Invalid_argument _ | Failure _ | Sys_error _ | Stack_overflow -> None
