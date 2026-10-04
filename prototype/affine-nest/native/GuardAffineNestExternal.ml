(* External candidate data is parsed, then consumed by the same proved checks. *)
module L = GuardMemoryLoops.L
module C = GuardMemoryCandidate
let rec size = function Datatypes.O -> 0 | Datatypes.S n -> 1 + size n
let atom text = C.Atom text
let list values = C.List values
let integer value = atom (Z.to_string (GuardMemoryNumbers.export_integer value))
let rec expression = function
  | L.Constant value -> list [atom "constant";integer value]
  | L.Var index -> list [atom "var";atom (string_of_int (size index))]
  | L.Sum (a,b) -> list [atom "sum";expression a;expression b]
  | L.Mult (factor,a) -> list [atom "scale";integer factor;expression a]
  | L.Div (a,d) -> list [atom "div";expression a;integer d]
  | L.Mod (a,d) -> list [atom "mod";expression a;integer d]
  | L.Min (a,b) -> list [atom "min";expression a;expression b]
  | L.Max (a,b) -> list [atom "max";expression a;expression b]
let rec test = function
  | L.LE (a,b) -> list [atom "le";expression a;expression b]
  | L.EQ (a,b) -> list [atom "eq";expression a;expression b]
  | L.And (a,b) -> list [atom "and";test a;test b]
  | L.Or (a,b) -> list [atom "or";test a;test b]
  | L.Not a -> list [atom "not";test a]
  | L.TConstantTest value -> list [atom "eq";list [atom "constant";atom "0"];
      list [atom "constant";atom (if value then "0" else "1")]]
let rec render = function C.Atom text -> text | C.List members -> "("^String.concat " " (List.map render members)^")"
let source_syntax source =
  let instructions = ref [] and ordinal = ref 0 in
  let rec statement = function
    | L.Loop (lower,upper,body) -> list [atom "loop";expression lower;expression upper;statement body]
    | L.Guard (condition,body) -> list [atom "guard";test condition;statement body]
    | L.Instr (instruction,arguments) ->
        let site = !ordinal in incr ordinal; instructions := instruction :: !instructions;
        list [atom "instr";atom (string_of_int site);list (List.map expression arguments)]
    | L.Seq statements -> list (atom "seq" :: sequence statements)
  and sequence = function L.SNil -> [] | L.SCons (first,rest) ->
    let first = statement first in first :: sequence rest in
  let syntax = statement source in syntax,List.rev !instructions
let access (identifier,rows) = list [atom "array";atom (Z.to_string (GuardMemoryNumbers.export_positive identifier));
  list (List.map (fun (coefficients,bias) -> list [list (List.map integer coefficients);integer bias]) rows)]
let rec value = function
  | GuardMemoryRuntime.ConstantValue n -> list [atom "constant";integer n]
  | GuardMemoryRuntime.ParameterValue n -> list [atom "argument";atom (string_of_int (size n))]
  | GuardMemoryRuntime.LoadedValue n -> list [atom "loaded";atom (string_of_int (size n))]
  | GuardMemoryRuntime.AddValue (a,b) -> list [atom "add";value a;value b]
  | GuardMemoryRuntime.SubValue (a,b) -> list [atom "sub";value a;value b]
  | GuardMemoryRuntime.MulValue (a,b) -> list [atom "mul";value a;value b]
let instruction item = list [atom "store";access item.GuardMemoryInstr.instruction_write;
  list (List.map access item.GuardMemoryInstr.instruction_reads);value item.GuardMemoryInstr.instruction_value]
let request_syntax request syntax instructions =
  let positive id = atom (Z.to_string (GuardMemoryNumbers.export_positive id)) in
  list [atom "affine-request";
    list [atom "context";list (List.map positive request.AffineNestCheckedCompiler.affine_requested_context)];
    list [atom "pointers";list (List.map positive request.AffineNestCheckedCompiler.affine_requested_pointers)];
    list [atom "axes";list (List.map (fun (low,high) -> list [integer low;integer high]) request.AffineNestCheckedCompiler.affine_requested_axes)];
    list [atom "instructions";list (List.map instruction instructions)];list [atom "source";syntax]]
let source_identity request syntax instructions =
  let fields = match request_syntax request syntax instructions with
    | C.List (_::fields) -> fields | _ -> assert false in
  let fields = List.filter (function C.List (C.Atom "axes"::_) -> false | _ -> true) fields in
  Digest.to_hex (Digest.string (render (list (atom "affine-source"::fields))))
let request_text request syntax instructions =
  let fields = match request_syntax request syntax instructions with
    | C.List fields -> fields | _ -> assert false in
  render (list (fields @ [list [atom "source-identity";atom (source_identity request syntax instructions)]])) ^ "\n"
let fingerprint request syntax instructions = Digest.to_hex (Digest.string (request_text request syntax instructions))
let export_request request syntax instructions =
  match Sys.getenv_opt "GUARDCERT_AFFINE_REQUEST_DIR" with
  | None -> ()
  | Some directory ->
      let text = request_text request syntax instructions in
      let name = fingerprint request syntax instructions ^ ".sexp" in
      let path = Filename.concat directory name in
      let channel = open_out path in
      Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel text)
let template = lazy (match Sys.getenv_opt "GUARDCERT_AFFINE_CANDIDATE" with
  | None -> None
  | Some path ->
      let channel = open_in path in
      Fun.protect ~finally:(fun () -> close_in channel) (fun () -> Some (C.parse (C.read_input channel))))
let affine_step = function
  | C.List [C.Atom "swap";position] -> GuardMemoryAffineReindex.MemoryReindexSwap (C.natural (C.small position))
  | C.List [C.Atom "shift";position;delta] -> GuardMemoryAffineReindex.MemoryReindexShift
      (C.natural (C.small position),GuardMemoryNumbers.import_integer (C.integer delta))
  | C.List [C.Atom "skew";target;source;factor] -> GuardMemoryAffineReindex.MemoryReindexSkew
      (C.natural (C.small target),C.natural (C.small source),GuardMemoryNumbers.import_integer (C.integer factor))
  | C.List [C.Atom "reflect";position] -> GuardMemoryAffineReindex.MemoryReindexReflect (C.natural (C.small position))
  | _ -> invalid_arg "affine candidate reindex step"
let identity_box source axes =
  let rec headers collected = function
    | L.Loop (lower,upper,body) -> headers ((lower,upper)::collected) body
    | body -> List.rev collected,body in
  let headers,body = headers [] source in
  let dimensions = List.length headers in
  if dimensions < 2 || List.length axes <> dimensions then invalid_arg "composed tile box";
  let rec expression shift = function
    | L.Var index -> L.Var (C.natural (shift + size index))
    | L.Sum (a,b) -> L.Sum (expression shift a,expression shift b)
    | L.Mult (k,a) -> L.Mult (k,expression shift a)
    | L.Div (a,k) -> L.Div (expression shift a,k)
    | L.Mod (a,k) -> L.Mod (expression shift a,k)
    | L.Min (a,b) -> L.Min (expression shift a,expression shift b)
    | L.Max (a,b) -> L.Max (expression shift a,expression shift b)
    | constant -> constant in
  let tests = List.mapi (fun axis (lower,upper) ->
    let coordinate = L.Var (C.natural (dimensions-1-axis)) in
    L.And (L.LE (expression (dimensions-axis) lower,coordinate),
      L.LE (coordinate,L.Sum (expression (dimensions-axis) upper,
        L.Constant (GuardMemoryNumbers.import_integer (Z.of_int (-1))))))) headers in
  let domain = match tests with first::rest -> List.fold_left (fun a b -> L.And(a,b)) first rest
    | [] -> invalid_arg "empty composed tile domain" in
  List.fold_right (fun (lower,upper) body -> L.Loop (L.Constant lower,L.Constant upper,body))
    axes (L.Guard (domain,body))

let propose request source instructions =
  let dimensions = List.length request.AffineNestCheckedCompiler.affine_requested_axes in
  let rec choose current = function
    | C.List [C.Atom "chain";first;second] ->
        (match choose current first with
         | None -> None
         | Some (middle,first_evidence) ->
             (match choose middle second with
              | None -> None
              | Some (candidate,second_evidence) -> Some(candidate,
                  AffineNestCandidateEvidence.AffineChainEvidence(middle,first_evidence,second_evidence))))
    | C.List [C.Atom "partition";C.List conditions;syntax] ->
        if List.length conditions > 2 then invalid_arg "composed split cut limit";
        let conditions = List.map C.loop_test conditions in
        let expanded = AffineNestDomainSplit.affine_partitioned_sources conditions current in
        (match choose expanded syntax with None -> None | Some(candidate,evidence) ->
          Some(candidate,AffineNestCandidateEvidence.AffineDomainEvidence(conditions,evidence)))
    | C.List [C.Atom kind;C.List conditions;syntax]
        when kind="partition-target" || kind="partition-target-wrong" ->
        if List.length conditions > 2 then invalid_arg "target split cut limit";
        let conditions = List.map C.loop_test conditions in
        (match choose current syntax with
         | None -> None
         | Some(base,evidence) ->
             let expanded = AffineNestDomainSplit.affine_partitioned_sources conditions base in
             let rec drop_part = function
               | L.Loop(lower,upper,body) -> L.Loop(lower,upper,drop_part body)
               | L.Seq(L.SCons(first,_)) -> L.Seq(L.SCons(first,L.SNil))
               | body -> body in
             let candidate = if kind="partition-target-wrong" then drop_part expanded else expanded in
             Some(candidate,AffineNestCandidateEvidence.AffinePartitionTargetEvidence(conditions,base,evidence)))
    | C.List (C.Atom tile::rows::columns::extra) when tile="tile-box" || tile="tile-box-wrong" ->
        let axes = match extra with
          | [] -> request.AffineNestCheckedCompiler.affine_requested_axes
          | [C.List axes] -> List.map (function C.List [lower;upper] ->
              GuardMemoryNumbers.import_integer(C.integer lower),GuardMemoryNumbers.import_integer(C.integer upper)
              | _ -> invalid_arg "composed tile axis") axes
          | _ -> invalid_arg "composed tile arguments" in
        let staged = {request with AffineNestCheckedCompiler.affine_requested_loop=current;
          AffineNestCheckedCompiler.affine_requested_axes=axes} in
        let boxed = identity_box current axes in
        let rows,columns = C.small rows,C.small columns in
        let candidate,witnesses = GuardAffineNestTiling.propose staged boxed rows columns in
        let witnesses = if tile="tile-box-wrong" then
          snd(GuardAffineNestTiling.propose staged boxed (rows+1) (columns+1)) else witnesses in
        Some(candidate,AffineNestCandidateEvidence.AffineTilingEvidence witnesses)
    | C.List [C.Atom "request";C.Atom identity;syntax] ->
        if identity = fingerprint request source instructions then choose current syntax else None
    | C.List [C.Atom "source";C.Atom identity;syntax] ->
        if identity = source_identity request source instructions then choose current syntax else None
    | C.List [C.Atom "rank";rank;syntax] -> if C.small rank = dimensions then choose current syntax else None
    | C.List (C.Atom "choices"::choices) ->
        let rec first = function [] -> None | item::rest -> match choose current item with Some _ as result -> result | None -> first rest in
        first choices
    | C.List [C.Atom "map-index";C.List steps;syntax] ->
        if List.length steps > 32 then invalid_arg "affine candidate reindex limit";
        Some (C.instantiate_at instructions None syntax,
              AffineNestCandidateEvidence.AffineIndexEvidence (List.map affine_step steps))
    | C.List [C.Atom "site-order";C.List positions;syntax] ->
        if List.length positions > 64 then invalid_arg "affine static site permutation limit";
        (match choose current syntax with
         | Some (candidate,AffineNestCandidateEvidence.AffineIndexEvidence steps) ->
             Some (candidate,AffineNestCandidateEvidence.AffineSiteEvidence
               (steps,List.map (fun position -> C.natural (C.small position)) positions))
         | _ -> None)
    | C.List [C.Atom "split-domain";C.List conditions;syntax] ->
        if List.length conditions > 2 then invalid_arg "affine split cut limit";
        let conditions = List.map C.loop_test conditions in
        (match choose current syntax with
         | Some (candidate,AffineNestCandidateEvidence.AffineIndexEvidence steps) ->
             Some(candidate,AffineNestCandidateEvidence.AffineSplitEvidence(conditions,steps,[]))
         | Some (candidate,AffineNestCandidateEvidence.AffineSiteEvidence(steps,positions)) ->
             Some(candidate,AffineNestCandidateEvidence.AffineSplitEvidence(conditions,steps,positions))
         | _ -> None)
    | syntax -> Some (C.instantiate_at instructions None syntax,AffineNestCandidateEvidence.AffineIndexEvidence []) in
  match Lazy.force template with None -> None | Some syntax -> choose request.AffineNestCheckedCompiler.affine_requested_loop syntax
