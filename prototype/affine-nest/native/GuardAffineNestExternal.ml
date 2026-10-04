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
let propose request source instructions =
  let dimensions = List.length request.AffineNestCheckedCompiler.affine_requested_axes in
  let rec choose = function
    | C.List [C.Atom "request";C.Atom identity;syntax] ->
        if identity = fingerprint request source instructions then choose syntax else None
    | C.List [C.Atom "source";C.Atom identity;syntax] ->
        if identity = source_identity request source instructions then choose syntax else None
    | C.List [C.Atom "rank";rank;syntax] -> if C.small rank = dimensions then choose syntax else None
    | C.List (C.Atom "choices"::choices) ->
        let rec first = function [] -> None | item::rest -> match choose item with Some _ as result -> result | None -> first rest in
        first choices
    | C.List [C.Atom "map-index";C.List steps;syntax] ->
        if List.length steps > 32 then invalid_arg "affine candidate reindex limit";
        Some (C.instantiate_at instructions None syntax,
              AffineNestCandidateEvidence.AffineIndexEvidence (List.map affine_step steps))
    | C.List [C.Atom "site-order";C.List positions;syntax] ->
        if List.length positions > 64 then invalid_arg "affine static site permutation limit";
        (match choose syntax with
         | Some (candidate,AffineNestCandidateEvidence.AffineIndexEvidence steps) ->
             Some (candidate,AffineNestCandidateEvidence.AffineSiteEvidence
               (steps,List.map (fun position -> C.natural (C.small position)) positions))
         | _ -> None)
    | syntax -> Some (C.instantiate_at instructions None syntax,AffineNestCandidateEvidence.AffineIndexEvidence []) in
  match Lazy.force template with None -> None | Some syntax -> choose syntax
