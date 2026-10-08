(* Ordinary signed-bound proposals, never a semantic certificate. The original
   extracted source/candidate checker validates the complete rewritten Loop.
   Intervals use mathematical integers; machine safety remains its obligation. *)
include GuardTightPreparedTensorCandidate
module Bounds = GuardMemoryArrayBackend.MemoryNested.A

type interval = { low : Z.t; high : Z.t }
let point value = { low=value; high=value }
let constant value = L.Constant(GuardMemoryNumbers.import_integer value)
let rec interval environment = function
  | L.Constant value -> point(GuardMemoryNumbers.export_integer value)
  | L.Var index -> List.nth environment (GuardOpenScopIO.nat_to_int index)
  | L.Sum(first,second) ->
    let a=interval environment first and b=interval environment second in
    { low=Z.add a.low b.low; high=Z.add a.high b.high }
  | L.Mult(factor,expression) ->
    let factor=GuardMemoryNumbers.export_integer factor in
    let value=interval environment expression in
    let a=Z.mul factor value.low and b=Z.mul factor value.high in
    { low=Z.min a b; high=Z.max a b }
  | L.Div(expression,denominator) ->
    let denominator=GuardMemoryNumbers.export_integer denominator in
    if Z.sign denominator<=0 then invalid_arg "signed enclosure denominator";
    let value=interval environment expression in
    { low=Z.fdiv value.low denominator; high=Z.fdiv value.high denominator }
  | L.Min(first,second) ->
    let a=interval environment first and b=interval environment second in
    { low=Z.min a.low b.low; high=Z.min a.high b.high }
  | L.Max(first,second) ->
    let a=interval environment first and b=interval environment second in
    { low=Z.max a.low b.low; high=Z.max a.high b.high }
  | L.Mod _ -> invalid_arg "modulo bound outside signed enclosure proposal"

(* Every max leaf is a lower enclosure; every min leaf is an upper enclosure.
   Prefer an affine leaf involving surrounding iterators, then any affine leaf.
   If there is none, use the signed interval endpoint instead of zero or e+1. *)
let enclosure depth fallback leaves =
  let leaves=List.filter affine leaves in
  match leaves with
  | [] -> fallback
  | first::rest ->
    fst(List.fold_left(fun (best,score) expression ->
      let current=loop_score depth expression in
      if current>score then expression,current else best,score)
      (first,loop_score depth first)rest)

let known environment = List.map(fun value -> Z.sign value.low>=0)environment
let body_interval environment lower upper =
  let low=(interval environment lower).low in
  let high=Z.pred((interval environment upper).high) in
  (* An empty envelope has no body executions. Retaining a nonempty abstract
     interval avoids proposing unrelated failures while visiting dead syntax. *)
  { low; high=Z.max low high }

let rec adapt environment depth = function
  | L.Loop(lower,upper,body) when affine lower && affine upper ->
    let inner=body_interval environment lower upper :: environment in
    L.Loop(lower,upper,adapt inner (depth+1)body)
  | L.Loop(lower,upper,body) ->
    let lo=enclosure depth (constant((interval environment lower).low))(max_leaves lower) in
    let hi=enclosure depth (constant((interval environment upper).high))(min_leaves upper) in
    let iterator=L.Var(nat 0) in
    let envelope=body_interval environment lo hi :: environment in
    let membership=L.And(lower_membership(shift lower)iterator,
                         upper_membership iterator(shift upper)) in
    let facts=[L.LE(shift lo,iterator);L.LE(L.Sum(iterator,one),shift hi)] in
    let membership=simplify_test (known envelope) facts membership in
    (* Inside the membership guard the original bounds constrain the iterator. *)
    let inside=body_interval environment lower upper :: environment in
    L.Loop(lo,hi,guard membership (adapt inside (depth+1)body))
  | L.Guard(test,body) ->
    guard(simplify_test (known environment) [] test)(adapt environment depth body)
  | L.Instr _ as body -> body
  | L.Seq sequence -> L.Seq(adapt_sequence environment depth sequence)
and adapt_sequence environment depth = function
  | L.SNil -> L.SNil
  | L.SCons(head,tail) ->
    L.SCons(adapt environment depth head,adapt_sequence environment depth tail)

let propose_bounds bounds body =
  let environment=List.map(fun value ->
    { low=GuardMemoryNumbers.export_integer value.Bounds.lower;
      high=GuardMemoryNumbers.export_integer value.Bounds.upper })bounds in
  if List.exists(fun value -> Z.compare value.low value.high>0)environment then
    invalid_arg "empty request interval";
  adapt environment 0 body
