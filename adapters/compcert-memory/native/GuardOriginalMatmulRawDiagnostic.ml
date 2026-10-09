(* Preserve the exact incoming statement, including every skip/sequence.
   This is an untrusted syntax exporter used to diagnose matcher obligations. *)
open Format
open Camlcoq
open AST
open Ctypes
open Clight
open ExportBase
open ExportCtypes
let expr = ExportClight.expr
let rec stmt p = function
  | Sskip ->
      fprintf p "Sskip"
  | Sassign(e1, e2) ->
      fprintf p "@[<hov 2>(Sassign@ %a@ %a)@]" expr e1 expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hov 2>(Sset %a@ %a)@]" ident id expr e2
  | Scall(optid, e1, el) ->
      fprintf p "@[<hov 2>(Scall %a@ %a@ %a)@]"
        (print_option ident) optid expr e1 (print_list expr) el
  | Sbuiltin(optid, ef, tyl, el) ->
      fprintf p "@[<hov 2>(Sbuiltin %a@ %a@ %a@ %a)@]"
        (print_option ident) optid
        external_function ef
        typlist tyl
        (print_list expr) el
  | Ssequence(s1, s2) ->
      fprintf p "@[<hv 2>(Ssequence@ %a@ %a)@]" stmt s1 stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<hv 2>(Sifthenelse %a@ %a@ %a)@]" expr e stmt s1 stmt s2
  | Sloop(s1, s2) ->
      fprintf p "@[<hv 2>(Sloop@ %a@ %a)@]" stmt s1 stmt s2
  | Sbreak ->
      fprintf p "Sbreak"
  | Scontinue ->
      fprintf p "Scontinue"
  | Sswitch(e, cases) ->
      fprintf p "@[<hv 2>(Sswitch %a@ %a)@]" expr e lblstmts cases
  | Sreturn e ->
      fprintf p "@[<hv 2>(Sreturn %a)@]" (print_option expr) e
  | Slabel(lbl, s1) ->
      fprintf p "@[<hv 2>(Slabel %a@ %a)@]" ident lbl stmt s1
  | Sgoto lbl ->
      fprintf p "(Sgoto %a)" ident lbl

and lblstmts p = function
  | LSnil ->
      (fprintf p "LSnil")
  | LScons(lbl, s, ls) ->
      fprintf p "@[<hv 2>(LScons %a@ %a@ %a)@]"
              (print_option coqZ) lbl stmt s lblstmts ls


let rec inspect = function
  | Slabel (label,body) ->
    if List.mem label (GuardScopFrontend.chosen_labels ()) then begin
      let path = Filename.concat (Sys.getenv "GUARDCERT_ORIGINAL_OUTPUT") "RawOriginalMatmul.v" in
      let output = open_out path in
      Fun.protect ~finally:(fun () -> close_out output) (fun () ->
        output_string output "From Stdlib Require Import List String ZArith.\nFrom compcert.lib Require Import Coqlib Integers Floats.\nFrom compcert.common Require Import AST.\nFrom compcert.cfrontend Require Import Ctypes Cop Clight.\nFrom compcert.export Require Import Clightdefs.\nFrom GuardOriginalMatmul Require Import OriginalMatmul.\nImport Clightdefs.ClightNotations.\nLocal Open Scope Z_scope.\nLocal Open Scope clight_scope.\n";
        let formatter = formatter_of_out_channel output in
        fprintf formatter "Definition raw_original_matmul_region : statement :=@ %a.@." stmt body)
    end; inspect body
  | Ssequence (first,second) | Sloop (first,second) -> inspect first; inspect second
  | Sifthenelse (_,yes,no) -> inspect yes; inspect no
  | Sswitch (_,cases) -> inspect_cases cases
  | _ -> ()
and inspect_cases = function
  | LSnil -> () | LScons (_,body,rest) -> inspect body; inspect_cases rest
let print program =
  List.iter (fun (_,definition) -> match definition with
    | Gfun (Internal fn) -> inspect fn.fn_body | _ -> ()) program.prog_defs;
  GuardOriginalMatmulDiagnostic.print program
