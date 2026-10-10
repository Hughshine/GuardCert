(* The retained source relations are proposal data for the adapter. The actual
   source model and final extracted checker remain the semantic authority. *)
include GuardSelectedDoubleMixedPhaseV3
let current_source = ref None
let phase before =
  current_source := Some before;
  GuardSelectedDoubleMixedPhaseV3.phase before
