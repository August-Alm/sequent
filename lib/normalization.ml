(**
  Module: Normalization
  Main entry point: Compose three normalization passes
  
  Pass 1: Shrinking (Core → Core) - naming + reduction rules
  Pass 2: Collapsing (Core → Cut) - apply 4 symmetric transformations
  Pass 3: Linearization (Cut → Cut) - insert explicit substitutions
*)

module CT = Core.Terms
module Cut = Cut.Terms

(** Normalize Core definitions to Cut definitions *)
let normalize_definitions (defs: CT.definitions) : Cut.definitions =
  (* Pass 1: Shrinking - naming and reduction *)
  let shrunken_defs = Shrinking.shrink_definitions defs in
  
  (* Pass 2: Collapsing - Core to Cut transformation *)
  let collapsed_defs = Collapsing.collapse_definitions shrunken_defs in
  
  (* Pass 3: Linearization - insert explicit substitutions *)
  Linearization.linearize_definitions collapsed_defs
