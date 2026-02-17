(**
  Direct Melcore test for nat type - bypasses parsing/desugaring
  to isolate whether the issue is in desugar.ml or types.ml
*)

module MTy = Melcore.Types
module MTm = Melcore.Terms
module MPrint = Melcore.Printing

open Common.Identifiers

(* === Build nat signature directly in Melcore === *)

let nat_sym = Path.of_string "nat"
let zero_sym = Path.of_string "zero"
let succ_sym = Path.of_string "succ"

(* Use recursive lazy - this is what desugar does *)
let rec nat_sgn_lazy : MTy.sgn_typ Lazy.t =
  lazy
  { MTy.name = nat_sym
  ; parameters = []
  ; xtors =
    [ { MTy.name = zero_sym
      ; parameters = []
      ; existentials = []
      ; arguments = []
      ; main = MTy.Sym (nat_sym, MTy.Pos, nat_sgn_lazy)
      }
    ; { MTy.name = succ_sym
      ; parameters = []
      ; existentials = []
      ; arguments = [MTy.Sym (nat_sym, MTy.Pos, nat_sgn_lazy)]
      ; main = MTy.Sym (nat_sym, MTy.Pos, nat_sgn_lazy)
      }
    ]
  }

let nat_sgn = Lazy.force nat_sgn_lazy

let () =
  Printf.printf "=== Direct Melcore nat test ===\n\n";
  
  Printf.printf "Signature built successfully\n";
  Printf.printf "  xtors: %d\n" (List.length nat_sgn.xtors);
  List.iter (fun (x: MTy.xtor) ->
    Printf.printf "  - %s: main = %s\n" (Path.name x.name) (MPrint.typ_to_string x.main)
  ) nat_sgn.xtors;
  
  (* Now test type checking *)
  Printf.printf "\n=== Type checking ===\n";
  
  (* Build a simple term: match n with { zero => zero; succ(m) => succ(m) } *)
  let n_var = Ident.mk "n" in
  let m_var = Ident.mk "m" in
  
  let nat_typ = MTy.Data nat_sgn in
  
  (* zero constructor *)
  let zero_xtor : MTy.xtor = List.hd nat_sgn.xtors in
  let succ_xtor : MTy.xtor = List.nth nat_sgn.xtors 1 in
  
  (* The term: match n with { zero => zero; succ(m) => succ(m) } *)
  let term : MTm.term = 
    MTm.Match 
      ( MTm.Var n_var  (* scrutinee *)
      , [ (zero_xtor, [], MTm.Ctor (zero_xtor, []))  (* zero => zero *)
        ; (succ_xtor, [m_var], MTm.Ctor (succ_xtor, [MTm.Var m_var]))  (* succ(m) => succ(m) *)
        ]
      )
  in
  
  Printf.printf "Term: %s\n" (MPrint.term_to_string term);
  
  (* Build a term definition *)
  let iszero_def : MTm.term_def =
    { name = Path.of_string "iszero"
    ; type_args = []
    ; term_args = [(n_var, nat_typ)]
    ; return_type = nat_typ
    ; body = term
    }
  in
  
  (* Empty definitions context *)
  let defs : MTm.definitions = Path.of_list [] in
  
  Printf.printf "Checking iszero: nat -> nat\n";
  
  match MTm.check_definition defs iszero_def with
  | Ok _ -> Printf.printf "SUCCESS: Type-checking passed!\n"
  | Error e -> 
      Printf.printf "ERROR: %s\n" (match e with
        | MTm.UnboundVariable v -> "Unbound: " ^ Ident.name v
        | MTm.UnboundSymbol p -> "Unbound symbol: " ^ Path.name p
        | MTm.ExpectedData t -> "Expected data: " ^ MPrint.typ_to_string t
        | MTm.ExpectedCode t -> "Expected code: " ^ MPrint.typ_to_string t
        | MTm.TypeMismatch {expected; actual} -> 
            Printf.sprintf "Type mismatch: expected %s, got %s" 
              (MPrint.typ_to_string expected) (MPrint.typ_to_string actual)
        | MTm.SignatureMismatch _ -> "Signature mismatch"
        | MTm.XtorNotInSignature (x, sgn) -> 
            Printf.sprintf "Xtor %s not in signature %s" 
              (Path.name x.name) (Path.name sgn.name)
        | MTm.NonExhaustive _ -> "Non-exhaustive"
        | MTm.ArityMismatch {xtor; expected; actual} ->
            Printf.sprintf "Arity mismatch for %s: expected %d, got %d"
              (Path.name xtor.name) expected actual
        | MTm.UnificationFailed (t1, t2) ->
            Printf.sprintf "Unification failed: %s vs %s"
              (MPrint.typ_to_string t1) (MPrint.typ_to_string t2)
      )
