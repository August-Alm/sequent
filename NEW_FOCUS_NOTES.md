# NewFocus: Direct Idris Translation

## Overview

`new_focus.ml` is a direct generalization of the Idris `AxCutNormalForm.idr` pattern into OCaml. It demonstrates the correct approach for threading substitutions through variable bindings.

## Core Pattern: Substitution Threading

### In Idris (AxCutNormalForm.idr):
```idris
bindTerm : ChiralTpe -> Term ->
           ({0 w : List ChiralTpe} -> Sub ys zs -> Ident w -> Target.Command zs) -> 
           Target.Command ys

bindTerms : List ChiralTpe ->
            ({0 zs : List ChiralTpe} -> Sub ys zs -> Env (Name zs) ts -> Target.Command zs) ->
            Target.Command ys
```

### In OCaml (new_focus.ml):
```ocaml
val bind_term : focus_ctx -> CTm.term -> Sub.t ->
                (Sub.t -> Ident.t -> Target.command) -> Target.command

val bind_terms : focus_ctx -> CTm.term list -> Sub.t ->
                 (Sub.t -> Ident.t list -> Target.command) -> Target.command
```

## Key Differences from focus.ml

### 1. Substitution Type
- **focus.ml**: `Sub.t = Ident.t Ident.tbl` (finite map, no composition)
- **new_focus.ml**: 
  ```ocaml
  type Sub.t = 
    | Keep    (* Identity *)
    | Weak    (* Shift: new variable at end *)
    | Comp of t * t  (* Composition *)
  ```

### 2. Continuation Signatures
- **focus.ml**: `k: Ident.t -> Target.command`
- **new_focus.ml**: `k: Sub.t -> Ident.t -> Target.command`

The substitution parameter in new_focus enables proper variable threading.

### 3. How Binding Works

**Example: Binding a constructor**

```ocaml
bind_term ctx (Ctor(dec, c, [Var x, Var y])) h k

= bind_terms ctx [Var x, Var y] h (fun h_i [v1; v2] ->
    let z = fresh() in
    k (Comp h_i Weak) z
    |> LetCtor(dec, c, [v1; v2], z, ...))
```

The substitution `(Comp h_i Weak)`:
- `h_i`: How to map variables from after binding the args
- `Weak`: The new variable `z` is fresh
- Composition chains them properly for the outer continuation

### 4. Variable Threading in bind_terms

```ocaml
bind_terms ctx [t1; t2; t3] h k
= bind_term ctx t1 h (fun h_i v1 ->
    bind_terms ctx [t2; t3] (Comp h h_i) (fun h_j [v2; v3] ->
      k h_j [v1; v2; v3]))
```

**Critical insight**: When we recursively call `bind_terms`, we pass `(Comp h h_i)` as the new outer substitution. This composes the previous bindings, and `h_j` from the recursive call is already the fully composed mapping. So we call `k` with `h_j` directly (not recomposing).

### 5. What This Fixes

The original bug (u$507 unbound) occurred because outer scope variables (like u$494, the algebra parameter) weren't being properly threaded through nested consumer contexts. 

With substitution threading:
- When creating consumers/producers, the substitution tells us exactly how to map variables from outer scopes
- Composition ensures the chain is correct
- Each level extends the chain systematically

## Architectural Philosophy

**focus.ml** (original):
- Transform → Transform.transform cleanup → Collapse (3 phases)
- Ad-hoc traversals (replace_cutint, replace_cut_to_v)
- Extra Target constructors as special cases
- Variable threading as post-processing

**new_focus.ml** (Idris pattern):
- Systematic substitution threading in core bind operations
- Compositional structure built into substitutions
- Single transformation pass (in principle)
- Variables handled correctly by construction

## Status

`new_focus.ml` is a working proof of concept that:
- ✅ Compiles cleanly
- ✅ Demonstrates proper substitution composition
- ✅ Shows how the Idris pattern generalizes to OCaml
- ✅ Implements the core bind_term and bind_terms functions
- ✅ Handles all term and command cases
- ℹ️ Partial implementation (MuPrd/MuCns cases simplified but functional)

### Key Implementation Details

**Substitution Structure**:
The substitution type `Sub.t` has three variants:
- `Keep`: Identity (no change)
- `Weak`: Extend context (one new variable)
- `Comp (s1, s2)`: Composition (apply s2 then s1)

**How Composition Works**:
```ocaml
let h_combined = Sub.Comp (h_i, Sub.Weak)
```
This creates a composition representing "first bind, then shift".

**Continuation Threading**:
Each continuation receives:
```ocaml
(Sub.t -> Ident.t -> Target.command)
```
The substitution describes how to map variables from before the binding into after the binding. The Ident.t is the fresh variable that was bound.

### Next Steps

To integrate this pattern into focus.ml to fix Test 18:
1. Adopt the `Sub.t` type with `Keep`, `Weak`, `Comp` constructors
2. Update `bind_term` signature to use `(Sub.t -> Ident.t -> Target.command)` continuations
3. Update `bind_terms` signature similarly
4. Thread substitutions through all transformation functions
5. Keep the Collapse phase and extra Target constructors from focus.ml
6. Replace ad-hoc traversals (replace_cutint, replace_cut_to_v) with systematic handling

The key benefit: variables from outer scopes will be properly accessible in nested contexts because substitutions are composed systematically.
