# Type Instantiation Analysis for Core→Cut Normalization

## Question
How can we get polymorphic type instantiation information (the `τ` arguments in `Let`, `New`, `Invoke`) into the Core AST so normalization can generate properly typed Cut code?

## Answer: Route 1 is Sufficient ✅

**All the type information needed is already available in Lang and can be passed to Core.**

### Current State

1. **Lang typed_term HAS type instantiations**:
   - `TyTmIns(t, ty_arg, k, ty_result)` - explicit type instantiation
   - `TyTmCtor(ctor, ty_args, tm_args, ty)` - constructor with type args
   - `TyTmDtor(dtor, ty_args, tm_args, ty)` - destructor with type args

2. **Core AST ALREADY SUPPORTS type arguments**:
   ```ocaml
   type statement =
     | Call of Path.t * (Type.t list) * (producer list) * (consumer list)
                         ^^^^^^^^^^^^^^ Type arguments here!
   
   type xtor_args = (Type.t list) * (producer list) * (consumer list)
                     ^^^^^^^^^^^^^^ Type arguments here!
   ```

3. **convert.ml ALREADY extracts type args** for constructors/destructors:
   ```ocaml
   | LTm.TyTmCtor (ctor, ty_args, tm_args, _ty) ->
     CTm.Constructor (ctor.symbol, (
       List.map convert_typ ty_args,  ✅ Already working!
       List.map convert tm_args,
       []
     ))
   
   | LTm.TyTmDtor (dtor, ty_args, tm_args, _ty) ->
     CTm.Destructor (dtor.symbol, (
       List.map convert_typ ty_args,  ✅ Already working!
       ...
     ))
   ```

4. **BUT convert.ml has TODOs** for function Call statements:
   ```ocaml
   Line 128: let ty_args = [] in (* TODO: extract actual type instantiations *)
   Line 138: CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, ...))
   Line 153: let ty_args = [] in (* TODO: extract actual type instantiations *)
   ```

   Note: `collect_type_and_term_args` already extracts the type args (line 130)!

### Solution: Fix the TODOs in convert.ml

Simply use the already-collected `ty_args` instead of `[]`:

**File: lib/convert.ml**

**Change 1** (line ~125):
```ocaml
(* BEFORE *)
| LTm.TyTmSym (sym, _ty) ->
  let alpha = Ident.fresh () in
  let ty_args = [] in (* TODO: extract actual type instantiations *)
  CTm.Mu (alpha, CTm.Call (sym, ty_args, [], [CTm.Covar alpha]))

(* AFTER *)
| LTm.TyTmSym (sym, _ty) ->
  (* Symbol references without application have no type args yet *)
  let alpha = Ident.fresh () in
  CTm.Mu (alpha, CTm.Call (sym, [], [], [CTm.Covar alpha]))
```

**Change 2** (line ~136):
```ocaml
(* BEFORE *)
if provided_arity = required_arity then
  let alpha = Ident.fresh () in
  CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, ...))
  
(* Already correct! ty_args is from collect_type_and_term_args *)
```

**Change 3** (line ~151):
```ocaml
(* BEFORE *)
let rec make_lambdas remaining_tys provided_args =
  match remaining_tys with
  | [] -> 
    let alpha = Ident.fresh () in
    let ty_args = [] in (* TODO: extract actual type instantiations *)
    CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, ...))

(* AFTER *)
let rec make_lambdas remaining_tys provided_args =
  match remaining_tys with
  | [] -> 
    let alpha = Ident.fresh () in
    (* Use the ty_args from outer scope (from collect_type_and_term_args) *)
    CTm.Mu (alpha, CTm.Call (sym, List.map convert_typ ty_args, ...))
```

### Why This Works

The key insight is that `collect_type_and_term_args` (lines 95-101) already walks the nested structure of:
```
TyTmApp(TyTmIns(TyTmIns(TyTmSym(f), t1), t2), arg)
```

And extracts:
- `ty_args = [t1, t2]` ✅
- `tm_args = [arg]` ✅

So all we need to do is USE those collected `ty_args` instead of discarding them!

### Flow After Fix

1. **Lang type checker** produces fully typed `typed_term` with `TyTmIns` nodes
2. **convert.ml** extracts type args via `collect_type_and_term_args`
3. **Core AST** stores type args in `Call` and `xtor_args`
4. **normalization.ml** reads type args from Core and passes them to Cut
5. **Cut AST** uses type args in `Let`, `New`, `Invoke`

### Route 2 (Unnecessary)

We don't need to modify Core type checking to produce annotated terms because:
- Lang already does type checking and produces fully annotated `typed_term`
- The conversion just needs to preserve this information (not discard it)
- Core type checking is for validation, not for inference/annotation

## Recommendation

**Implement Route 1**: Fix the 3 TODOs in convert.ml to properly pass `ty_args` to `Call` statements.

This is a small, localized change that will make the entire pipeline work correctly without requiring changes to Core's type system or type checker.
