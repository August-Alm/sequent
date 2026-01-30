# Sequent Calculus Compiler

A compiler for a functional ML-like language with generalized algebraic data types (GADTs) and codata types, compiled through a series of intermediate representations based on sequent calculus.

## Overview

This project implements a multi-stage compiler that translates a surface language with rich type features into explicit sequent calculus representations. The compiler demonstrates how classical sequent calculus provides a natural compilation target for functional languages with both data (products/sums) and codata (functions/streams) constructs.

## Key Features

### Surface Language (Lang)

- **ML-style syntax** with type inference and bidirectional type checking
- **Generalized algebraic data types (GADTs)** with pattern matching
- **Generalized codata types** (observations/destructors) with copattern matching
- **Polymorphism** with explicit type abstraction and application
- **Higher-kinded types** for type-level abstraction
- **Primitive types**: Functions (`->`) and universal quantification (`∀`)

### Type System

- **Bidirectional type checking**: Combines type inference and checking modes
- **Typed intermediate representation**: Preserves type information through compilation
- **GADT support**: Including type equations and constraints
- **Kind checking**: Ensures well-formed types at the kind level

### Compilation Pipeline

1. **Surface Language (Lang)** → Parsed and type-checked functional language
2. **Typed terms** → Explicit type annotations on all subterms
3. **Core (sequent calculus)** → Direct computational interpretation
4. **Cut (future)** → Administrative normal form

## Language Examples

### Data Types (Inductive)

```ocaml
data nat: type where 
  { zero: nat
  ; succ: nat -> nat
  }

data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }
```

### Codata Types (Coinductive)

```ocaml
code stream: type -> type where
  { head: {a} stream(a) -> a
  ; tail: {a} stream(a) -> stream(a)
  }

let ones: stream(nat) = 
  new stream(nat)
  { head{_}(self) => succ(zero)
  ; tail{_}(self) => self
  }
```

### Pattern Matching

```ocaml
let not(b: bool): bool = 
  match b with
  { true => false
  ; false => true
  }
```

### Polymorphic Functions

```ocaml
let identity{a}(x: a): a = x

let map{a}{b}(f: a -> b, xs: list(a)): list(b) =
  match xs with
  { nil{_} => nil{b}
  ; cons{_}(x)(rest) => cons{b}(f(x))(map{a}{b}(f)(rest))
  }
```

## Sequent Calculus Representation

The Core intermediate language uses explicit sequent calculus notation:

- **Producers** (p): Terms that can be cut against consumers
  - Variables: `x`
  - Mu-abstractions: `μα.⟨p | c⟩`
  - Constructors: `ctor(p₁, ..., pₙ)`
  - Cocase: `new { dtor₁(...) => s₁; ...; dtorₙ(...) => sₙ }`

- **Consumers** (c): Contexts expecting a producer
  - Covariables: `α`
  - Mu-tilde abstractions: `μ̃x.⟨p | c⟩`
  - Destructors: `dtor(c₁, ..., cₙ)`
  - Case: `case { ctor₁(...) => s₁; ...; ctorₙ(...) => sₙ }`

- **Statements** (s): Cuts connecting producers and consumers
  - Cut: `⟨p | c⟩`

### Compilation Examples

**Lambda abstraction** compiles to a cocase:
```
fun(x: a) => body  ⟹  new { $app(x)(α) => ⟨body | α⟩ }
```

**Application** compiles to a mu with destructor:
```
f(x)  ⟹  μα.⟨f | $app(α, x)⟩
```

**Let binding** uses mu-tilde:
```
let x = t in u  ⟹  μα.⟨t | μ̃x.⟨u | α⟩⟩
```

## Building and Running

### Prerequisites

- OCaml (≥ 4.14)
- Dune build system
- Menhir parser generator
- Sedlex lexer generator

### Build

```bash
dune build
```

### Run Tests

```bash
# Type checking tests
dune exec sequent

# Conversion pipeline tests
dune exec test_convert

# Parser tests
dune exec test_parser
```

### Interactive Use

```ocaml
(* In OCaml toplevel *)
#require "sequent";;
open Sequent;;

(* Parse and type check *)
let ast = Lang.Parse.parse_defs_string "...";;
let defs = Lang.Syntax.to_definitions ast;;
let typed_defs = Lang.Terms.check_all defs;;

(* Convert to Core *)
let core_producer = Convert.convert (snd (List.hd typed_defs.term_defs)).body;;

(* Pretty print *)
print_endline (Core.Terms.producer_to_string core_producer);;
```

## Project Structure

```
lib/
├── common/          # Shared utilities
│   ├── identifiers.ml    # Names, paths, and scoping
│   └── types.ml          # Type system (kinds, types, GADTs)
├── lang/            # Surface language
│   ├── lexer.ml          # Lexical analysis (sedlex)
│   ├── parser.mly        # Syntax (menhir)
│   ├── syntax.ml         # AST → Terms
│   ├── types.ml          # Type definitions
│   └── terms.ml          # Type checker
├── core/            # Sequent calculus IR
│   └── terms.ml          # Core language definitions
├── cut/             # Cut IR (future)
│   └── terms.ml
└── convert.ml       # Lang → Core conversion

bin/
├── main.ml          # Type checking demo
├── test_parser.ml   # Parser tests
└── test_convert.ml  # Full pipeline tests
```

## Implementation Highlights

### Bidirectional Type Checking

The type checker uses a bidirectional approach:
- **Inference mode** (`infer_typ`): Synthesizes types for terms
- **Checking mode** (`check_typ`): Verifies terms against expected types
- Returns **typed terms** with explicit type annotations

### Type Conversion

The `Lang.Types.Convert` module translates surface types to Core types:
- Functions (`a -> b`) → Codata with `$app` destructor
- Forall (`{a: k} t`) → Codata with `$inst` destructor
- Data types → Data types (structural preservation)
- Codata types → Codata types (sources split: self + args + continuation)

### Pretty Printing

Core terms are printed using proper mathematical notation:
- Greek letters: `μ` (mu), `μ̃` (mu-tilde)
- Angle brackets: `⟨` and `⟩`
- Automatic indentation for nested structures

## Theoretical Background

This compiler is based on:
- [Grokking the sequent calculus](https://arxiv.org/pdf/2406.14719) 
- [Compiling classical sequent calculus to stock hardware](https://se.cs.uni-tuebingen.de/publications/schuster25compiling.pdf)
- [Compiling with classical connectives](https://arxiv.org/pdf/1907.13227)
- [Sequent calculus as a compiler intermediate language](https://pauldownen.com/publications/scfp_ext.pdf)

## Future Work

- [ ] Cut elimination and normalization
- [ ] Cut IR with administrative normal form
- [ ] Code generation
- [ ] Optimization passes
- [ ] Module system

## License

[To be determined]
