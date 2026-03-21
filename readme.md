# Compiling with Sequent Calculus

A compiler for a functional ML-like language with generalized algebraic data types (GADTs) and codata types, higher kinded types, parametric higher rank polymorphism and implicit data kinds, compiled through a series of intermediate representations based on sequent calculus.

## Key Features

### Surface Language

- **ML-style syntax** with type inference and bidirectional type checking
- **Generalized algebraic data types (GADTs)** with pattern matching
- **Generalized codata types** (observations/destructors) with copattern matching
- **Polymorphism**, including higher rank
- **Higher-kinded types** for type-level abstraction
- **Data kinds** similar to Haskell's DataKind extension
- **Destinations** for functional style destination-passing
- **Linear types**


### Compilation Pipeline

1. **Surface Language (Lang)**
2. **Melcore** Desugared and fully type annotated 
3. **Core** Polarized sequent calculus
4. **Focused** Normalized ("focused") representation
5. **Axil** Linearized and monomorphized representation
6. **ASM** Currently only AArch64/Arm64

## Language Examples

This example shows data and codata declarations:
```
data option: type -> type where
  { none: {a} option(a)
  ; some: {a} a -> option(a)
  }

code stream: type -> type where
  { state: {a} stream(a) -> a
  ; next: {a} stream(a) -> option(stream(a))
  }

let ints_from(i: int): stream(int) =
  new { state => i
      ; next => some{stream(int)}(ints_from(i + 1))
      }
```
Here is an example making use of GADT and data kind features:
```
data nat: type where
  { zero: nat
  ; succ: nat -> nat
  }

data single_nat: nat -> type where
  { single_zero: single_nat(zero)
  ; single_succ: {n: nat} single_nat(n) -> single_nat(succ(n))
  }

data vec: type -> nat -> type where
  { nil: {a} vec(a)(zero)
  ; cons: {a}{n: nat} a -> vec(a)(n) -> vec(a)(succ(n))
  }

let replicate{a}{n: nat}(x: a)(k: single_nat(n)): vec(a)(n) =
  match k with
  { single_zero => nil{a}
  ; single_succ{m}(k') => cons{a}{m}(x)(replicate{a}{m}(x)(k'))
  }

let length{a}{n: nat}(v: vec(a)(n)): single_nat(n) =
  match v with
  { nil{_} => single_zero
  ; cons{_}{m}(x)(xs) => single_succ{m}(length{a}{m}(xs))
  }
```
This example shows destinations in action, defining an optimized (tail-recursive, O(1) memory) list map function. The destination types are examples of linear types.
```
data list: type -> type where
  { nil: {a} list(a)
  ; cons: {a} a -> list(a) -> list(a)
  }

let map_dsp{a}{b}(f: a -> b)(xs: list(a))(ds: dest(list(b))): unit =
  match xs with
  { nil{_} => fill(ds)(nil{b})
  ; cons{_}(x)(xs) =>
      let (d, ds) = ds @ cons{b} in
      let _ = fill(d)(f(x)) in
      map_dsp{a}{b}(f)(xs)(ds)
  }

let map{a}{b}(f: a -> b)(xs: list(a)): list(b) =
  let init = alloc{list(b)}() in
  let r = update init with { (ds) => map_dsp{a}{b}(f)(xs)(ds) } in
  finalize(r)
```

## Building and Running

### Prerequisites

- OCaml (≥ 4.14)
- Dune build system
- Menhir parser generator
- Sedlex lexer generator
- GNU as and gcc (for compiling .asm to executables)

### Build

```bash
dune build
```

### Run Compiler

```bash
$ dune exec bin/compile.exe -- --link examples/fibonacci.cd examples/fibonacci/fibonacci
$ cd examples/fibonacci
$ sudo chmod +x fibonacci
$ ./fibonacci 1000
817770325994397771
```

### Run Tests

```bash
# Test whole pipeline
$ dune exec test_pipeline
```

## Theoretical Background

This compiler is based on:
- [Grokking the sequent calculus](https://arxiv.org/pdf/2406.14719) 
- [Compiling classical sequent calculus to stock hardware](https://se.cs.uni-tuebingen.de/publications/schuster25compiling.pdf)
- [Compiling with classical connectives](https://arxiv.org/pdf/1907.13227)
- [Sequent calculus as a compiler intermediate language](https://pauldownen.com/publications/scfp_ext.pdf)
- [The simple essence of monomorphization](https://dl.acm.org/doi/epdf/10.1145/3720472)
- [Destination calculus: A Linear 𝜆−Calculus for Purely Functional Memory Writes](https://arxiv.org/pdf/2503.07489)

## Future Work

- [] Primitive strings
- [] Array support
- [] I/O
- [] Module system
- [] Sweeter syntax and inference

## License

[To be determined]

