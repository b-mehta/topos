![.github/workflows/main.yml](https://github.com/b-mehta/topos/workflows/.github/workflows/main.yml/badge.svg)

# Topos theory for Lean

This is a WIP project to define some topos theory within the Lean theorem prover.

## What's here?
- Cartesian closed categories
- Sieves and grothendieck topologies including the open set topology
- (Trunc) construction of finite products from binary products and terminal
- Locally cartesian closed categories and epi-mono factorisations
- Many lemmas about pullbacks (for instance the pasting lemma)
- Skeleton of a category (assuming choice)
- Subobject category
- Subobject classifier
- Power objects

## What's coming soon?
- Definition of a topos
- Proof that category of coalgebras for a comonad form a topos
- Every topos is locally cartesian closed, Fundamental theorem of Topos Theory
- (Internal) Beck-Chevalley and Pare's theorem
- Beck's monadicity theorem [unless someone else does it sooner]
- Every topos is finitely cocomplete
- Lawvere-Tierney topologies, sheaves
- Logical functors

## What might be coming?
- Geometric morphisms
- Filter/quotient construction on a topos
- The construction of the Cohen topos to show ZF doesn't prove CH
- The construction of a topos to show ZF doesn't prove AC
- A topos in which every function R -> R is continuous
- Proof that Lawvere-Tierney topologies generalise Grothendieck topologies
- Logic internal to a topos
- Giraud's theorem
- Classifying toposes

## Build Instructions

EITHER:
[Install elan and update-mathlib](https://github.com/leanprover-community/mathlib/tree/master/docs/install).

OR:
If you have docker, spin up an instance of the `edayers/lean` image (or build your own using the provided Dockerfile).

FINALLY:
run
``` sh
# topos/
leanpkg configure
update-mathlib
leanpkg build
```
