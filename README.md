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
- Reflexive monadicity theorem
- (Internal) Beck-Chevalley and Pare's theorem
- Definition of a topos
- Every topos is finitely cocomplete
- Local cartesian closure of toposes and Fundamental Theorem of Topos Theory
- Lawvere-Tierney topologies and sheaves
- Sheafification

## What's coming soon?
- Proof that category of coalgebras for a comonad form a topos
- Logical functors
- Proof that Lawvere-Tierney topologies generalise Grothendieck topologies
- Logic internal to a topos
- Natural number objects

## What might be coming?
- Geometric morphisms
- Filter/quotient construction on a topos
- ETCS
- The construction of the Cohen topos to show ZF doesn't prove CH
- The construction of a topos to show ZF doesn't prove AC
- A topos in which every function R -> R is continuous
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
leanproject get-mathlib-cache
leanpkg build
```
