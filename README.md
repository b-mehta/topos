![.github/workflows/main.yml](https://github.com/b-mehta/topos/workflows/.github/workflows/main.yml/badge.svg)

# Topos theory for Lean

This is a WIP project to define some topos theory within the Lean theorem prover.

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
