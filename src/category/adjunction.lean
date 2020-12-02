/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.equivalence
import category_theory.adjunction.opposites
import category_theory.yoneda
import category_theory.natural_isomorphism
import category_theory.fully_faithful
import category_theory.conj
import tactic

namespace category_theory
open category

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

def left_adjoint_of_right_adjoint_op {F : C ⥤ D} [h : is_right_adjoint F.op] : is_left_adjoint F :=
{ right := (left_adjoint F.op).unop,
  adj := adjunction.adjoint_unop_of_adjoint_op _ _ (adjunction.of_right_adjoint _) }

end category_theory
