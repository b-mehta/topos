import category_theory.monad
/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

/-! # Kleisli category on a monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)`. It also defines the Kleisli adjunction which gives rise to `(T, η_ T, μ_ T)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/
namespace category_theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def kleisli (T : C ⥤ C) [monad.{v} T] := C

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance kleisli.category (T : C ⥤ C) [monad.{v} T] : category (kleisli T) :=
{ hom  := λ (X Y : C), X ⟶ T.obj Y,
  id   := λ X, (η_ T).app X,
  comp := λ X Y Z f g, f ≫ T.map g ≫ (μ_ T).app Z,

  id_comp' := λ X Y f, by simp [←category.assoc, ←nat_trans.naturality (η_ T) f, monad.left_unit'],
  comp_id' := λ X Y f, by simp only [category.comp_id, monad.right_unit ],
  assoc'   := λ W X Y Z f g h, begin
    simp only [functor.map_comp, category.assoc],
    congr' 2, rw monad.assoc T Z,
    slice_rhs 1 2 { erw [nat_trans.naturality (μ_ T) h] },
    simp only [category.assoc],
  end }

namespace kleisli

variables (T : C ⥤ C) [monad.{v} T]

namespace adjunction

@[simps] def F_T : C ⥤ kleisli T :=
{ obj       := λ X, X,
  map       := λ X Y f, by dunfold has_hom.hom; exact f ≫ (η_ T).app Y,
  map_id'   := λ X, by simpa only [category.id_comp],
  map_comp' := λ X Y Z f g, begin
    dunfold category_struct.comp, dsimp,
    simpa only [monad.right_unit, category.comp_id,
                 functor.map_comp, category.assoc,
                 ←nat_trans.naturality (η_ T) g] end }

@[simps] def U_T : kleisli T ⥤ C :=
{ obj       := λ X, T.obj X,
  map       := λ X Y f, T.map f ≫ (μ_ T).app Y,
  map_id'   := λ X, by simp only [category_struct.id, monad.right_unit],
  map_comp' := λ X Y Z f g, begin
    dunfold category_struct.comp, dsimp,
    simp only [monad.assoc T Z, functor.map_comp, category.assoc],
    congr' 1,
    slice_lhs 1 2 { erw [nat_trans.naturality (μ_ T) g] },
    simp only [category.assoc]
  end }

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : F_T T ⊣ U_T T :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.refl _,
  hom_equiv_naturality_left_symm' := λ X Y Z f g, begin
    simp, dunfold category_struct.comp, dsimp,
    slice_rhs 2 3 { rw [←nat_trans.naturality (η_ T) g] },
    slice_rhs 3 4 { erw [monad.left_unit T] },
    dsimp, simp only [category.comp_id]
  end,
  hom_equiv_naturality_right' := λ X Y Z f g, rfl }

end adjunction
end kleisli
end category_theory
