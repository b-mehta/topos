/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import category_theory.epi_mono
import category_theory.limits.shapes.binary_products

/-! # Stuff that should be in mathlib -/
namespace category_theory

universes v₁ u₁
variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

lemma mono_comp_of_mono {X Y Z : C}
  (m : X ⟶ Y) (m' : Y ⟶ Z) (hm : mono m) (hm' : mono m') : mono (m ≫ m') :=
⟨λ Z f g w,
  have f ≫ m = g ≫ m := (cancel_mono m').mp (by simp only [category.assoc]; exact w),
  (cancel_mono m).mp this⟩

lemma epi_comp_of_epi {X Y Z : C}
  (e : X ⟶ Y) (e' : Y ⟶ Z) (he : epi e) (he' : epi e') : epi (e ≫ e') :=
⟨λ Z f g w,
  have e' ≫ f = e' ≫ g := (cancel_epi e).mp (by simp only [category.assoc] at w; exact w),
  (cancel_epi e').mp this⟩

end category_theory
