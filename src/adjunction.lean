/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.equivalence
import category_theory.adjunction

namespace category_theory
open category

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

-- Some basic adjunction properties
@[reducible]
def equiv_homset_left_of_nat_iso {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F G : C ⥤ D} (iso : F ≅ G) {X : C} {Y : D} :
  (F.obj X ⟶ Y) ≃ (G.obj X ⟶ Y) :=
⟨λ f, (iso.app _).inv ≫ f, λ g, (iso.app _).hom ≫ g, λ f, begin dsimp, rw ← assoc, simp end, λ g, begin dsimp, rw ← assoc, simp end⟩

@[reducible]
def equiv_homset_right_of_nat_iso {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {G H : D ⥤ C} (iso : G ≅ H) {X : C} {Y : D} :
  (X ⟶ G.obj Y) ≃ (X ⟶ H.obj Y) :=
⟨λ f, f ≫ (iso.app _).hom, λ g, g ≫ (iso.app _).inv, λ f, by simp, λ g, by simp⟩

def adjunction_of_nat_iso_left {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) :
  G ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.trans (equiv_homset_left_of_nat_iso iso.symm) (adj.hom_equiv X Y),
  hom_equiv_naturality_left_symm' := begin intros, simp, rw ← assoc, rw ← assoc, rw ← assoc, rw ← assoc, congr' 2, simp end,
  hom_equiv_naturality_right' := λ X Y Y' f g, by simp}

def adjunction_of_nat_iso_right {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) :
  F ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.trans (adj.hom_equiv X Y) (equiv_homset_right_of_nat_iso iso),
  hom_equiv_naturality_left_symm' := λ X X' Y f g, by simp,
  hom_equiv_naturality_right' := λ X Y Y' f g, begin simp, congr' 1, rw ← assoc, rw ← assoc, congr' 1, rw [nat_trans.naturality] end}

end category_theory