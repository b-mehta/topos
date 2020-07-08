/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.opposites
import category_theory.sparse
import category_theory.limits.lattice
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.full_subcategory
import category_theory.limits.shapes.regular_mono
import category_theory.closed.cartesian
import category_theory.limits.shapes.pullbacks
import category_theory.limits.over

universes v u

namespace category_theory

open category_theory category_theory.category

variables {C : Type u} [category.{v} C]

def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)

variables (C)

instance up_to_iso : setoid C :=
{ r := are_iso,
  iseqv :=
  begin
    refine ⟨λ X, ⟨iso.refl _⟩, λ X Y, _, λ X Y Z, _⟩,
    rintro ⟨i⟩,
    refine ⟨i.symm⟩,
    rintro ⟨i⟩ ⟨j⟩,
    refine ⟨i.trans j⟩,
  end }

def skel := quotient (category_theory.up_to_iso C)

instance skel_preorder : preorder (skel C) :=
{ le :=
  begin
    refine quotient.lift₂ (λ X Y, nonempty (X ⟶ Y)) _,
    rintros _ _ _ _ ⟨i₁⟩ ⟨i₂⟩,
    apply propext,
    split,
    rintro ⟨f⟩,
    refine ⟨i₁.inv ≫ f ≫ i₂.hom⟩,
    rintro ⟨g⟩,
    refine ⟨i₁.hom ≫ g ≫ i₂.inv⟩,
  end,
  le_refl :=
  begin
    refine quotient.ind (λ a, _),
    exact ⟨𝟙 _⟩,
  end,
  le_trans :=
  begin
    intros _ _ _,
    apply quotient.induction_on₃ a b c,
    rintros _ _ _ ⟨f⟩ ⟨g⟩,
    refine ⟨f ≫ g⟩,
  end }

variables {C} [∀ X Y : C, subsingleton (X ⟶ Y)]

lemma iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
{ hom := f,
  inv := g }

lemma equiv_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≈ Y :=
⟨iso_of_both_ways f g⟩

instance : partial_order (skel C) :=
{ le_antisymm :=
  begin
    refine quotient.ind₂ _,
    rintros _ _ ⟨f⟩ ⟨g⟩,
    apply quotient.sound,
    apply equiv_of_both_ways f g,
  end,
  ..category_theory.skel_preorder C }

def skel_quotient : C ⥤ skel C :=
{ obj := quotient.mk,
  map := λ X Y f, ⟨⟨⟨f⟩⟩⟩ }

end category_theory