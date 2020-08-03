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
import category_theory.currying
import tactic
import adjunction

universes v v₂ v₃ u u₂ u₃

namespace category_theory

open category_theory category_theory.category

variables {C : Type u} [category.{v} C]
variables {D : Type u₂} [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]

def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)

variables (C)

def skeletal : Prop := ∀ (X Y : C), (X ≅ Y) → X = Y

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

instance skel_subsingleton {X Y : skel C} : subsingleton (X ⟶ Y) :=
⟨by { rintros ⟨⟨f₁⟩⟩ ⟨⟨f₂⟩⟩, refl }⟩

instance skel_iso_subsingleton {X Y : skel C} : subsingleton (X ≅ Y) :=
⟨by { rintros i₁ i₂, ext1, apply subsingleton.elim }⟩

def skel_quotient : C ⥤ skel C :=
{ obj := quotient.mk,
  map := λ X Y f, ⟨⟨⟨f⟩⟩⟩ }

variables {C}

@[simps]
def skel_map (F : C ⥤ D) : skel C ⥤ skel D :=
{ obj :=
  begin
    refine quotient.lift _ _,
    intro x,
    apply quotient.mk (F.obj x),
    rintros x y ⟨k⟩,
    apply quotient.sound,
    refine ⟨_⟩,
    apply F.map_iso k,
  end,
  map :=
  begin
    refine quotient.rec _ _,
    { intro x,
      refine quotient.rec _ _,
      { intros y k,
        refine ⟨⟨_⟩⟩,
        rcases k with ⟨⟨⟨k⟩⟩⟩,
        refine ⟨F.map k⟩ },
      { intros y z h,
        apply subsingleton.elim } },
    { intros x y h,
      apply subsingleton.elim }
  end }

lemma skel_quotient_map (F : C ⥤ D) : skel_quotient C ⋙ skel_map F = F ⋙ skel_quotient D :=
rfl

def skel_map_comp (F : C ⥤ D) (G : D ⥤ E) : skel_map (F ⋙ G) ≅ skel_map F ⋙ skel_map G :=
nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

def skel_map_id : skel_map (𝟭 C) ≅ 𝟭 _ :=
nat_iso.of_components (λ X, quotient.rec_on_subsingleton X (λ x, iso.refl _)) (by tidy)

def skel_map_func {F₁ F₂ : C ⥤ D} (k : F₁ ⟶ F₂) : skel_map F₁ ⟶ skel_map F₂ :=
{ app := λ X, quotient.rec_on_subsingleton X (λ x, ⟨⟨⟨k.app x⟩⟩⟩) }

def skel_map_iso {F₁ F₂ : C ⥤ D} (h : F₁ ≅ F₂) : skel_map F₁ ≅ skel_map F₂ :=
{ hom := skel_map_func h.hom, inv := skel_map_func h.inv }

variables [∀ X Y : C, subsingleton (X ⟶ Y)]

def iso_of_both_ways {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
{ hom := f, inv := g }

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

lemma skel_is_skel : skeletal (skel C) :=
begin
  intros X Y,
  apply quotient.induction_on₂ X Y,
  rintros _ _ ⟨⟨⟨⟨f⟩⟩⟩, ⟨⟨⟨g⟩⟩⟩, _, _⟩,
  apply quotient.sound,
  apply equiv_of_both_ways f g,
end

def skel_map₂ (F : C ⥤ D ⥤ E) : skel C ⥤ skel D ⥤ skel E :=
category_theory.curry_obj
{ obj :=
  begin
    rintro ⟨x₁, x₂⟩,
    refine quotient.map₂ _ _ x₁ x₂,
    intros c d, apply (F.obj c).obj d,
    rintros c₁ c₂ ⟨hc⟩ d₁ d₂ ⟨hd⟩,
    refine ⟨(F.map_iso hc).app d₁ ≪≫ (F.obj c₂).map_iso hd⟩,
  end,
  map :=
  begin
    rintros ⟨X₁,Y₁⟩,
    rintros ⟨X₂,Y₂⟩,
    refine quotient.rec_on_subsingleton X₁ _,
    refine quotient.rec_on_subsingleton Y₁ _,
    refine quotient.rec_on_subsingleton X₂ _,
    refine quotient.rec_on_subsingleton Y₂ _,
    rintros y₂ x₂ y₁ x₁ ⟨⟨⟨hx⟩⟩, ⟨⟨hy⟩⟩⟩,
    dsimp at hx hy,
    refine ⟨⟨_⟩⟩,
    cases hx, cases hy,
    exact ⟨(F.map hx).app y₁ ≫ (F.obj x₂).map hy⟩,
  end }

def skel_map_eq {F₁ F₂ : C ⥤ D} (h : F₁ ≅ F₂) : skel_map F₁ = skel_map F₂ :=
begin
  apply functor.ext (quotient.ind _) _,
  { intro x,
    apply quotient.sound,
    refine ⟨h.app x⟩ },
  { tidy },
end

end category_theory