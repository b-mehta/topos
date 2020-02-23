/- Author: E.W.Ayers
   Skeleton category.
   This should probably live in full_subcategory.lean
   -/
import .pullbacks
import category_theory.full_subcategory

namespace category_theory
universes u v

variables {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} {i : X ≅ Y}
include 𝒞
def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)
lemma are_iso.refl : are_iso X X := ⟨iso.refl X⟩
lemma are_iso.symm : are_iso X Y → are_iso Y X
| ⟨i⟩ := ⟨i.symm⟩
lemma are_iso.trans : are_iso X Y → are_iso Y Z → are_iso X Z
| ⟨a⟩ ⟨b⟩ := ⟨iso.trans a b⟩

variable (C)

def skeleton.setoid : setoid C :=
{ r := are_iso,
  iseqv :=⟨λ _, are_iso.refl, λ _ _, are_iso.symm, λ _ _ _, are_iso.trans⟩
}

local attribute [instance] skeleton.setoid

def skeleton_q := quotient (skeleton.setoid C)
variable {C}
def skeleton_q.mk (X : C) : skeleton_q C := ⟦X⟧

structure is_skeleton (D : set C) : Prop :=
(skel_prop : ∀ {X Y} (hx : X ∈ D) (hy : Y ∈ D), (X ≅ Y) → X = Y )
(ess_surj : ∀ (X : C), ∃ {Y:C}, Y ∈ D ∧ nonempty (X ≅ Y))

instance {D : set C} : category { X : C // X ∈ D } := by apply_instance


variable (C)
lemma skeleton_exists : ∃ (D : set C), @is_skeleton C 𝒞 D :=
begin
  let D : set C := {X : C | ∃ XX : quotient (skeleton.setoid C), quotient.out XX = X},
  refine ⟨D,_,_⟩,
  { rintros X Y ⟨XX,rfl⟩ ⟨YY,rfl⟩ i,
    congr,
    induction XX,
    induction YY,
    apply quotient.sound',
    have h1, refine (@quotient.mk_out C (skeleton.setoid C) XX), cases h1,
    have h2, refine (@quotient.mk_out C (skeleton.setoid C) YY), cases h2,
    refine ⟨calc XX ≅ _ : h1.symm ... ≅ _ : i ... ≅ YY : h2⟩,
    refl, refl},
  { rintros X,
    refine ⟨quotient.out ⟦X⟧,⟨⟦X⟧,rfl⟩,are_iso.symm (@quotient.mk_out C (skeleton.setoid C) X)⟩}
end

def skeleton : Type u := {X : C // X ∈ classical.some (skeleton_exists C)}

variable {C}

instance skeleton_category : category.{v} (skeleton C) := show category.{v} {X : C // _}, by apply_instance

end category_theory