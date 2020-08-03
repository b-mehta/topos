/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.shapes.regular_mono
import category_theory.epi_mono
import sub

/-!
# Subobject classifiers

Define a subobject classifier, show that it implies there's a terminal object,
show that if there is a subobject classifier then every mono is regular.
-/
universes v u v₂ u₂

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C]

/-- Define what it means for χ to classify the mono f. -/
abbreviation classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := has_pullback_top f χ truth

instance subsingleton_classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) [mono truth] (f : U ⟶ X) (χ : X ⟶ Ω) :
  subsingleton (classifying truth f χ) :=
⟨by { intros P Q, cases P, cases Q, congr, rw [← cancel_mono truth, P_comm, Q_comm] }⟩

/--
`is_subobject_classifier truth` holds if the morphism `truth : Ω₀ ⟶ Ω` is a subobject classifier,
i.e. that for any monomorphism `U ⟶ X`, there is a unique morphism `X ⟶ Ω` forming a pullback
square.
Note we do not require `truth` to be a monomorphism here, nor that `Ω₀` is terminal.
-/
structure is_subobject_classifier {Ω Ω₀ : C} (truth : Ω₀ ⟶ Ω) :=
(classifier_of : ∀ {U X} (f : U ⟶ X) [mono.{v} f], X ⟶ Ω)
(classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
(uniquely' : ∀ {U X} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω), classifying truth f χ₁ → classifier_of f = χ₁)

variable (C)

/--
A category has a subobject classifier if there is a monomorphism `truth` which is a
subobject classifier.
We do not require `Ω₀` to be terminal, nor do we assume the existence of any limits.
-/
class has_subobject_classifier :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
[truth_mono : mono.{v} truth]
(is_subobj_classifier : is_subobject_classifier truth)

variables [has_subobject_classifier.{v} C]

/-! Convenience interface to the `has_subobject_classifier` class. -/
namespace classifier

/-- Convenience notation for the classifier target given the typeclass `has_subobject_classifier`. -/
def Ω : C := has_subobject_classifier.Ω.{v}
/-- Convenience notation for the classifier source given the typeclass `has_subobject_classifier`. -/
def Ω₀ : C := has_subobject_classifier.Ω₀.{v}
/-- Convenience notation for the classifier given the typeclass `has_subobject_classifier`. -/
def truth : Ω₀ C ⟶ Ω C := has_subobject_classifier.truth
/-- From the typeclass `has_subobject_classifier`, show that the classifier `truth` is a monomorphism. -/
instance truth_mono : mono (truth C) := has_subobject_classifier.truth_mono
/-- The subobject classifier given by `has_subobject_classifier` is actually a classifier. -/
def subobj_classifier_is_subobj_classifier : is_subobject_classifier (truth C) := has_subobject_classifier.is_subobj_classifier

variable {C}
def classifier_of {U X : C} (f : U ⟶ X) [mono f] : X ⟶ Ω C :=
(subobj_classifier_is_subobj_classifier C).classifier_of f
def classifies {U X : C} (f : U ⟶ X) [mono f] : classifying (truth C) f (classifier_of f) :=
(subobj_classifier_is_subobj_classifier C).classifies' f
lemma uniquely {U X : C} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω C) (hχ : classifying (truth C) f χ₁) : classifier_of f = χ₁ :=
(subobj_classifier_is_subobj_classifier C).uniquely' f χ₁ hχ

end classifier

open classifier

-- Usually we would assume C has finite limits, and Ω₀ C might not be equal to it.
instance unique_to_Ω₀ (P : C) : unique (P ⟶ Ω₀ C) :=
{ default := (classifies (𝟙 _)).top,
  uniq := λ a,
  begin
    rw [← cancel_mono (truth C), (classifies (𝟙 _)).comm, id_comp, uniquely],
    apply left_iso_has_pullback_top a (𝟙 P) (truth C) _ (id_comp _).symm,
  end }

instance truth_is_split : split_mono (truth C) :=
{ retraction := default _ }

variable {C}

/-- In a category with a subobject classifier, any mono is regular. -/
def mono_is_regular {A B : C} (m : A ⟶ B) [mono m] : regular_mono m :=
regular_of_is_pullback_snd_of_regular _ (classifies m).is_pb

/--
`factors_through f g` is usually a `Prop`, but if `g` is a mono, it's a regular mono so we can
lift it to data.
-/
def raised_factors {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (h : factors_through f g) [mono g] : {k // k ≫ g = f} :=
begin
  haveI := mono_is_regular g,
  refine regular_mono.lift' _ _ _,
  casesI h,
  have : h.left ≫ g = f := over.w h,
  rw [← this, assoc, assoc, regular_mono.w],
end

/-- A category with a subobject classifier is balanced. -/
-- Making this an instance screws with resolution (unsurprisingly).
def balanced {A B : C} (f : A ⟶ B) [ef : epi f] [mono f] : is_iso f :=
@is_iso_limit_cone_parallel_pair_of_epi _ _ _ _ _ _ _ (mono_is_regular f).is_limit ef

/--
If the source of a faithful functor has a subobject classifier, the functor reflects
isomorphisms. This holds for any balanced category.
-/
def reflects_isos (D : Type u₂) [category.{v₂} D] (F : C ⥤ D) [faithful F] : reflects_isomorphisms F :=
⟨λ A B f i, by exactI
begin
  haveI : epi f := faithful_reflects_epi F (by apply_instance),
  haveI : mono f := faithful_reflects_mono F (by apply_instance),
  apply balanced
end⟩
