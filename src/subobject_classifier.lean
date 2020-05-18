/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.limits.shapes.regular_mono
import category_theory.epi_mono
import pullbacks

/-!
# Subobject classifiers

Define a subobject classifier, show that it implies there's a terminal object,
show that if there is a subobject classifier then every mono is regular.
-/
universes v u

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- Define what it means for χ to classify the mono f.
abbreviation classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := has_pullback_top f χ true
-- structure classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) :=
-- (k : U ⟶ Ω₀)
-- (commutes : k ≫ true = f ≫ χ)
-- (forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
-- restate_axiom classifying.forms_pullback'

variable (C)
-- A subobject classifier is a mono which classifies every mono uniquely
class has_subobject_classifier :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
(truth_mono' : @mono C 𝒞 _ _ truth)
(classifier_of : ∀ {U X} (f : U ⟶ X) [@mono C 𝒞 _ _ f], X ⟶ Ω)
(classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
(uniquely' : ∀ {U X} (f : U ⟶ X) [@mono C 𝒞 _ _ f] (χ₁ : X ⟶ Ω),
            classifying truth f χ₁ → χ₁ = classifier_of f)

def fork.is_limit.mk' {X Y : C} {f g : X ⟶ Y} (t : fork f g)
  (create : Π (s : fork f g), {l : s.X ⟶ t.X // l ≫ t.ι = s.ι ∧ ∀ {m : s.X ⟶ t.X}, m ≫ t.ι = s.ι → m = l}) :
is_limit t :=
fork.is_limit.mk t (λ s, (create s).1) (λ s, (create s).2.1) (λ s m w, (create s).2.2 (w walking_parallel_pair.zero))

-- variable {C}
-- lemma mono_id (A : C) : @mono _ 𝒞 _ _ (𝟙 A) := ⟨λ _ _ _ w, by simp at w; exact w⟩

variables [has_subobject_classifier.{v} C]

namespace subobj

-- convenience defs
@[reducible]
def Ω : C :=
@has_subobject_classifier.Ω _ 𝒞 _
@[reducible]
def Ω₀ : C :=
@has_subobject_classifier.Ω₀ _ 𝒞 _
@[reducible]
def truth : Ω₀ C ⟶ Ω C :=
@has_subobject_classifier.truth _ 𝒞 _
@[priority 10]
instance subobj.truth_mono : mono (truth C) :=
@has_subobject_classifier.truth_mono' _ 𝒞 _

variable {C}
def classifier_of {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : X ⟶ Ω C :=
has_subobject_classifier.classifier_of f
def classifies {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : classifying (truth C) f (classifier_of f) :=
has_subobject_classifier.classifies' f
def square.k {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : U ⟶ Ω₀ C :=
(classifies f).top
def square.commutes {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] :
  square.k f ≫ truth C = f ≫ classifier_of f :=
(subobj.classifies f).comm
def square.is_pullback {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] :
  is_limit (pullback_cone.mk _ _ (square.commutes f)) :=
(classifies f).is_pb
restate_axiom has_subobject_classifier.uniquely'

end subobj

open subobj

variable {C}
-- Usually we would assume C has finite limits, and Ω₀ C might not be equal to it.
instance unique_to_Ω₀ (P : C) : unique (P ⟶ Ω₀ C) :=
{ default := square.k (𝟙 _),
  uniq := λ a,
  begin
    rw ← cancel_mono (truth C),
    rw square.commutes (𝟙 _),
    rw id_comp,
    apply has_subobject_classifier.uniquely,
    refine ⟨a, (id_comp _).symm, pullback_square_iso _ _ _ _ _⟩,
  end }

variable (C)
instance truth_is_split : split_mono (subobj.truth C) :=
{ retraction := subobj.square.k (𝟙 _),
  id' := subsingleton.elim _ _ }

variable {C}
def regular_of_regular_pullback {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : regular_mono h]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk _ _ comm)) : regular_mono g :=
{ Z := hr.Z,
  left := k ≫ hr.left,
  right := k ≫ hr.right,
  w := by rw [← reassoc_of comm, ← reassoc_of comm, hr.w],
  is_limit :=
  begin
    apply fork.is_limit.mk' _ _,
    intro s,
    have l₁ : (fork.ι s ≫ k) ≫ regular_mono.left = (fork.ι s ≫ k) ≫ regular_mono.right,
      rw [assoc, s.condition, assoc],
    let l₂ : fork hr.left hr.right := fork.of_ι (s.ι ≫ k) l₁,
    let p₂ : pullback_cone h k := pullback_cone.mk (hr.is_limit.lift l₂) s.ι (hr.is_limit.fac _ walking_parallel_pair.zero),
    refine ⟨t.lift p₂, t.fac p₂ walking_cospan.right, _⟩,
    intros m w,
    have z : m ≫ g = t.lift p₂ ≫ g,
      erw w, exact (t.fac p₂ walking_cospan.right).symm,
    apply t.hom_ext,
    apply (pullback_cone.mk f g comm).equalizer_ext,
    erw [← cancel_mono h, assoc, assoc, comm],
    rw reassoc_of z,
    exact z,
  end }

def mono_is_regular {A B : C} (m : A ⟶ B) [mono m] : regular_mono m :=
regular_of_regular_pullback _ (square.is_pullback m)

def balanced {A B : C} (f : A ⟶ B) [ef : epi f] [mono f] : is_iso f :=
@is_iso_limit_cone_parallel_pair_of_epi _ _ _ _ _ _ _ (mono_is_regular f).is_limit ef
