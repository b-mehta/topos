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

-- Define what it means for χ to classify the mono f.
abbreviation classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) := has_pullback_top f χ truth

instance subsingleton_classifying {Ω Ω₀ U X : C} (truth : Ω₀ ⟶ Ω) [mono truth] (f : U ⟶ X) (χ : X ⟶ Ω) :
  subsingleton (classifying truth f χ) :=
⟨by { intros P Q, cases P, cases Q, congr, rw [← cancel_mono truth, P_comm, Q_comm] }⟩

structure is_subobject_classifier {Ω Ω₀ : C} (truth : Ω₀ ⟶ Ω) :=
(classifier_of : ∀ {U X} (f : U ⟶ X) [mono.{v} f], X ⟶ Ω)
(classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
(uniquely' : ∀ {U X} (f : U ⟶ X) [mono f] (χ₁ : X ⟶ Ω), classifying truth f χ₁ → classifier_of f = χ₁)

variable (C)
class has_subobject_classifier :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
[truth_mono : mono.{v} truth]
(is_subobj_classifier : is_subobject_classifier truth)

def fork.is_limit.mk' {X Y : C} {f g : X ⟶ Y} (t : fork f g)
  (create : Π (s : fork f g), {l : s.X ⟶ t.X // l ≫ t.ι = s.ι ∧ ∀ {m : s.X ⟶ t.X}, m ≫ t.ι = s.ι → m = l}) :
is_limit t :=
fork.is_limit.mk t (λ s, (create s).1) (λ s, (create s).2.1) (λ s m w, (create s).2.2 (w walking_parallel_pair.zero))

namespace classifier

variables [has_subobject_classifier.{v} C]

def Ω : C := has_subobject_classifier.Ω.{v}
def Ω₀ : C := has_subobject_classifier.Ω₀.{v}
def truth : Ω₀ C ⟶ Ω C := has_subobject_classifier.truth
instance truth_mono : mono (truth C) := has_subobject_classifier.truth_mono
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

variable {C}
-- Usually we would assume C has finite limits, and Ω₀ C might not be equal to it.
instance unique_to_Ω₀ [has_subobject_classifier.{v} C] (P : C) : unique (P ⟶ Ω₀ C) :=
{ default := (classifies (𝟙 _)).top,
  uniq := λ a,
  begin
    rw [← cancel_mono (truth C), (classifies (𝟙 _)).comm, id_comp, uniquely],
    apply left_iso_has_pullback_top a (𝟙 P) (truth C) _ (id_comp _).symm,
  end }

variable (C)
instance truth_is_split [has_subobject_classifier.{v} C] : split_mono (truth C) :=
{ retraction := default _ }
variable {C}

def regular_of_is_pullback_of_regular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S} [hr : regular_mono h]
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

instance regular_of_pullback_regular {P Q R : C} (f : P ⟶ R) (g : Q ⟶ R) [has_limit (cospan f g)] [regular_mono f] : regular_mono (pullback.snd : pullback f g ⟶ Q) :=
regular_of_is_pullback_of_regular pullback.condition (cone_is_pullback f g)

variable [has_subobject_classifier.{v} C]
def mono_is_regular {A B : C} (m : A ⟶ B) [mono m] : regular_mono m :=
regular_of_is_pullback_of_regular _ (classifies m).is_pb

def raised_factors {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (h : factors_through f g) [mono g] : {k // k ≫ g = f} :=
by haveI := mono_is_regular g; exact regular_mono.lift' _ _ (by { cases h, simp [← h_h, regular_mono.w] })

def balanced {A B : C} (f : A ⟶ B) [ef : epi f] [mono f] : is_iso f :=
@is_iso_limit_cone_parallel_pair_of_epi _ _ _ _ _ _ _ (mono_is_regular f).is_limit ef

def reflects_isos (D : Type u₂) [category.{v₂} D] (F : C ⥤ D) [faithful F] : reflects_isomorphisms F :=
⟨λ A B f i, by exactI
begin
  haveI : epi f := faithful_reflects_epi F (by apply_instance),
  haveI : mono f := faithful_reflects_mono F (by apply_instance),
  apply balanced
end⟩