/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.types
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
structure classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) :=
(k : U ⟶ Ω₀)
(commutes : k ≫ true = f ≫ χ)
(forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
restate_axiom classifying.forms_pullback'

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

variable {C}
lemma mono_id (A : C) : @mono _ 𝒞 _ _ (𝟙 A) := ⟨λ _ _ _ w, by simp at w; exact w⟩

variables [has_subobject_classifier.{v} C]

-- convenience defs
@[reducible]
def subobj.Ω : C :=
@has_subobject_classifier.Ω _ 𝒞 _
@[reducible]
def subobj.Ω₀ : C :=
@has_subobject_classifier.Ω₀ _ 𝒞 _
@[reducible]
def subobj.truth : subobj.Ω₀ ⟶ subobj.Ω :=
@has_subobject_classifier.truth _ 𝒞 _
@[reducible]
instance subobj.truth_mono : mono subobj.truth :=
@has_subobject_classifier.truth_mono' _ 𝒞 _
def subobj.classifier_of {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : X ⟶ subobj.Ω :=
has_subobject_classifier.classifier_of f
def subobj.classifies {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : classifying subobj.truth f (subobj.classifier_of f) :=
has_subobject_classifier.classifies' f
def subobj.square.k {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] : U ⟶ subobj.Ω₀ :=
(subobj.classifies f).k
def subobj.square.commutes {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] :
  subobj.square.k f ≫ subobj.truth = f ≫ subobj.classifier_of f :=
(subobj.classifies f).commutes
def subobj.square.is_pullback {U X : C} (f : U ⟶ X) [@mono C 𝒞 _ _ f] :
  is_limit (pullback_cone.mk _ _ (subobj.square.commutes f)) :=
(subobj.classifies f).forms_pullback
restate_axiom has_subobject_classifier.uniquely'

-- subobject classifier => there is a terminal object.
-- TODO: make a lemma saying subobj.Ω₀ = ⊤_C
-- NB: together with the commented out instance at the top and the instance below that, this shows
-- that every category with a subobj classifier and pullbacks has binary products and equalizers
-- It's a todo in mathlib to show binary products implies finite products, and we have
-- in mathlib and these together imply finite limits exist.
-- So when we define (elem) toposes, we only need assume pullbacks and subobj classifier
-- and not all finite limits (but of course cartesian closed is still necessary and such)
instance terminal_of_subobj : @has_terminal C 𝒞 :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := subobj.Ω₀,
        π := {app := λ p, pempty.elim p}},
      is_limit :=
      { lift := λ s, subobj.square.k (𝟙 s.X),
        fac' := λ _ j, j.elim,
        uniq' := λ s m J,
        begin
          clear J,
          rw ← cancel_mono subobj.truth,
          rw subobj.square.commutes,
          rw id_comp,
          apply has_subobject_classifier.uniquely (𝟙 s.X),
          refine {k := m, commutes := _, forms_pullback' := _},
          rw id_comp,
          refine ⟨λ c, c.π.app walking_cospan.right, λ c, _, λ c, _⟩,
          apply pi_app_left (pullback_cone.mk m (𝟙 s.X) _) c,
          rw ← cancel_mono subobj.truth,
          rw assoc, rw pullback_cone.condition c,
          refl,
          apply_instance,
          erw comp_id,
          intros g₂ j, specialize j walking_cospan.right, erw comp_id at j,
          exact j, apply_instance
        end } } }
}

variable (C)
lemma terminal_obj : terminal C = subobj.Ω₀ := rfl

variable {C}
instance unique_to_Ω₀ (P : C) : unique (P ⟶ subobj.Ω₀) :=
limits.unique_to_terminal P

-- TODO: really, we should prove that subobj.truth is an equalizer, and that
-- the pullback of an equalizer is an equalizer (and every mono is a pullback of truth)
def mono_is_equalizer {A B : C} (m : A ⟶ B) [@mono C 𝒞 _ _ m] :
  is_limit (fork.of_ι m (begin rw ← subobj.square.commutes m, rw ← assoc, congr' 1 end) : fork (subobj.classifier_of m) (terminal.from B ≫ subobj.truth)) :=
{ lift := λ s, (subobj.square.is_pullback m).lift (pullback_cone.mk (terminal.from s.X) (fork.ι s) (begin erw fork.condition s, rw ← assoc, congr' 1 end)),
  fac' := λ s,
    begin
      intro j, cases j,
        simp, erw (subobj.square.is_pullback m).fac _ walking_cospan.right, refl,
      simp, rw ← assoc, erw (subobj.square.is_pullback m).fac _ walking_cospan.right,
      rw ← s.w walking_parallel_pair_hom.left, refl
    end,
  uniq' := λ s n J,
  begin
    apply pullback_cone.hom_ext (subobj.square.is_pullback m), apply subsingleton.elim,
    erw (subobj.square.is_pullback m).fac, erw J walking_parallel_pair.zero, refl,
  end
}

def balanced {A B : C} (f : A ⟶ B) [ef : @epi C 𝒞 _ _ f] [mf : mono f] : is_iso f :=
@epi_limit_cone_parallel_pair_is_iso _ _ _ _ _ _ _ (mono_is_equalizer f) ef