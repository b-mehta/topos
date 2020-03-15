/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.types
import pullbacks

/-!
# Power objects

Define power objects
-/
universes v u

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
variables [has_finite_limits.{v} C]
include 𝒞

structure powerises {A PA epsA B R : C} (memA : epsA ⟶ PA ⨯ A) (m : R ⟶ B ⨯ A) [@mono _ 𝒞 _ _ m] (mhat : B ⟶ PA) :=
(top : R ⟶ epsA)
(commutes : top ≫ memA = m ≫ limits.prod.map mhat (𝟙 A))
(forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
restate_axiom powerises.forms_pullback'

class has_power_object (A : C) :=
(PA epsA : C)
(memA : epsA ⟶ PA ⨯ A)
(mem_mono' : @mono _ 𝒞 _ _ memA)
(hat : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m], B ⟶ PA)
(powerises' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m], powerises memA m (hat m))
(uniquely' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m] (hat' : B ⟶ PA), powerises memA m hat' → hat' = hat m)

variable (C)
class has_power_objects :=
(has_power_object : Π (A : C), has_power_object.{v} A)

variable [has_power_objects.{v} C]

def pow.functor_obj : Cᵒᵖ ⟶ C :=
  λ (X : Cᵒᵖ), (has_power_objects.has_power_object.{v} X.unop).PA