/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.comma
import pullbacks

universes v u

open category_theory category_theory.category category_theory.limits
namespace category_theory

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section
variables [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

lemma prod_map_comm {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
  limits.prod.map (𝟙 _) f ≫ limits.prod.map g (𝟙 _) = limits.prod.map g (𝟙 _) ≫ limits.prod.map (𝟙 _) f :=
begin
  apply prod.hom_ext, simp, erw id_comp, erw comp_id, simp, erw id_comp, erw comp_id
end

lemma prod_functorial {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  limits.prod.map (f ≫ g) (𝟙 W) = limits.prod.map f (𝟙 W) ≫ limits.prod.map g (𝟙 W) :=
begin
  apply prod.hom_ext,
  simp, simp, dsimp, simp
end
lemma prod_functorial' {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  limits.prod.map (𝟙 W) (f ≫ g) = limits.prod.map (𝟙 W) f ≫ limits.prod.map (𝟙 W) g :=
begin
  apply prod.hom_ext,
  simp, dsimp, simp, simp
end
end

variables [has_binary_products.{v} C] {B : C} [has_binary_products.{v} (over B)]
variables (f g : over B)

@[reducible]
def magic_arrow (f g : over B) :
  (g ⨯ f).left ⟶ g.left ⨯ f.left :=
prod.lift ((limits.prod.fst : g ⨯ f ⟶ g).left) ((limits.prod.snd : g ⨯ f ⟶ f).left)

-- This is an equalizer but we don't really need that
instance magic_mono : mono (magic_arrow f g) :=
begin
  refine ⟨λ Z p q h, _⟩,
  have h₁ := h =≫ limits.prod.fst,
  rw [assoc, assoc, prod.lift_fst] at h₁,
  have h₂ := h =≫ limits.prod.snd,
  rw [assoc, assoc, prod.lift_snd] at h₂,
  have: p ≫ (g ⨯ f).hom = q ≫ (g ⨯ f).hom,
    have: (g ⨯ f).hom = (limits.prod.fst : g ⨯ f ⟶ g).left ≫ g.hom := (over.w (limits.prod.fst : g ⨯ f ⟶ g)).symm,
    rw this,
    apply reassoc_of h₁,
  let Z' : over B := over.mk (q ≫ (g ⨯ f).hom),
  let p' : Z' ⟶ g ⨯ f := over.hom_mk p,
  let q' : Z' ⟶ g ⨯ f := over.hom_mk q,
  suffices: p' = q',
    show p'.left = q'.left,
    rw this,
  apply prod.hom_ext,
  ext1,
  exact h₁,
  ext1,
  exact h₂,
end

def magic_comm (f g h : over B) (k : f ⟶ g) :
  (limits.prod.map k (𝟙 h)).left ≫ magic_arrow h g = magic_arrow h f ≫ limits.prod.map k.left (𝟙 h.left) :=
begin
  apply prod.hom_ext,
  { rw [assoc, prod.lift_fst, ← over.comp_left, limits.prod.map_fst, assoc, limits.prod.map_fst, prod.lift_fst_assoc], refl },
  { rw [assoc, assoc, limits.prod.map_snd, comp_id, prod.lift_snd, ← over.comp_left, limits.prod.map_snd, comp_id, prod.lift_snd] }
end
def magic_pb (f g h : over B) (k : f ⟶ g) :
  is_limit (pullback_cone.mk (limits.prod.map k (𝟙 h)).left (magic_arrow h f) (magic_comm f g h k)) :=
begin
  refine is_limit.mk' _ _,
  intro s,
  have s₁ := pullback_cone.condition s =≫ limits.prod.fst,
    rw [assoc, assoc, prod.lift_fst, limits.prod.map_fst] at s₁,
  have s₂ := pullback_cone.condition s =≫ limits.prod.snd,
    rw [assoc, assoc, prod.lift_snd, limits.prod.map_snd, comp_id] at s₂,
  let sX' : over B := over.mk (pullback_cone.fst s ≫ (g ⨯ h).hom),
  have z : (pullback_cone.snd s ≫ limits.prod.snd) ≫ h.hom = sX'.hom,
    rw ← s₂,
    change (pullback_cone.fst s ≫ _) ≫ h.hom = pullback_cone.fst s ≫ (g ⨯ h).hom,
    rw ← over.w (limits.prod.snd : g ⨯ h ⟶ _),
    rw assoc,
  have z₂ : (pullback_cone.snd s ≫ limits.prod.fst) ≫ f.hom = pullback_cone.fst s ≫ (g ⨯ h).hom,
    rw ← over.w k,
    slice_lhs 1 3 {rw ← s₁},
    rw assoc,
    rw over.w (limits.prod.fst : g ⨯ h ⟶ _),
  let l : sX' ⟶ f := over.hom_mk (pullback_cone.snd s ≫ limits.prod.fst) z₂,
  let t : sX' ⟶ f ⨯ h := prod.lift l (over.hom_mk (pullback_cone.snd s ≫ limits.prod.snd) z),
  have t₁: t.left ≫ (limits.prod.fst : f ⨯ h ⟶ f).left = l.left,
    rw [← over.comp_left, prod.lift_fst],
  have t₂: t.left ≫ (limits.prod.snd : f ⨯ h ⟶ h).left = pullback_cone.snd s ≫ limits.prod.snd,
    rw [← over.comp_left, prod.lift_snd], refl,
  have fac: t.left ≫ magic_arrow h f = pullback_cone.snd s,
    apply prod.hom_ext,
    rw [assoc],
    change t.left ≫ magic_arrow h f ≫ limits.prod.fst = pullback_cone.snd s ≫ limits.prod.fst,
    rw [prod.lift_fst], exact t₁,
    rw ← t₂,
    rw assoc,
    change t.left ≫ magic_arrow h f ≫ limits.prod.snd = _,
    rw prod.lift_snd,
  refine ⟨t.left, _, fac, _⟩,
  rw [← cancel_mono (magic_arrow h g), pullback_cone.condition s, assoc],
  change t.left ≫ (limits.prod.map k (𝟙 h)).left ≫ magic_arrow h g =
    pullback_cone.snd s ≫ limits.prod.map k.left (𝟙 h.left),
  rw [magic_comm, ← fac, assoc],
  intros m m₁ m₂,
  rw ← cancel_mono (magic_arrow h f),
  erw m₂,
  exact fac.symm,
end

end category_theory