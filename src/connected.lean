/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.equalizers
import category_theory.limits.preserves
import category_theory.limits.over
import category_theory.comma
import to_mathlib

/-!
# Connected category

Define a connected category
-/

universes v₁ v₂ u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

variables (J : Type v₂) [𝒥 : category.{v₁} J]
include 𝒥

/--
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits,
and further that a category has finite connected limits iff it has pullbacks
and equalizers (the latter is not yet done).
-/
class connected extends inhabited J :=
(iso_constant : Π {α : Type u₂} (F : J ⥤ discrete α), F ≅ (functor.const J).obj (F.obj default))

variable {J}
def any_functor_eq_constant [conn : connected.{v₁} J] {α : Type u₂} (F : J ⥤ discrete α) :
  F = (functor.const J).obj (F.obj (default J)) :=
begin
  apply functor.ext _ _,
    intro X,
    have z := conn.iso_constant,
    exact ((z F).hom.app X).down.1,
  intros, apply subsingleton.elim
end

def connected.of_any_functor_const_on_obj [inhabited J] (h : ∀ {α : Type u₂} (F : J ⥤ discrete α), ∀ (B : J), F.obj B = F.obj (default J)) :
  connected.{v₁} J :=
begin
  split,
  intros α F,
  specialize h F,
  apply nat_iso.of_components _ _,
  intro B, apply eq_to_iso (h B),
  intros, apply subsingleton.elim
end

section examples
omit 𝒥
instance cospan_inhabited : inhabited walking_cospan := ⟨walking_cospan.one⟩

def cospan_connected : connected.{v₁} (walking_cospan.{v₁}) :=
begin
  apply connected.of_any_functor_const_on_obj,
  intros,
  cases B,
  exact (F.map walking_cospan.hom.inl).down.1,
  exact (F.map walking_cospan.hom.inr).down.1,
  refl
end

instance parallel_pair_inhabited : inhabited walking_parallel_pair := ⟨walking_parallel_pair.one⟩

def parallel_pair_connected : connected.{v₁} (walking_parallel_pair.{v₁}) :=
begin
  apply connected.of_any_functor_const_on_obj,
  intros,
  cases B,
  exact (F.map walking_parallel_pair_hom.left).down.1,
  refl
end
end examples

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞
@[simps]
def functor_from_nat_trans {X Y : C} (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) : J ⥤ discrete (X ⟶ Y) :=
{ obj := α.app,
  map := λ A B f, eq_to_hom (begin have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm end),
  map_id' := λ A, rfl,
  map_comp' := λ A₁ A₂ A₃ f g, (eq_to_hom_trans _ _).symm
}

def nat_trans_from_connected [conn : connected.{v₁} J] {X Y : C} (j : J) (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  α.app j = (α.app (default J) : X ⟶ Y) :=
@congr_arg _ _ _ _
  (λ t : _ ⥤ _, t.obj j)
  (any_functor_eq_constant (functor_from_nat_trans α))

omit 𝒥 𝒞

local attribute [tidy] tactic.case_bash

@[simps]
def prod_functor [category.{v₂} C] [has_binary_products.{v₂} C] : C ⥤ C ⥤ C :=
{ obj := λ X, { obj := λ Y, X ⨯ Y, map := λ Y Z, limits.prod.map (𝟙 X) },
  map := λ Y Z f, { app := λ T, limits.prod.map f (𝟙 T) }}

@[simps]
def γ₂ [small_category J] [category.{v₂} C] [has_binary_products.{v₂} C] {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

@[simps]
def γ₁ [small_category J] [category.{v₂} C] [has_binary_products.{v₂} C] {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

@[simps]
def forget_cone [category.{v₂} C] [has_binary_products.{v₂} C] [small_category J] {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod_functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ₂ X }

def prod_preserves_connected_limits [𝒞 : category.{v₂} C] [has_binary_products.{v₂} C] [small_category J] [conn : connected.{v₂} J] (X : C) :
  preserves_limits_of_shape J (prod_functor.obj X) :=
{ preserves_limit := λ K,
  { preserves := λ c l,
    { lift := λ s, limits.prod.lift (s.π.app (default _) ≫ limits.prod.fst) (l.lift (forget_cone s)),
      fac' := λ s j,
      begin
        apply prod.hom_ext,
        { rw assoc,
          rw functor.map_cone_π,
          erw limit.map_π,
          erw comp_id,
          rw limit.lift_π,
          exact (@nat_trans_from_connected _ _ _ _ conn _ _ j (s.π ≫ γ₁ X)).symm },
        { have: l.lift (forget_cone s) ≫ c.π.app j = s.π.app j ≫ limits.prod.snd := l.fac (forget_cone s) j,
          rw ← this,
          simp }
      end,
      uniq' := λ s m L,
      begin
        apply prod.hom_ext,
          rw limit.lift_π,
          rw ← L (default J),
          dsimp,
          rw assoc,
          rw limit.map_π,
          erw comp_id,
        rw limit.lift_π,
        apply l.uniq (forget_cone s),
        intro j,
        dsimp,
        rw ← L j,
        simp
      end } } }

#check forget

namespace over

namespace creates

variables [𝒥' : small_category J]
include 𝒥' 𝒞

@[simps]
def nat_trans_in_over {B : C} (F : J ⥤ over B) :
  F ⋙ forget ⟶ (functor.const J).obj B :=
{ app := λ j, (F.obj j).hom }

@[simps]
def raise_cone [conn : connected.{v₂} J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) :
  cone F :=
{ X := @over.mk _ _ B c.X (c.π.app (default J) ≫ (F.obj (default J)).hom),
  π :=
  { app := λ j, over.hom_mk (c.π.app j) (@nat_trans_from_connected _ _ _ _ conn _ _ j (c.π ≫ nat_trans_in_over F)) } }

end creates

def forgetful_creates_connected_limits [small_category J] [conn : connected.{v₂} J] [𝒞 : category.{v₂} C] {B : C} (F : J ⥤ over B) [has_limit.{v₂} (F ⋙ forget)] :
  has_limit.{v₂} F :=
{ cone := @creates.raise_cone _ _ _ _ conn _ _ (limit.cone (F ⋙ forget)),
  is_limit :=
  { lift := λ s, over.hom_mk (limit.lift (F ⋙ forget) (forget.map_cone _)),
    uniq' :=
    begin
      intros s m K,
      ext1,
      dsimp at K ⊢,
      apply limit.hom_ext,
      intro j,
      rw limit.lift_π,
      dsimp,
      rw ← K j,
      refl,
    end } }

end over

end category_theory