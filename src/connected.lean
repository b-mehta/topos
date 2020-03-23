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
class connected (J : Type v₂) [𝒥 : category.{v₁} J] extends inhabited J :=
(iso_constant : Π {α : Type*} (F : J ⥤ discrete α), F ≅ (functor.const J).obj (F.obj default))

section J
variables  {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥

def any_functor_eq_constant [conn : connected J] {α : Type*} (F : J ⥤ discrete α) :
  F = (functor.const J).obj (F.obj (default J)) :=
begin
  apply functor.ext _ _,
    intro X,
    have z := conn.iso_constant,
    exact ((z F).hom.app X).down.1,
  intros, apply subsingleton.elim
end

def connected.of_any_functor_const_on_obj [inhabited J]
  (h : ∀ {α : Type u₂} (F : J ⥤ discrete α), ∀ (B : J), F.obj B = F.obj (default J)) :
  connected J :=
begin
  split,
  intros α F,
  specialize h F,
  apply nat_iso.of_components _ _,
  intro B, apply eq_to_iso (h B),
  intros, apply subsingleton.elim
end
end J

section examples
instance cospan_inhabited : inhabited walking_cospan := ⟨walking_cospan.one⟩

def cospan_connected : connected (walking_cospan) :=
begin
  apply connected.of_any_functor_const_on_obj,
  intros,
  cases B,
  exact (F.map walking_cospan.hom.inl).down.1,
  exact (F.map walking_cospan.hom.inr).down.1,
  refl
end

instance parallel_pair_inhabited : inhabited walking_parallel_pair := ⟨walking_parallel_pair.one⟩

def parallel_pair_connected : connected (walking_parallel_pair) :=
begin
  apply connected.of_any_functor_const_on_obj,
  intros,
  cases B,
  exact (F.map walking_parallel_pair_hom.left).down.1,
  refl
end
end examples

section C
variables  {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥
variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞
@[simps]
def functor_from_nat_trans {X Y : C} (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) : J ⥤ discrete (X ⟶ Y) :=
{ obj := α.app,
  map := λ A B f, eq_to_hom (begin have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm end),
  map_id' := λ A, rfl,
  map_comp' := λ A₁ A₂ A₃ f g, (eq_to_hom_trans _ _).symm
}

def nat_trans_from_connected [conn : connected J] {X Y : C} (j : J) (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  α.app j = (α.app (default J) : X ⟶ Y) :=
@congr_arg _ _ _ _
  (λ t : _ ⥤ _, t.obj j)
  (any_functor_eq_constant (functor_from_nat_trans α))
end C

local attribute [tidy] tactic.case_bash

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

section products

variables [has_binary_products.{v₂} C]

@[simps]
def prod_functor  : C ⥤ C ⥤ C :=
{ obj := λ X, { obj := λ Y, X ⨯ Y, map := λ Y Z, limits.prod.map (𝟙 X) },
  map := λ Y Z f, { app := λ T, limits.prod.map f (𝟙 T) }}

variables  {J : Type v₂} [small_category J]

@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

@[simps]
def γ₁  {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

@[simps]
def forget_cone  {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod_functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ₂ X }

def prod_preserves_connected_limits [conn : connected J] (X : C) :
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

end products

variables  {J : Type v₂} [𝒥' : small_category J]
include 𝒥'

namespace over

namespace creates

@[simps]
def nat_trans_in_over {B : C} (F : J ⥤ over B) :
  F ⋙ forget ⟶ (functor.const J).obj B :=
{ app := λ j, (F.obj j).hom }

@[simps]
def raise_cone [conn : connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) :
  cone F :=
{ X := @over.mk _ _ B c.X (c.π.app (default J) ≫ (F.obj (default J)).hom),
  π :=
  { app := λ j, over.hom_mk (c.π.app j) (@nat_trans_from_connected _ _ _ _ conn _ _ j (c.π ≫ nat_trans_in_over F)) } }

lemma raised_cone_lowers_to_original [conn : connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) (t : is_limit c) :
  forget.map_cone (@raise_cone _ _ _ _ conn _ _ c) = c :=
by tidy

omit 𝒥'
instance forget_reflects_iso {B : C} {X Y : over B} (f : X ⟶ Y) [t : is_iso (forget.map f)] : is_iso f :=
{ inv := over.hom_mk t.inv (by { dsimp, erw [(as_iso (forget.map f)).inv_comp_eq, over.w f] }) }
include 𝒥'

def raised_cone_is_limit [conn : connected J] {B : C} {F : J ⥤ over B} {c : cone (F ⋙ forget)} (t : is_limit c) :
  is_limit (@raise_cone _ _ _ _ conn _ _ c) :=
{ lift := λ s, over.hom_mk (t.lift (forget.map_cone s))
               (by { dsimp, slice_lhs 1 2 {rw t.fac}, exact over.w (s.π.app (default J)) }),
  uniq' :=
  begin
    intros s m K,
    ext1,
    dsimp at K ⊢,
    apply t.hom_ext,
    intro j,
    rw t.fac,
    dsimp,
    rw ← K j,
    refl,
  end }

@[simps]
def iso_apex_of_iso_cone {F : J ⥤ C} {c₁ c₂ : cone F} (h : c₁ ≅ c₂) : c₁.X ≅ c₂.X :=
{ hom := h.hom.hom,
  inv := h.inv.hom }

def any_cone_works [conn : connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) (t : is_limit c) (d : cone F) (h : forget.map_cone d ≅ c) :
  is_limit d :=
begin
  apply is_limit.of_iso_limit (@raised_cone_is_limit _ _ _ _ conn _ _ _ t),
  have comm: h.inv.hom ≫ d.X.hom = c.π.app (default J) ≫ (F.obj (default J)).hom,
    rw ← h.inv.w (default J),
    erw ← over.w (d.π.app (default J)),
    rw assoc, refl,

  set f: (raise_cone c).X ⟶ d.X := over.hom_mk (iso_apex_of_iso_cone h).inv comm,
  have that: is_iso (forget.map f),
    rw forget_map, rw hom_mk_left, apply_instance,
  haveI f_iso: is_iso f := @creates.forget_reflects_iso _ _ _ _ _ f that,
  apply cones.ext (as_iso f),
  intro j,
  ext1,
  exact (h.inv.w j).symm
end

end creates

def forgetful_creates_connected_limits [conn : connected J] {B : C} (F : J ⥤ over B) [has_limit (F ⋙ forget)] :
  has_limit F :=
{ cone := @creates.raise_cone _ _ _ _ conn _ _ (limit.cone (F ⋙ forget)),
  is_limit := creates.raised_cone_is_limit (limit.is_limit _) }

end over

end category_theory