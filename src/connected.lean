/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves
import to_mathlib

/-!
# Connected category

Define a connected category
-/
universes v₁ v₂ u₁ u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

variables {J : Type u₁} [𝒥 : category.{v₁} J]
include 𝒥

section constant_functor

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

structure functor.is_constant (F : J ⥤ C) :=
(val : C)
(const_obj : ∀ (B : J), F.obj B = val)
(const_hom : ∀ (B₁ B₂ : J) (f : B₁ ⟶ B₂), F.map f = eq_to_hom (const_obj B₁) ≫ eq_to_hom (const_obj B₂).symm)

end constant_functor

variable (J)
class is_connected extends inhabited J :=
(make_constant : Π {α : Type u₂} (F : J ⥤ discrete α), F.is_constant)

def connected_of_any_functor_const_obj [inhabited J] (h : ∀ {α : Type u₂} (F : J ⥤ discrete α), Σ' (val : α), ∀ (B : J), F.obj B = val) :
  is_connected.{v₁} J :=
begin
  split,
  intros α F,
  cases h F,
  refine ⟨fst, snd, _⟩,
  intros, apply subsingleton.elim
end

def connected_of_any_functor_const_obj' [inhabited J] (h : ∀ {α : Type u₂} (F : J ⥤ discrete α), ∀ (B : J), F.obj B = F.obj (default J)) :
  is_connected.{v₁} J :=
begin
  split,
  intros α F,
  specialize h F,
  refine ⟨F.obj (default J), h, _⟩,
  intros, apply subsingleton.elim
end

section examples
omit 𝒥

instance : inhabited walking_cospan := ⟨walking_cospan.one⟩

def cospan_connected : is_connected.{v₁} (walking_cospan.{v₁}) :=
begin
  apply connected_of_any_functor_const_obj',
  intros,
  cases B,
  exact (F.map walking_cospan.hom.inl).down.1,
  exact (F.map walking_cospan.hom.inr).down.1,
  refl
end

end examples

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞
variable {J}
/-- (implementation) -/
def functor_from_nat_trans {X Y : C} (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) : J ⥤ discrete (X ⟶ Y) :=
{ obj := α.app,
  map := λ A B f, eq_to_hom (begin have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm end),
  map_id' := λ A, rfl,
  map_comp' := λ A₁ A₂ A₃ f g, (eq_to_hom_trans _ _).symm
}

def nat_trans_from_connected [conn : is_connected.{v₁} J] (X Y : C) (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  Σ' (f : X ⟶ Y), ∀ (j : J), α.app j = f :=
begin
  set F := functor_from_nat_trans α,
  exact ⟨(@is_connected.make_constant _ _ conn _ F).val, (@is_connected.make_constant _ _ _ _ F).const_obj⟩
end

omit 𝒞

local attribute [tidy] tactic.case_bash

omit 𝒥

@[simps]
def prod_functor [category.{v₂} C] [has_binary_products.{v₂} C] : C ⥤ C ⥤ C :=
{ obj := λ X, { obj := λ Y, X ⨯ Y, map := λ Y Z, limits.prod.map (𝟙 X) },
  map := λ Y Z f, { app := λ T, limits.prod.map f (𝟙 T) }}

-- class preserves_limit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
-- (preserves : Π {c : cone K}, is_limit c → is_limit (F.map_cone c))
-- class preserves_colimit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
-- (preserves : Π {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c))

-- class preserves_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
-- (preserves_limit : Π {K : J ⥤ C}, preserves_limit K F)

-- include 𝒥

@[reducible]
def γ [small_category J] [category.{v₂} C] [has_binary_products.{v₂} C] {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

def γ₂ [small_category J] [category.{v₂} C] [has_binary_products.{v₂} C] {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

@[reducible]
def forget_cone [category.{u₁} C] [has_binary_products.{u₁} C] [small_category J] {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod_functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ X }

def prod_preserves_connected_limits [𝒞 : category.{u₁} C] [has_binary_products.{u₁} C] [small_category J] [conn : is_connected.{u₁} J] (X : C) :
  preserves_limits_of_shape J (prod_functor.obj X) :=
{ preserves_limit := λ K,
  { preserves := λ c l,
    { lift := λ s, limits.prod.lift (s.π.app (default _) ≫ limits.prod.fst) (l.lift (forget_cone s)),
      fac' := λ s j,
      begin
        apply prod.hom_ext,
        { rw assoc, rw functor.map_cone_π,
          simp, erw comp_id,
          obtain ⟨f, hf⟩ := @nat_trans_from_connected J _ C 𝒞 conn _ _ (s.π ≫ γ₂ X),
          have: s.π.app (default J) ≫ limits.prod.fst = f := hf (default J),
          rw this,
          rw ← hf j,
          refl },
        { have: l.lift (forget_cone s) ≫ c.π.app j = s.π.app j ≫ limits.prod.snd := l.fac (forget_cone s) j,
          rw ← this,
          simp }
      end,
      uniq' := λ s m K,
      begin
        apply prod.hom_ext,
        simp, specialize K (default J), rw ← K, simp, erw comp_id,
        simp, apply l.uniq (forget_cone s), intro j, specialize K j, dsimp at K, dsimp, rw ← K_1, simp
      end
    }
  }
}

end category_theory