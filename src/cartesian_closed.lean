/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/

import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import adjunction
import tactic
import to_mathlib
import binary_products

/-!
# Cartesian closed categories

Define exponentiable objects and cartesian closed categories.
Show that exponential forms a difunctor.
-/
universes v u

namespace category_theory

open limits category
section
variables {C : Type u} [𝒞 : category.{v} C] [has_binary_products.{v} C] {A U V W X Y Z : C}
include 𝒞

local attribute [tidy] tactic.case_bash

def prodinl (X : C) : C ⥤ C := prod_functor.obj X

@[simp] lemma prodinl_map_def {f : Y ⟶ Z} : (prodinl X).map f = limits.prod.map (𝟙 X) f := rfl
@[simp] lemma map_fst {f : U ⟶ V} {g : W ⟶ X} : limits.prod.map f g ≫ limits.prod.fst = limits.prod.fst ≫ f := by simp
@[simp] lemma map_snd {f : U ⟶ V} {g : W ⟶ X} : limits.prod.map f g ≫ limits.prod.snd = limits.prod.snd ≫ g := by simp
@[simp] lemma prod.map_id : limits.prod.map (𝟙 X) (𝟙 Y) = 𝟙 (X⨯Y) := begin apply prod.hom_ext, simp, simp end
@[simp] lemma lift_fst {f : W ⟶ X} {g : W ⟶ Y} : limits.prod.lift f g ≫ limits.prod.fst = f := by simp
@[simp] lemma lift_snd {f : W ⟶ X} {g : W ⟶ Y} : limits.prod.lift f g ≫ limits.prod.snd = g := by simp
open category

def prodinl_comp (X Y : C) : prodinl (X ⨯ Y) ≅ prodinl Y ⋙ prodinl X :=
nat_iso.of_components (limits.prod.associator _ _) (by tidy)

end

class exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] (X : C) :=
(exponentiable : is_left_adjoint (prodinl X))

def binary_product_exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) : exponentiable (X ⨯ Y) :=
{ exponentiable :=
  { right := hX.exponentiable.right ⋙ hY.exponentiable.right,
    adj := adjunction_of_nat_iso_left (adjunction.comp _ _ hY.exponentiable.adj hX.exponentiable.adj) (prodinl_comp _ _).symm } }

class is_cartesian_closed (C : Type u) [𝒞 : category.{v} C] [has_binary_products.{v} C] extends has_terminal.{v} C :=
(cart_closed : Π (X : C), exponentiable X)

instance exponentiable_of_cc {C : Type u} [𝒞 : category.{v} C] [@has_binary_products C 𝒞] [is_cartesian_closed C] {A : C} :
  exponentiable A := is_cartesian_closed.cart_closed A

variables {C : Type u} [𝒞 : category.{v} C] [has_binary_products.{v} C] {X X' Y Y' Z A B : C} [exponentiable A]
include 𝒞

/-- This is (-)^A -/
def exp.functor (A : C) [exponentiable A] : C ⥤ C :=
(exponentiable.exponentiable A).right

def exp.adjunction : prodinl A ⊣ exp.functor A :=
(exponentiable.exponentiable A).adj

def ev.nat_trans (A : C) [exponentiable A] : exp.functor A ⋙ prodinl A ⟶ 𝟭 C :=
exp.adjunction.counit

def coev.nat_trans (A : C) [exponentiable A] : 𝟭 C ⟶ prodinl A ⋙ exp.functor A :=
exp.adjunction.unit

/-- `B ^ A` or `A ⟹ B` -/
def exp (A : C) (B : C) [exponentiable A] : C := (exp.functor A).obj B

infixl `⟹`:20 := exp

-- [todo] rename as 'post compose' or similar?
def post (A : C) [exponentiable A] {X Y : C} (f : X ⟶ Y) : A⟹X ⟶ A⟹Y :=
(exp.functor A).map f

lemma post.map_comp {f : X ⟶ Y} {g : Y ⟶ Z} : post A (f ≫ g) = post A f ≫ post A g :=
begin
  show functor.map _ _ = _ ≫ _,
  rw (exp.functor A).map_comp',
  refl,
end

def ev : A ⨯ (A⟹B) ⟶ B :=
(ev.nat_trans A).app B

def coev : B ⟶ A⟹(A⨯B) :=
(coev.nat_trans A).app B

@[simp] lemma ev_coev : limits.prod.map (𝟙 A) coev ≫ ev = 𝟙 (A⨯B) :=
(@adjunction.left_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

@[simp] lemma coev_ev : coev ≫ post _ ev = 𝟙 (A⟹B) :=
(@adjunction.right_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

lemma coev_nat (f : X ⟶ Y) : f ≫ coev = coev ≫ post _ (limits.prod.map (𝟙 A) f) :=
(coev.nat_trans A).naturality f

lemma ev_nat {f : X ⟶ Y} : limits.prod.map (𝟙 A) (post _ f) ≫ ev = ev ≫ f :=
(ev.nat_trans A).naturality f

def exp_transpose : (A ⨯ Y ⟶ X) ≃ (Y ⟶ A⟹X) :=
exp.adjunction.hom_equiv _ _

lemma exp_transpose_natural_left  (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
  exp_transpose.to_fun (limits.prod.map (𝟙 _) f ≫ g) = f ≫ exp_transpose.to_fun g :=
adjunction.hom_equiv_naturality_left _ _ _

lemma exp_transpose_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
  exp_transpose.to_fun (f ≫ g) = exp_transpose.to_fun f ≫ post _ g :=
adjunction.hom_equiv_naturality_right _ _ _

lemma exp_transpose_natural_right_symm  (f : X ⟶ A⟹Y) (g : Y ⟶ Y') :
  exp_transpose.inv_fun (f ≫ post A g) = exp_transpose.inv_fun f ≫ g :=
adjunction.hom_equiv_naturality_right_symm _ _ _

lemma exp_transpose_natural_left_symm  (f : X ⟶ X') (g : X' ⟶ A⟹Y) :
  exp_transpose.inv_fun (f ≫ g) = limits.prod.map (𝟙 _) f ≫ exp_transpose.inv_fun g :=
adjunction.hom_equiv_naturality_left_symm _ _ _

section terminal
variable [has_terminal.{v} C]

lemma prod_left_unitor_naturality (f : X ⟶ Y):
  (prod.left_unitor X).inv ≫ limits.prod.map (𝟙 _) f = f ≫ (prod.left_unitor Y).inv :=
begin
  apply prod.hom_ext,
  { apply subsingleton.elim },
  { simp [id_comp C f] }
end

def terminal_exponentiable : exponentiable ⊤_C :=
{ exponentiable := {
  right := 𝟭 C,
  adj := adjunction.mk_of_hom_equiv
  { hom_equiv := λ X _, have unitor : _, from prod.left_unitor X,
      ⟨λ a, unitor.inv ≫ a, λ a, unitor.hom ≫ a, by tidy, by tidy⟩ } } }

attribute [instance] terminal_exponentiable

def exp_terminal_iso : (⊤_C ⟹ X) ≅ X :=
begin
  apply yoneda.ext (⊤_ C ⟹ X) X _ _ _ _ _,
  intros Y f, exact (prod.left_unitor Y).inv ≫ exp_transpose.inv_fun f,
  intros Y f, exact exp_transpose.to_fun ((prod.left_unitor Y).hom ≫ f),
  { intros Z g, dsimp,
    rw ← assoc, erw iso.hom_inv_id (prod.left_unitor Z),
    simp [exp_transpose.right_inv g] },
  { intros Z g, dsimp,
    rw exp_transpose.left_inv,
    rw ← assoc,
    erw iso.inv_hom_id (prod.left_unitor Z),
    simp },
  { intros Z W f g, dsimp,
    rw exp_transpose_natural_left_symm,
    rw ← assoc, rw ← assoc,
    erw prod_left_unitor_naturality _, refl },
end

@[reducible]
def point_at_hom (f : A ⟶ Y) : ⊤_C ⟶ (A ⟹ Y) :=
exp_transpose.to_fun (limits.prod.fst ≫ f)
end terminal

section pre

variables [exponentiable B]

-- this notation (and the hats) are just here so i could figure out how to
-- do pre_map - I think the ⟨f,g⟩ might be nice but the rest can go (TODO)
local notation `⟨`f`, `g`⟩` := limits.prod.map f g

@[reducible]
def hat : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) := exp_transpose.to_fun
@[reducible]
def unhat : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) := exp_transpose.inv_fun

def pre (X : C) (f : B ⟶ A) :  (A⟹X) ⟶ B⟹X :=
hat (⟨f, 𝟙 (A ⟹ X)⟩ ≫ unhat (𝟙 (A ⟹ X)))

lemma pre_id : pre X (𝟙 A) = 𝟙 (A⟹X) :=
begin
  dunfold pre hat, erw exp_transpose_natural_left, rw exp_transpose.right_inv, simp
end

lemma pre_map {D : C} [exponentiable D] {f : A ⟶ B} {g : B ⟶ D} : pre X (f ≫ g) = pre X g ≫ pre X f :=
begin
  dunfold pre, apply function.injective_of_left_inverse exp_transpose.right_inv,
  rw exp_transpose.left_inv, rw ← exp_transpose_natural_left, rw exp_transpose.left_inv,
  show ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X)) =
    ⟨𝟙 A, (hat (⟨g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X))))⟩ ≫
      ⟨f, 𝟙 (B ⟹ X)⟩ ≫ unhat (𝟙 (B ⟹ X)),
  suffices: ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X)) =
    (⟨f, 𝟙 (D ⟹ X)⟩ ≫ ⟨𝟙 B, (hat (⟨g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X))))⟩) ≫ unhat (𝟙 (B ⟹ X)),
  rw this, rw ← assoc, congr' 1, apply prod.hom_ext, simp, dsimp, simp, simp, dsimp, simp,
  have: ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ = ⟨f, 𝟙 _⟩ ≫ ⟨g, 𝟙 _⟩, apply prod.hom_ext, simp, simp,
  rw this, rw assoc, rw assoc, congr' 1, erw ← exp_transpose_natural_left_symm,
  apply function.injective_of_left_inverse exp_transpose.left_inv, rw exp_transpose_natural_right,
  rw exp_transpose.right_inv, simp, exact (exp_transpose_natural_right _ _).symm
end

def pre.functor [is_cartesian_closed C] (X : C) : Cᵒᵖ ⥤ C :=
{ obj := λ A, (A.unop) ⟹ X,
  map := λ A B f, pre X f.unop,
  map_id' := begin intros, apply pre_id, end,
  map_comp' := begin intros, apply pre_map, end,
}
end pre

lemma exp_natural [is_cartesian_closed C] (A B : C) (X Y : Cᵒᵖ) (f : A ⟶ B) (g : X ⟶ Y) :
  (pre.functor A).map g ≫ post (opposite.unop Y) f = post (opposite.unop X) f ≫ (pre.functor B).map g :=
begin
  dunfold pre.functor,
  dsimp, dunfold pre,
  show _ = _,
  rw ← exp_transpose_natural_right,
  rw ← exp_transpose_natural_left,
  congr' 1,
  rw assoc,
  rw ← exp_transpose_natural_right_symm,
  rw ← assoc,
  show _ = (limits.prod.map _ _ ≫ _) ≫ _,
  rw prod_map_comm,
  rw assoc,
  erw ← exp_transpose_natural_left_symm,
  rw id_comp,
  rw comp_id
end

def exp.difunctor [is_cartesian_closed C] : C ⥤ Cᵒᵖ ⥤ C :=
{ obj := pre.functor,
  map := λ A B f, { app := λ X, post X.unop f, naturality' := λ X Y g, begin apply exp_natural end },
  map_id' := λ X, begin ext, apply functor.map_id end,
  map_comp' := λ X Y Z f g, begin ext, apply functor.map_comp end
}

section functor

universes v₂ u₂

variables {D : Type u} [category.{v} D] [has_binary_products.{v} D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

-- (implementation)
def alternative_cone (A B : C) : cone (pair A B ⋙ F) :=
{ X := F.obj A ⨯ F.obj B,
  π := nat_trans.of_homs (λ j, walking_pair.cases_on j limits.prod.fst limits.prod.snd)}

-- (implementation)
def alt_is_limit (A B : C) : is_limit (functor.map_cone F (limit.cone (pair A B))) :=
preserves_limit.preserves F (limit.is_limit (pair A B))

-- the multiplicative comparison isomorphism
def mult_comparison (A B : C) : F.obj (A ⨯ B) ≅ F.obj A ⨯ F.obj B :=
{ hom := prod.lift (F.map limits.prod.fst) (F.map limits.prod.snd),
  inv := (alt_is_limit F A B).lift (alternative_cone F A B),
  hom_inv_id' :=
  begin
    apply is_limit.hom_ext (alt_is_limit F A B),
    rintro ⟨j⟩,
      rw assoc, rw (alt_is_limit F A B).fac,
      erw limit.lift_π, simp,
    rw assoc, rw (alt_is_limit F A B).fac,
    erw limit.lift_π, simp
  end,
  inv_hom_id' :=
  begin
    ext ⟨j⟩, simp, erw (alt_is_limit F A B).fac, refl,
    simp, erw (alt_is_limit F A B).fac, refl,
  end
}

variables [is_cartesian_closed C] [is_cartesian_closed D]

-- the exponential comparison map
def exp_comparison (A B : C) :
  F.obj (A ⟹ B) ⟶ F.obj A ⟹ F.obj B :=
hat ((mult_comparison F A _).inv ≫ F.map ev)

end functor

end category_theory