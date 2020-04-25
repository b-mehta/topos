/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/

import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import tactic
import adjunction
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
variables {C : Type u} [𝒞 : category.{v} C] {A U V W X Y Z : C}
include 𝒞

local attribute [tidy] tactic.case_bash

open category

def prodinl_comp (X Y : C) [has_finite_products.{v} C] : prod_functor.obj (X ⨯ Y) ≅ prod_functor.obj Y ⋙ prod_functor.obj X :=
nat_iso.of_components (limits.prod.associator _ _) (by tidy)

end

class exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : has_finite_products.{v} C] (X : C) :=
(is_adj : is_left_adjoint (prod_functor.obj X))

def binary_product_exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : has_finite_products.{v} C] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) : exponentiable (X ⨯ Y) :=
{ is_adj :=
  { right := hX.is_adj.right ⋙ hY.is_adj.right,
    adj := adjunction_of_nat_iso_left (adjunction.comp _ _ hY.is_adj.adj hX.is_adj.adj) (prodinl_comp _ _).symm } }

class is_cartesian_closed (C : Type u) [𝒞 : category.{v} C] [has_finite_products.{v} C] :=
(cart_closed : Π (X : C), exponentiable X)

attribute [instance] is_cartesian_closed.cart_closed

variables {C : Type u} [𝒞 : category.{v} C] {A B X X' Y Y' Z : C}
include 𝒞

section exp
variables [has_finite_products.{v} C] [exponentiable A]

/-- This is (-)^A -/
def exp.functor (A : C) [exponentiable A] : C ⥤ C :=
(@exponentiable.is_adj _ _ _ A _).right

def exp.adjunction (A : C) [exponentiable A] : prod_functor.obj A ⊣ exp.functor A :=
exponentiable.is_adj.adj

def ev.nat_trans (A : C) [exponentiable A] : exp.functor A ⋙ prod_functor.obj A ⟶ 𝟭 C :=
exponentiable.is_adj.adj.counit

def coev.nat_trans (A : C) [exponentiable A] : 𝟭 C ⟶ prod_functor.obj A ⋙ exp.functor A :=
exponentiable.is_adj.adj.unit

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
adjunction.left_triangle_components (exp.adjunction A)

@[simp] lemma coev_ev : coev ≫ post _ ev = 𝟙 (A⟹B) :=
adjunction.right_triangle_components (exp.adjunction A)

lemma coev_nat (f : X ⟶ Y) : f ≫ coev = coev ≫ post _ (limits.prod.map (𝟙 A) f) :=
(coev.nat_trans A).naturality f

lemma ev_nat {f : X ⟶ Y} : limits.prod.map (𝟙 A) (post _ f) ≫ ev = ev ≫ f :=
(ev.nat_trans A).naturality f

/- aka curry -/
def exp_transpose : (A ⨯ Y ⟶ X) ≃ (Y ⟶ A⟹X) :=
exponentiable.is_adj.adj.hom_equiv _ _

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

end exp

section terminal
variable [has_finite_products.{v} C]

lemma prod_left_unitor_naturality (f : X ⟶ Y):
  (prod.left_unitor X).inv ≫ limits.prod.map (𝟙 _) f = f ≫ (prod.left_unitor Y).inv :=
begin
  apply prod.hom_ext,
  { apply subsingleton.elim },
  { simp [id_comp f] }
end

def terminal_exponentiable : exponentiable ⊤_C :=
{ is_adj := {
  right := 𝟭 C,
  adj := adjunction.mk_of_hom_equiv
  { hom_equiv := λ X _, have unitor : _, from prod.left_unitor X,
      ⟨λ a, unitor.inv ≫ a, λ a, unitor.hom ≫ a, by tidy, by tidy⟩ } } }

attribute [instance] terminal_exponentiable

def exp_terminal_iso : (⊤_C ⟹ X) ≅ X :=
yoneda.ext (⊤_ C ⟹ X) X
  (λ Y f, (prod.left_unitor Y).inv ≫ exp_transpose.inv_fun f)
  (λ Y f, exp_transpose.to_fun ((prod.left_unitor Y).hom ≫ f))
  (λ Z g, begin
    dsimp, rw ← assoc, erw iso.hom_inv_id (prod.left_unitor Z),
    simp [exp_transpose.right_inv g] end)
  (λ Z g, by simp)
  (λ Z W f g, begin
    rw [exp_transpose_natural_left_symm],
    slice_lhs 1 2 { erw prod_left_unitor_naturality f },
    rw assoc end)

@[reducible]
def point_at_hom [exponentiable A] (f : A ⟶ Y) : ⊤_C ⟶ (A ⟹ Y) :=
exp_transpose.to_fun (limits.prod.fst ≫ f)

end terminal

section pre

variables [has_finite_products.{v} C]

-- this notation (and the hats) are just here so i could figure out how to
-- do pre_map - I think the ⟨f,g⟩ might be nice but the rest can go (TODO)
local notation `⟨`f`, `g`⟩` := limits.prod.map f g

@[reducible]
def hat [exponentiable A] : (A ⨯ Y ⟶ X) → (Y ⟶ A ⟹ X) := exp_transpose.to_fun
@[reducible]
def unhat [exponentiable A] : (Y ⟶ A ⟹ X) → (A ⨯ Y ⟶ X) := exp_transpose.inv_fun

def pre (X : C) (f : B ⟶ A) [exponentiable A] [exponentiable B] :  (A⟹X) ⟶ B⟹X :=
hat (⟨f, 𝟙 (A ⟹ X)⟩ ≫ unhat (𝟙 (A ⟹ X)))

lemma pre_id [exponentiable A] : pre X (𝟙 A) = 𝟙 (A⟹X) :=
begin
  dunfold pre hat, erw exp_transpose_natural_left, rw exp_transpose.right_inv, simp
end

lemma pre_map [exponentiable A] [exponentiable B] {D : C} [exponentiable D] {f : A ⟶ B} {g : B ⟶ D} : pre X (f ≫ g) = pre X g ≫ pre X f :=
begin
  dunfold pre, apply function.injective_of_left_inverse exp_transpose.right_inv,
  rw exp_transpose.left_inv, rw ← exp_transpose_natural_left, rw exp_transpose.left_inv,
  show ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X)) =
    ⟨𝟙 A, (hat (⟨g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X))))⟩ ≫
      ⟨f, 𝟙 (B ⟹ X)⟩ ≫ unhat (𝟙 (B ⟹ X)),
  suffices: ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X)) =
    (⟨f, 𝟙 (D ⟹ X)⟩ ≫ ⟨𝟙 B, (hat (⟨g, 𝟙 (D ⟹ X)⟩ ≫ unhat (𝟙 (D ⟹ X))))⟩) ≫ unhat (𝟙 (B ⟹ X)),
  rw this, rw ← assoc, congr' 1, apply prod.hom_ext, simp, dsimp, simp, simp, dsimp, simp,
  have: ⟨f ≫ g, 𝟙 (D ⟹ X)⟩ = ⟨f, 𝟙 _⟩ ≫ ⟨g, 𝟙 _⟩, { rw prod_functorial },
  rw this, rw assoc, rw assoc, congr' 1, erw ← exp_transpose_natural_left_symm,
  apply function.injective_of_left_inverse exp_transpose.left_inv, rw exp_transpose_natural_right,
  rw exp_transpose.right_inv, simp, exact (exp_transpose_natural_right _ _).symm
end

end pre

def pre.functor [has_finite_products.{v} C] [is_cartesian_closed C] (X : C) : Cᵒᵖ ⥤ C :=
{ obj := λ A, (A.unop) ⟹ X,
  map := λ A B f, pre X f.unop,
  map_id' := begin intros, apply pre_id, end,
  map_comp' := begin intros, apply pre_map, end,
}

lemma exp_natural [has_finite_products.{v} C] [is_cartesian_closed C] {A B : C} {X Y : Cᵒᵖ} (f : A ⟶ B) (g : X ⟶ Y) :
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

def exp.difunctor [has_finite_products.{v} C] [is_cartesian_closed C] : C ⥤ Cᵒᵖ ⥤ C :=
{ obj := pre.functor,
  map := λ A B f, { app := λ X, post X.unop f, naturality' := λ X Y g, exp_natural _ _ },
  map_id' := λ X, by { ext, apply functor.map_id },
  map_comp' := λ X Y Z f g, by { ext, apply functor.map_comp } }

variables {D : Type u} [category.{v} D]
section functor

variables [has_finite_products.{v} C] [has_finite_products.{v} D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

-- (implementation)
def alternative_cone (A B : C) : cone (pair A B ⋙ F) :=
{ X := F.obj A ⨯ F.obj B,
  π := nat_trans.of_homs (λ j, walking_pair.cases_on j limits.prod.fst limits.prod.snd)}

-- (implementation)
def alt_is_limit (A B : C) : is_limit (functor.map_cone F (limit.cone (pair A B))) :=
preserves_limit.preserves (limit.is_limit (pair A B))

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

end functor

variables [has_finite_products.{v} C] [has_finite_products.{v} D] [is_cartesian_closed C] [is_cartesian_closed D]
variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F]

-- the exponential comparison map
def exp_comparison (A B : C) :
  F.obj (A ⟹ B) ⟶ F.obj A ⟹ F.obj B :=
hat ((mult_comparison F A _).inv ≫ F.map ev)

end category_theory
