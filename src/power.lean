/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.adjunction.limits
import pullbacks
import sub
import subobject_classifier
import binary_products
import creates
import beck2
import category_theory.limits.opposites
import category_theory.limits.over
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers

/-!
# Power objects

Define power objects
-/
universes v u v₂ u₂

open category_theory category_theory.category category_theory.limits

attribute [instance] has_pullbacks_of_has_finite_limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def cone_is_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] :
  is_limit (pullback_cone.mk _ _ pullback.condition : pullback_cone f g) :=
pullback_cone.is_limit.mk _
  (λ s, pullback.lift (pullback_cone.fst s) (pullback_cone.snd s) (pullback_cone.condition s))
  (λ s, limit.lift_π _ _)
  (λ s, limit.lift_π _ _)
  (λ s m w, pullback.hom_ext (by { rw limit.lift_π, apply w walking_cospan.left }) (by { rw limit.lift_π, apply w walking_cospan.right }))

section faithful

variables {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒟
instance right_op_faithful {F : Cᵒᵖ ⥤ D} [faithful F] : faithful F.right_op :=
{ injectivity' :=
  begin
    dsimp,
    intros X Y f g h,
    have := has_hom.hom.op_inj ((faithful.injectivity F (has_hom.hom.op_inj h))),
    exact this
  end
}
end faithful

def op_equiv (A : C) (B : Cᵒᵖ): (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

variables [has_finite_limits.{v} C]

structure powerises {A PA niA B R : C} (memA : niA ⟶ PA ⨯ A) (m : R ⟶ B ⨯ A) (mhat : B ⟶ PA) :=
(top : R ⟶ niA)
(commutes : top ≫ memA = m ≫ limits.prod.map mhat (𝟙 A))
(forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
restate_axiom powerises.forms_pullback'

class has_power_object (A : C) :=
(PA niA : C)
(memA : niA ⟶ PA ⨯ A)
(mem_mono' : @mono _ 𝒞 _ _ memA)
(hat : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m], B ⟶ PA)
(powerises' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m], powerises memA m (hat m))
(uniquely' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m] (hat' : B ⟶ PA), powerises memA m hat' → hat' = hat m)

variable (C)

class has_power_objects :=
(has_power_object : Π (A : C), has_power_object.{v} A)

variable {C}

attribute [instance] has_power_objects.has_power_object
attribute [simp] pullback.condition

section convenience

variables (A : C) [has_power_object.{v} A]

def P : C := @has_power_object.PA _ 𝒞 _ A _
def ni : C := @has_power_object.niA _ 𝒞 _ A _
def mem : ni A ⟶ P A ⨯ A := has_power_object.memA
instance mem_mono : mono (mem A) := has_power_object.mem_mono'

variables {A} {B R : C} (m : R ⟶ B ⨯ A) [mono m]

def hat : B ⟶ P A := has_power_object.hat m
def hat_powerises : powerises (mem A) m (hat m) := has_power_object.powerises' m
def square.top : R ⟶ ni A := (hat_powerises m).top
def square.commutes : square.top m ≫ mem A = m ≫ limits.prod.map (hat m) (𝟙 A) := (hat_powerises m).commutes
def square.is_pullback : is_limit (pullback_cone.mk _ _ (square.commutes m)) := (hat_powerises m).forms_pullback
lemma unique_hat (hat' : B ⟶ P A) (hp : powerises (mem A) m hat') : hat' = hat m := has_power_object.uniquely' m hat' hp
end convenience

section functor_setup
variables {A B : C} (f : A ⟶ B) [has_power_object.{v} B]
def E : C := pullback (mem B) (limits.prod.map (𝟙 _) f)
def Emap : E f ⟶ P B ⨯ A := pullback.snd
instance : mono (Emap f) := pullback.snd_of_mono
lemma Esquare : (pullback.fst : E f ⟶ _) ≫ mem B = Emap f ≫ limits.prod.map (𝟙 _) f := pullback.condition
lemma Epb : is_limit (pullback_cone.mk _ _ (Esquare f)) :=
cone_is_pullback _ _

variable [has_power_object.{v} A]
def P_map : P B ⟶ P A :=
hat (Emap f)

lemma Psquare : square.top (Emap f) ≫ mem A = Emap f ≫ limits.prod.map (P_map f) (𝟙 A) :=
square.commutes (Emap f)

lemma Ppb : is_limit (pullback_cone.mk _ _ (Psquare f)) :=
square.is_pullback (Emap f)

lemma easy_lemma {D R : C} (m : R ⟶ D ⨯ B) [hm : mono m] :
  hat (pullback.snd : pullback m (limits.prod.map (𝟙 D) f) ⟶ D ⨯ A) = hat m ≫ P_map f :=
begin
  symmetry,
  apply unique_hat,
  let p : pullback m (limits.prod.map (𝟙 D) f) ⟶ R := pullback.fst,
  let q : pullback m (limits.prod.map (𝟙 D) f) ⟶ D ⨯ A := pullback.snd,
  have := (pasting _ _ _ _ _ _ _ pullback.condition (square.commutes m) (square.is_pullback m)).inv (cone_is_pullback _ _),
  have comm: (p ≫ square.top m) ≫ mem B = (pullback.snd ≫ limits.prod.map (hat m) (𝟙 A)) ≫ limits.prod.map (𝟙 (P B)) f,
  { simp [← prod_map_comm, square.commutes m, pullback.condition_assoc] },
  have := (pasting (pullback.lift _ _ comm) pullback.fst _ (Emap f) (mem B) _ _ (limit.lift_π _ _) pullback.condition (Epb f)).hom _,
    swap, convert this using 2, rw prod_map_comm, rw prod_map_comm, apply limit.lift_π,
  have := (pasting (pullback.lift _ _ comm) _ _ (Emap f) _ _ _ (limit.lift_π _ _) (Psquare f) (square.is_pullback (Emap f))).inv this,
  refine ⟨pullback.lift _ _ comm ≫ square.top (Emap f), _, _⟩,
    simpa [square.commutes, reassoc_of (show pullback.lift _ _ comm ≫ Emap f = _, from limit.lift_π _ _), prod_functorial],
  convert this using 2,
  rw prod_functorial,
  rw prod_functorial
end

-- We need to assume g₁ = hom ≫ g₂. From here if we know that hom,inv cancel then we get g₂ = inv ≫ g₁.
-- Instead we assume this and derive that hom,inv cancel
lemma lifting {A B R₁ R₂ : C} [has_power_object.{v} A] {g₁ : R₁ ⟶ B ⨯ A} {g₂ : R₂ ⟶ B ⨯ A} [mono g₁] [mono g₂] (hom : R₁ ⟶ R₂) (inv : R₂ ⟶ R₁) :
  g₁ = hom ≫ g₂ → g₂ = inv ≫ g₁ → hat g₁ = hat g₂ :=
begin
  intros k l,
  have hi: hom ≫ inv = 𝟙 _,
    rw ← cancel_mono g₁,
    conv_rhs {rw [k, l]}, simp,
  have ih: inv ≫ hom = 𝟙 _,
    rw ← cancel_mono g₂,
    conv_rhs {rw [l, k]}, simp,
  apply unique_hat,
  refine ⟨inv ≫ square.top g₁, _, _⟩,
  { slice_lhs 2 3 {rw square.commutes g₁},
    slice_lhs 1 2 {rw ← l} },
  { apply is_limit.of_iso_limit (square.is_pullback g₁),
    refine cones.ext ⟨hom, inv, ‹_›, ‹_›⟩ (λ j, _),
    cases j,
    { simp [reassoc_of hi] },
    { cases j,
      { simp [reassoc_of hi] },
      { simp [k] } } }
end
def how_inj_is_hat {A B R₁ R₂ : C} [has_power_object.{v} A] {f₁ : R₁ ⟶ B ⨯ A} {f₂ : R₂ ⟶ B ⨯ A} [mono f₁] [mono f₂] (h : hat f₁ = hat f₂) :
  R₁ ≅ R₂ :=
{ hom := (square.is_pullback f₂).lift (pullback_cone.mk (square.top f₁) f₁ (h ▸ square.commutes f₁)),
  inv := (square.is_pullback f₁).lift (pullback_cone.mk (square.top f₂) f₂ (h.symm ▸ square.commutes f₂)),
  hom_inv_id' :=
  begin
    erw [← cancel_mono f₁, assoc,
         (square.is_pullback f₁).fac _ walking_cospan.right,
         (square.is_pullback f₂).fac _ walking_cospan.right],
    simp
  end,
  inv_hom_id' :=
  begin
    erw [← cancel_mono f₂, assoc,
         (square.is_pullback f₂).fac _ walking_cospan.right,
         (square.is_pullback f₁).fac _ walking_cospan.right],
    simp
  end }

lemma very_inj {A B R₁ R₂ : C} [has_power_object.{v} A] {f₁ : R₁ ⟶ B ⨯ A} {f₂ : R₂ ⟶ B ⨯ A} [mono f₁] [mono f₂] (h : hat f₁ = hat f₂) :
  (how_inj_is_hat h).hom ≫ f₂ = f₁ :=
(square.is_pullback f₂).fac _ walking_cospan.right

lemma liftable {A B : C} [has_power_object.{v} A] (a b : sub' (B ⨯ A)) : (a ≈ b) → @hat _ _ _ _ _ _ _ a.1.hom a.2 = @hat _ _ _ _ _ _ _ b.1.hom b.2 :=
begin
  rintros ⟨⟨hom, k⟩, ⟨inv, l⟩⟩,
  exact @lifting _ _ _ _ _ _ _ _ _ _ a.2 b.2 _ _ k l,
end
def hat_sub {A B : C} [has_power_object.{v} A] : sub (B ⨯ A) → (B ⟶ P A) :=
quotient.lift (λ (f : sub' (B ⨯ A)), @hat _ _ _ _ _ _ _ f.1.hom f.2) liftable

def hat_sub' {A B : C} [has_power_object.{v} A] (k : B ⟶ P A) : sub (B ⨯ A) :=
quotient.mk ⟨over.mk (pullback.snd : pullback (mem A) (limits.prod.map k (𝟙 _)) ⟶ B ⨯ A), pullback.snd_of_mono⟩

def hat_natural_right {A A' B R : C} [has_power_object.{v} A] [has_power_object.{v} A'] (k : R ⟶ B ⨯ A) [mono k] (g : A' ⟶ A) :
  hat k ≫ P_map g = hat (pullback.snd : pullback k (limits.prod.map (𝟙 B) g) ⟶ B ⨯ A') :=
begin
  rw easy_lemma
end
def hat_natural_left {A B B' R : C} [has_power_object.{v} A] (k : R ⟶ B ⨯ A) [mono k] (g : B' ⟶ B) :
  g ≫ hat k = hat (pullback.snd : pullback k (limits.prod.map g (𝟙 A)) ⟶ B' ⨯ A) :=
begin
  apply unique_hat,
  refine ⟨pullback.fst ≫ square.top k, _, _⟩,
  slice_lhs 2 3 {rw square.commutes},
  slice_lhs 1 2 {rw pullback.condition},
  rw assoc,
  rw ← prod_functorial,
  have := (pasting pullback.fst _ pullback.snd k _ (limits.prod.map g (𝟙 A)) _ _ _ (square.is_pullback k)).inv (cone_is_pullback _ _),
  convert this,
  rw prod_functorial,
  rw prod_functorial,
end

def hat_sub_natural_left (A B B' : C) [has_power_object.{v} A] (k : sub (B ⨯ A)) (g : B' ⟶ B) : g ≫ hat_sub k = hat_sub (sub_map (limits.prod.map g (𝟙 A)) k) :=
begin
  apply quotient.induction_on k,
  dsimp [hat_sub, sub_map], intro a,
  rw hat_natural_left
end

def hat_sub_natural_right {A A' B : C} [has_power_object.{v} A] [has_power_object.{v} A'] (k : sub (B ⨯ A)) (g : A' ⟶ A) : hat_sub k ≫ P_map g = hat_sub (sub_map (limits.prod.map (𝟙 B) g) k) :=
begin
  apply quotient.induction_on k,
  dsimp [hat_sub, sub_map],
  intro a,
  rw ← easy_lemma
end

@[simps]
def hat_sub'' {A B : C} [has_power_object.{v} A] : (B ⟶ P A) ≃ sub (B ⨯ A) :=
{ to_fun := hat_sub',
  inv_fun := hat_sub,
  left_inv :=
  begin
    intro g,
    dsimp [hat_sub, hat_sub'],
    symmetry,
    apply unique_hat,
    exact ⟨_, pullback.condition, cone_is_pullback _ _⟩
  end,
  right_inv :=
  begin
    intro g,
    dsimp [hat_sub, hat_sub'],
    apply quotient.induction_on g,
    intro g',
    haveI := g'.2,
    apply quotient.sound,
    dsimp,
    split,
    refine ⟨_, _⟩,
    apply (square.is_pullback g'.1.hom).lift (pullback_cone.mk pullback.fst pullback.snd pullback.condition),
    dsimp, erw (square.is_pullback g'.1.hom).fac _ walking_cospan.right, refl,
    refine ⟨_, _⟩,
    apply pullback.lift (square.top g'.1.hom) g'.1.hom (square.commutes g'.1.hom),
    simp
  end }

def hat_sub'_natural_right (A A' B : C) [has_power_object.{v} A] [has_power_object.{v} A'] (k : B ⟶ P A) (g : A' ⟶ A) : hat_sub' (k ≫ P_map g) = sub_map (limits.prod.map (𝟙 B) g) (hat_sub' k) :=
begin
  erw ← hat_sub''.eq_symm_apply,
  dsimp [hat_sub''],
  rw ← hat_sub_natural_right,
  congr' 1,
  apply (hat_sub''.left_inv k).symm
end

def hat_sub'_natural_left {A B B' : C} [has_power_object.{v} A] (k : B ⟶ P A) (g : B' ⟶ B) : hat_sub' (g ≫ k) = sub_map (limits.prod.map g (𝟙 A)) (hat_sub' k) :=
begin
  erw ← hat_sub''.eq_symm_apply,
  dsimp [hat_sub''],
  rw ← hat_sub_natural_left,
  congr' 1,
  apply (hat_sub''.left_inv k).symm
end

lemma P_map_id (X : C) [has_power_object.{v} X] : P_map (𝟙 X) = 𝟙 (P X) :=
begin
  symmetry, apply unique_hat,
  refine ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩
end
lemma P_map_comp {X Y Z : C} [has_power_object.{v} X] [has_power_object.{v} Y] [has_power_object.{v} Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
  P_map (f ≫ g) = P_map g ≫ P_map f :=
begin
  erw ← easy_lemma,
  rw P_map,
  refine lifting _ _ _ _,
  { refine pullback.lift (pullback.lift pullback.fst (pullback.snd ≫ limits.prod.map (𝟙 _) f) _) pullback.snd _,
    { rw pullback.condition, rw assoc, congr' 1, apply prod.hom_ext; simp,
      erw comp_id, erw comp_id, erw comp_id },
    { erw limit.lift_π, refl } },
  { refine pullback.lift _ _ _,
    apply pullback.fst ≫ pullback.fst, apply pullback.snd,
    slice_lhs 2 3 {rw pullback.condition},
    slice_lhs 1 2 {erw pullback.condition},
    rw assoc, apply prod.hom_ext; simp,
    erw comp_id },
  { simp, refl },
  { erw limit.lift_π, refl }
end

def P_functor [has_power_objects.{v} C] : Cᵒᵖ ⥤ C :=
{ obj := λ X, P X.unop,
  map := λ X Y f, P_map f.unop,
  map_id' := λ X, P_map_id _,
  map_comp' := λ X Y Z f g, P_map_comp _ _ }
end functor_setup

def thing (X Y Z : C) (g : Y ⟶ Z) :
  is_limit (pullback_cone.mk (limits.prod.map g (𝟙 X)) (prod.lift limits.prod.snd limits.prod.fst) (begin apply prod.hom_ext; simp end) : pullback_cone (prod.lift limits.prod.snd limits.prod.fst) (limits.prod.map (𝟙 X) g)) :=
begin
  refine pullback_cone.is_limit.mk _ _ _ _ _,
  intro c,
  apply pullback_cone.snd c ≫ (limits.prod.braiding _ _).hom,
  intro c,
  apply prod.hom_ext,
  have := pullback_cone.condition c =≫ limits.prod.snd,
  simp at this, simp, exact this.symm,
  have := pullback_cone.condition c =≫ limits.prod.fst,
  simp at this, simp, exact this.symm,
  intro c,
  rw category.assoc, apply prod.hom_ext,
  simp, simp,
  intros c m J,
  rw ← cancel_mono (limits.prod.braiding X Y).inv,
  rw category.assoc, rw iso.hom_inv_id, rw comp_id,
  apply J walking_cospan.right,
end

def self_adj [has_power_objects.{v} C] : is_right_adjoint (@P_functor C 𝒞 _ _) :=
{ left := P_functor.right_op,
  adj := adjunction.mk_of_hom_equiv
  { hom_equiv :=
    begin
      intros A B,
      apply equiv.trans _ hat_sub''.symm,
      apply equiv.trans (op_equiv (P_functor.obj (opposite.op A)) B),
      apply equiv.trans hat_sub'',
      apply sub_iso_compose (limits.prod.braiding _ _),
    end,
    hom_equiv_naturality_left_symm' :=
    begin
      intros X' X Y f g,
      dsimp [hat_sub''],
      simp,
      change (hat_sub ((sub_iso_compose (prod.braiding (opposite.unop Y) X')).inv_fun (hat_sub' (f ≫ g)))).op =
      (P_functor.map (has_hom.hom.op f)).op ≫
        (hat_sub ((sub_iso_compose (prod.braiding (opposite.unop Y) X)).inv_fun (hat_sub' g))).op,
      rw ← op_comp,
      congr' 1,
      erw hat_sub_natural_right,
      congr' 1,
      rw has_hom.hom.unop_op,
      dsimp [sub_iso_compose],
      rw hat_sub'_natural_left,
      apply postcompose_sub_comm,
      swap,
      apply prod.hom_ext, simp, simp,
      apply thing
    end,
    hom_equiv_naturality_right' :=
    begin
      intros X Y Y' f g,
      dsimp [hat_sub'', sub_iso_compose, op_equiv],
      erw hat_sub_natural_right, congr' 1,
      rw hat_sub'_natural_left,
      apply postcompose_sub_comm,
      swap,
      apply prod.hom_ext,
      simp,
      simp,
      apply thing
    end
  }
}

@[reducible]
def diagonal (A : C) : A ⟶ A ⨯ A := limits.prod.lift (𝟙 A) (𝟙 A)
instance mono_prod_lift_of_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono f] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.fst,
  simp at this,
  rwa cancel_mono at this,
end

instance mono_prod_lift_of_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono g] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.snd,
  simp at this,
  rwa cancel_mono at this,
end

@[reducible]
def singleton_arrow (A : C) [has_power_object.{v} A] : A ⟶ P A := hat (diagonal A)

set_option trace.app_builder true

lemma seven_six_one {A B : C} [has_power_object.{v} B] (f : A ⟶ B) : hat (limits.prod.lift (𝟙 A) f) = f ≫ singleton_arrow B :=
begin
  rw hat_natural_left,
  refine lifting (pullback.lift f (limits.prod.lift (𝟙 A) f) _) (pullback.snd ≫ limits.prod.fst) _ _,
  { apply prod.hom_ext,
    { simp [id_comp f] },
    { simp [comp_id f] } },
  { simp },
  { apply prod.hom_ext,
    { simp },
    { slice_rhs 3 4 {rw limit.lift_π},
      have q : _ ≫ diagonal B = _ ≫ limits.prod.map f (𝟙 B) := pullback.condition,
      have q₁ := q =≫ limits.prod.fst,
      rw [assoc, assoc] at q₁, simp only [limit.map_π] at q₁,
      erw ← q₁,
      have q₂ := q =≫ limits.prod.snd,
      rw [assoc, assoc] at q₂, simp at q₂, rw q₂, simp,
      erw comp_id }
    }
end

lemma seven_six_two {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) :
  hat (limits.prod.lift f (𝟙 A)) = singleton_arrow B ≫ P_map f :=
begin
  erw hat_natural_right,
  refine lifting (pullback.lift f (limits.prod.lift f (𝟙 A)) _) (pullback.snd ≫ limits.prod.snd) _ _,
  apply prod.hom_ext, simp, erw comp_id,
  simp, erw id_comp,
  simp, apply prod.hom_ext,
  simp,
  have: (_ ≫ diagonal B) ≫ _ = (_ ≫ limits.prod.map (𝟙 B) f) ≫ _ := pullback.condition =≫ limits.prod.snd,
  rw [assoc] at this, simp at this, erw ← this,
  have: (_ ≫ diagonal B) ≫ _ = (_ ≫ limits.prod.map (𝟙 B) f) ≫ _ := pullback.condition =≫ limits.prod.fst,
  rw [assoc] at this, simp at this, rw this, dsimp, simp,
  simp
end

instance singleton_mono (A : C) [has_power_object.{v} A] : mono (singleton_arrow A) :=
begin
  split,
  intros,
  rw [← seven_six_one, ← seven_six_one] at w,
  have q := very_inj w =≫ limits.prod.fst,
  simp at q,
  have r := very_inj w =≫ limits.prod.snd,
  simp [q] at r,
  rw r
end

instance pfaithful [has_power_objects.{v} C] : faithful (@P_functor _ 𝒞 _ _) :=
begin
  refine ⟨_⟩,
  dsimp, intros A B f g k,
  have w: hat (limits.prod.lift f.unop (𝟙 B.unop)) = hat (limits.prod.lift g.unop (𝟙 B.unop)),
    rw seven_six_two, rw seven_six_two,
    show _ ≫ P_functor.map f = _ ≫ P_map (has_hom.hom.unop g),
    rw k, refl,
  have q := very_inj w =≫ limits.prod.snd,
  simp at q,
  have r := very_inj w =≫ limits.prod.fst,
  simp [q] at r,
  apply has_hom.hom.unop_inj, symmetry, assumption
end

lemma p_faithful {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f g : A ⟶ B) : P_map f = P_map g → f = g :=
begin
  intro k,
  have w: hat (limits.prod.lift f (𝟙 _)) = hat (limits.prod.lift g (𝟙 _)),
    rw [seven_six_two, seven_six_two, k],
  have q := very_inj w =≫ limits.prod.snd,
  simp at q,
  have r := very_inj w =≫ limits.prod.fst,
  simp [q] at r,
  symmetry, assumption
end

instance mono_prod_map {X Y Z W : C} (f : X ⟶ Y) (g : W ⟶ Z) [mono f] [mono g] : mono (limits.prod.map f g) :=
begin
  split, intros A h k l,
  apply prod.hom_ext,
  rw ← cancel_mono f,
  rw assoc, rw assoc,
  have := l =≫ limits.prod.fst,
  simp at this, assumption,
  have := l =≫ limits.prod.snd,
  simp at this,
  rwa ← cancel_mono g, simpa
end

def internal_image {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] : P A ⟶ P B :=
hat (mem A ≫ limits.prod.map (𝟙 (P A)) f)

-- TODO: this doesn't use pasting so it's super long. can we make it nicer by using pasting?
-- TODO: if not, it's still a horribly long proof which desperately needs a cleanup
lemma naturalish {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] {R D : C} (m : R ⟶ D ⨯ A) [mono m] :
  hat m ≫ internal_image f = hat (m ≫ limits.prod.map (𝟙 D) f) :=
begin
  rw internal_image,
  rw hat_natural_left,
  have comm: pullback.fst ≫ mem A = prod.lift (pullback.snd ≫ limits.prod.fst) (pullback.fst ≫ mem A ≫ limits.prod.snd) ≫ limits.prod.map (hat m) (𝟙 A),
  { have q: pullback.fst ≫ mem A ≫ limits.prod.map (𝟙 (P A)) f = pullback.snd ≫ limits.prod.map (hat m) (𝟙 B) := pullback.condition,
    have q1 := q =≫ limits.prod.fst,
    simp only [limits.prod.map_fst, assoc] at q1, erw comp_id at q1,
    apply prod.hom_ext,
    { simpa using q1 },
    { simp only [map_pair_right, limit.lift_π, cones.postcompose_obj_π, limit.lift_map, assoc, binary_fan.mk_π_app_right, nat_trans.comp_app], dsimp, simp } },
  let the_cone := (pullback_cone.mk pullback.fst (limits.prod.lift (pullback.snd ≫ limits.prod.fst) (pullback.fst ≫ mem A ≫ limits.prod.snd)) comm),
  apply lifting _ _ _ _,
  { apply (square.is_pullback m).lift the_cone },
  { apply pullback.lift (square.top m) (m ≫ limits.prod.map (𝟙 _) f) _,
    slice_lhs 1 2 {rw square.commutes m},
    slice_lhs 2 3 {rw ← prod_map_comm},
    simp },
  { have: (square.is_pullback m).lift the_cone ≫ m = _ := (square.is_pullback m).fac the_cone walking_cospan.right,
    slice_rhs 1 2 {rw this},
    apply prod.hom_ext,
    dsimp, simp, erw category.comp_id,
    simp,
    have: (pullback.fst ≫ mem A ≫ limits.prod.map (𝟙 _) f) ≫ limits.prod.snd = (pullback.snd ≫ limits.prod.map (hat m) (𝟙 _)) ≫ limits.prod.snd := pullback.condition =≫ limits.prod.snd,
    rw [assoc] at this, simp at this,
    rw this,
    erw comp_id },
  { rw limit.lift_π, refl }
end

lemma internal_image_map_comp {X Y Z : C} [has_power_object.{v} X] [has_power_object.{v} Y] [has_power_object.{v} Z]
  (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  internal_image (f ≫ g) = internal_image f ≫ internal_image g :=
begin
  erw naturalish, rw internal_image,
  congr' 1, rw prod_functorial',
  simp
end

-- def powerises_id (A : C) [has_power_object.{v} A] : powerises (mem A) (mem A) (𝟙 (P A)) :=
-- { top := 𝟙 _,
--   commutes := begin apply prod.hom_ext; simp, erw comp_id, erw comp_id end,
--   forms_pullback' := begin convert pullback.with_id_l' (mem A), all_goals {apply prod.hom_ext; simp, erw comp_id, erw comp_id },  end
-- }
lemma internal_image_map_id {X : C} [has_power_object.{v} X] : internal_image (𝟙 X) = 𝟙 (P X) :=
begin
  symmetry, apply unique_hat,
  have: limits.prod.map (𝟙 (P X)) (𝟙 X) = 𝟙 _,
  { apply prod.hom_ext,
    { erw [limits.prod.map_fst, comp_id, id_comp] },
    { erw [limits.prod.map_snd, comp_id, id_comp] } },
  rw [this, comp_id],
  refine ⟨𝟙 _, _, _⟩,
  rw [id_comp, this, comp_id],
  refine pullback_cone.is_limit.mk _ _ _ _ _,
  { intro s,
    exact s.π.app walking_cospan.left },
  { intro s,
    erw comp_id },
  { intro s,
    simp [pullback_cone.condition s, this] },
  { intros s m w,
    rw ← w walking_cospan.left, dsimp, apply (comp_id _).symm,
  }
end

theorem beck_chevalley {A B C' D : C}
  [has_power_object.{v} A] [has_power_object.{v} B]
  [has_power_object.{v} C'] [has_power_object.{v} D]
  {h : D ⟶ A} {f : A ⟶ C'} {k : D ⟶ B} {g : B ⟶ C'} (comm : h ≫ f = k ≫ g) [mono f] [mono k]
  (t : is_limit (pullback_cone.mk h k comm)) :
  internal_image f ≫ P_map g = P_map h ≫ internal_image k :=
begin
  erw naturalish,
  erw hat_natural_right,
  set X := pullback (mem A ≫ limits.prod.map (𝟙 (P A)) f) (limits.prod.map (𝟙 (P A)) g),
  set π₁ : X ⟶ ni A := pullback.fst,
  set π₂ : X ⟶ P A ⨯ B := pullback.snd,
  have comm2: (π₁ ≫ mem A ≫ limits.prod.snd) ≫ f = (π₂ ≫ limits.prod.snd) ≫ g,
    have: (π₁ ≫ _) ≫ _ = (_ ≫ _) ≫ _ := pullback.condition =≫ limits.prod.snd,
    rw [assoc] at this, simp at this, rwa [assoc, assoc, assoc],
  set l: X ⟶ D := t.lift (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2),
  have lprop₁: l ≫ h = π₁ ≫ mem A ≫ limits.prod.snd,
    exact t.fac (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2) walking_cospan.left,
  have lprop₂: l ≫ k = π₂ ≫ limits.prod.snd,
    exact t.fac (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2) walking_cospan.right,
  have comm3: π₁ ≫ mem A ≫ limits.prod.fst = π₂ ≫ limits.prod.fst,
    have: (π₁ ≫ _) ≫ _ = (_ ≫ _) ≫ _ := pullback.condition =≫ limits.prod.fst,
    rw [assoc] at this, simp at this, erw [comp_id, comp_id] at this, assumption,
  refine lifting _ _ _ _,
  { apply pullback.lift π₁ (limits.prod.lift (π₂ ≫ limits.prod.fst) l) _,
    apply prod.hom_ext, rw [assoc, comm3], simp, erw comp_id, rw [assoc, ← lprop₁], simp },
  { refine pullback.lift pullback.fst (pullback.snd ≫ limits.prod.map (𝟙 _) k) _,
    slice_lhs 1 2 {rw pullback.condition},
    rw [assoc, assoc, ← prod_functorial', comm, prod_functorial'] },
  { rw ← assoc, erw limit.lift_π, apply prod.hom_ext; simp, erw comp_id,
    exact lprop₂.symm },
  { erw limit.lift_π, refl }
end

def classifying_powers [has_power_object.{v} (⊤_ C)] {U X : C} (f : U ⟶ X) [mono f] :
  classifying (mem (⊤_ C) ≫ limits.prod.fst) f (hat (f ≫ prod.lift (𝟙 X) (terminal.from X))) :=
{ k := square.top (f ≫ prod.lift (𝟙 X) (terminal.from X)),
  commutes :=
  begin
    rw ← assoc,
    rw square.commutes (f ≫ limits.prod.lift (𝟙 X) (terminal.from X)),
    simp, erw id_comp,
  end,
  forms_pullback' :=
  begin
    refine pullback_cone.is_limit.mk _ _ _ _ _,
    { intro s,
      apply (square.is_pullback (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))).lift (pullback_cone.mk (pullback_cone.fst s) _ _),
      apply pullback_cone.snd s ≫ (prod.right_unitor _).inv,
      apply prod.hom_ext,
      simp, rw pullback_cone.condition s, erw id_comp,
      apply subsingleton.elim },
    { intro s,
      have comm: pullback_cone.fst s ≫ mem (⊤_ C) = (pullback_cone.snd s ≫ (prod.right_unitor X).inv) ≫ limits.prod.map (hat (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))) (𝟙 (⊤_ C)),
          apply prod.hom_ext,
          simp, rw pullback_cone.condition s, erw id_comp,
          apply subsingleton.elim,
        exact (square.is_pullback (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))).fac (pullback_cone.mk (pullback_cone.fst s) _ comm) walking_cospan.left },
    { intro s,
      have comm: pullback_cone.fst s ≫ mem (⊤_ C) = (pullback_cone.snd s ≫ (prod.right_unitor X).inv) ≫ limits.prod.map (hat (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))) (𝟙 (⊤_ C)),
        apply prod.hom_ext,
        simp, rw pullback_cone.condition s, erw id_comp,
        apply subsingleton.elim,
      have := (square.is_pullback (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))).fac (pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ (prod.right_unitor _).inv) comm) walking_cospan.right =≫ limits.prod.fst,
      dsimp at this, rw [assoc, assoc, assoc] at this, simp at this, exact this },
    { intros s m J,
      have comm: pullback_cone.fst s ≫ mem (⊤_ C) = (pullback_cone.snd s ≫ (prod.right_unitor X).inv) ≫ limits.prod.map (hat (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))) (𝟙 (⊤_ C)),
        apply prod.hom_ext,
        simp, rw pullback_cone.condition s, erw id_comp,
        apply subsingleton.elim,
      apply (square.is_pullback (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))).hom_ext,
      refine pullback_cone.equalizer_ext (pullback_cone.mk (square.top (f ≫ prod.lift (𝟙 X) (terminal.from X)))
           (f ≫ prod.lift (𝟙 X) (terminal.from X)) _) _ _,
      rw (square.is_pullback (f ≫ prod.lift (𝟙 X) (terminal.from X))).fac,
      change m ≫ (square.top (f ≫ limits.prod.lift (𝟙 X) (terminal.from X))) = (pullback_cone.fst s),
      apply J walking_cospan.left,
      rw (square.is_pullback (f ≫ prod.lift (𝟙 X) (terminal.from X))).fac,
      change m ≫ (f ≫ prod.lift (𝟙 X) (terminal.from X)) = pullback_cone.snd s ≫ (prod.right_unitor X).inv,
      apply prod.hom_ext,
      simp, exact J walking_cospan.right,
      apply subsingleton.elim }
  end }

def classifying_powers' [has_power_object.{v} (⊤_ C)] {U X : C} (f : U ⟶ X) [mono f]
  (χ₁ : X ⟶ P (⊤_ C)) (k : classifying (mem (⊤_ C) ≫ (prod.right_unitor (P (⊤_ C))).hom) f χ₁) :
  powerises (mem (⊤_ C)) (f ≫ prod.lift (𝟙 X) (terminal.from X)) χ₁ :=
begin
  set top := k.k,
  have comm: top ≫ _ = _ ≫ _ := k.commutes,
  have pb: is_limit (pullback_cone.mk _ _ comm) := k.forms_pullback',
  refine ⟨top, _, _⟩,
  { apply prod.hom_ext,
    { rw assoc, erw comm, simp, erw id_comp },
    { apply subsingleton.elim } },
  { refine pullback_cone.is_limit.mk _ _ _ _ _,
    { intro s,
      apply pb.lift (pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.fst) _),
      rw assoc,
      have := pullback_cone.condition s =≫ limits.prod.fst,
      simp at this, exact this },
    { intro s,
      exact pb.fac (pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.fst) _) walking_cospan.left },
    { intro s,
      erw ← assoc,
      erw pb.fac (pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.fst) _) walking_cospan.right,
      erw assoc,
      erw (prod.right_unitor X).hom_inv_id,
      erw comp_id },
    { intros s m J,
      apply pb.hom_ext,
      refine pullback_cone.equalizer_ext (pullback_cone.mk top f comm) _ _,
      rw pb.fac,
      exact J walking_cospan.left,
      rw pb.fac,
      dunfold pullback_cone.snd, dsimp,
      conv_rhs {rw [← J walking_cospan.right, assoc]},
      dsimp,
      simp } }
end

instance weak_topos_has_subobj [has_power_object.{v} (⊤_ C)] : has_subobject_classifier.{v} C :=
{ Ω := P (⊤_ C),
  Ω₀ := ni (⊤_ C),
  truth := mem (⊤_ C) ≫ (prod.right_unitor _).hom,
  truth_mono' := begin apply_instance end,
  classifier_of := λ U X f hf,
  begin
    haveI := hf,
    apply hat (f ≫ limits.prod.lift (𝟙 _) (terminal.from _))
  end,
  classifies' := λ U X f hf, @classifying_powers _ _ _ _ _ _ _ hf,
  uniquely' := λ U X f hf χ₁ k,
  begin
    haveI := hf,
    apply unique_hat,
    apply classifying_powers' f,
    exact k
  end
}

instance p_reflects_iso [has_power_objects.{v} C] : reflects_isomorphisms (P_functor : Cᵒᵖ ⥤ C) :=
{ reflects := λ A B f i,
  begin
    haveI := i,
    suffices: is_iso f.unop,
      refine ⟨this.inv.op, _, _⟩,
      dsimp, apply has_hom.hom.unop_inj, simp,
      dsimp, apply has_hom.hom.unop_inj, simp,
    apply @balanced _ 𝒞 _ _ _ _ _ _,
    { split,
      intros,
      apply p_faithful g h,
      erw [← cancel_mono (P_functor.map f), ← P_map_comp, w, P_map_comp],
      refl },
    { split,
      intros,
      apply p_faithful g h,
      erw [← cancel_epi (P_functor.map f), ← P_map_comp, w, P_map_comp],
      refl }
  end }

def exists_power {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] :
  internal_image f ≫ P_map f = 𝟙 (P A) :=
begin
  suffices: internal_image f ≫ P_map f = P_map (𝟙 _) ≫ internal_image (𝟙 _),
    rwa [P_map_id, internal_image_map_id, id_comp] at this,
  apply beck_chevalley rfl _,
  apply pullback_of_mono
end

instance fin_category_op (J : Type v) [small_category J] [fcj : fin_category J] : fin_category Jᵒᵖ :=
{ decidable_eq_obj := by { intros x y, rw ← opposite.unop_inj_iff x y, apply_instance },
  fintype_obj :=
    { elems := finset.map ⟨opposite.op, opposite.op_inj⟩ fcj.fintype_obj.elems,
      complete :=
      begin
        intro x,
        rw finset.mem_map,
        use x.unop,
        split,
        apply fcj.fintype_obj.complete,
        refl
      end },
  decidable_eq_hom :=
  begin
    intros x y f g,
    have: f.unop = g.unop ↔ f = g := ⟨@has_hom.hom.unop_inj _ _ _ _ f g, λ t, _⟩,
    rw ← this, apply_instance,
    congr, assumption
  end,
  fintype_hom := λ X Y,
  { elems := begin have f: (opposite.unop Y ⟶ opposite.unop X) ↪ (X ⟶ Y) := ⟨has_hom.hom.op, has_hom.hom.op_inj⟩, have q := (@fin_category.fintype_hom J _ fcj Y.unop X.unop).elems, exact finset.map f q, end,
    complete := begin intro f, simp, use f.unop, split, apply (@fin_category.fintype_hom J _ fcj Y.unop X.unop).complete, refl end } }

lemma unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [epi f] : mono f.unop :=
⟨λ Z g h eq, has_hom.hom.op_inj ((cancel_epi f).1 (has_hom.hom.unop_inj eq))⟩

instance pare [has_power_objects.{v} C] : monadic_right_adjoint (P_functor : Cᵒᵖ ⥤ C) :=
{ to_is_right_adjoint := self_adj,
  eqv :=
  begin
    apply reflexive_monadicity_theorem _ _ p_reflects_iso,
    { intros _ _ _ _ _, apply_instance },
    { rintros B' A' f' g' ⟨r', rf, rg⟩,
      refine { preserves := λ c t, _ },
      let e : c.X.unop ⟶ A'.unop := (cofork.π c).unop,
      haveI : split_mono g'.unop := ⟨r'.unop, by simpa using rg⟩,
      have : epi (cofork.π c) := epi_of_is_colimit_parallel_pair t,
      haveI : mono e := unop_mono_of_epi _,
      have : internal_image g'.unop ≫ P_map f'.unop = P_map e ≫ internal_image e := beck_chevalley _ _,
      apply colimit_of_splits (functor.map_cocone P_functor c) (internal_image e) (internal_image g'.unop) (exists_power e) (exists_power g'.unop) this,
        rw [← unop_comp, ← cofork.condition c], refl,
      refine is_limit.mk' _ (λ s, _),
      have equal_legs : pullback_cone.fst s = pullback_cone.snd s,
        simpa [← unop_comp, rf, rg] using pullback_cone.condition s =≫ r'.unop,
      have make_w: f' ≫ has_hom.hom.op (pullback_cone.fst s) = g' ≫ has_hom.hom.op (pullback_cone.fst s),
        apply has_hom.hom.unop_inj, dsimp, rw [pullback_cone.condition s, equal_legs],
      let q := cofork.of_π (pullback_cone.fst s).op make_w,
      have fac : (t.desc q).unop ≫ e = pullback_cone.fst s,
        erw [← unop_comp, t.fac q walking_parallel_pair.one], refl,
      refine ⟨(t.desc q).unop, fac, equal_legs ▸ fac, λ m m₁ m₂, _⟩,
      refine has_hom.hom.op_inj (t.hom_ext (cofork.coequalizer_ext c _)),
      rw [has_hom.hom.op_unop, is_colimit.fac],
      apply has_hom.hom.unop_inj m₁ }
  end }

@[simps]

instance some_colims (J : Type v) [small_category J] [has_power_objects.{v} C] [has_limits_of_shape Jᵒᵖ C] : has_colimits_of_shape J C :=
{ has_colimit := λ F, by exactI
  begin
    suffices: has_colimit (F ⋙ op_op_equivalence.inverse),
      apply adjunction.has_colimit_of_comp_equivalence F op_op_equivalence.inverse,
    let F'' : Jᵒᵖ ⥤ Cᵒᵖ := (F ⋙ op_op_equivalence.inverse).left_op,
    suffices : has_limit F'',
      apply limits.has_colimit_of_has_limit_left_op,
    suffices : has_limit (F'' ⋙ P_functor),
      apply monadic_creates_limits F'' P_functor,
    apply_instance
  end }

def has_colim [has_power_objects.{v} C] : has_finite_colimits.{v} C :=
{ has_colimits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI { has_colimit := λ F, by apply_instance } }

namespace intersect

def intersection {A : C} : sub A → sub A → sub A :=
begin
  refine quotient.lift (λ (f : sub' A), _) _,
  { exact (@postcompose _ _ _ _ f.1.hom f.2 ∘ sub_map f.1.hom) },
  { rintros a b ⟨⟨ab, hab⟩, ⟨ba, hba⟩⟩,
    ext x,
    apply quotient.induction_on x,
    intro y,
    dsimp [postcompose, sub_map],
    apply quotient.sound,
    split,
    { refine ⟨pullback.lift pullback.fst (pullback.snd ≫ ab) _, _⟩,
      { slice_rhs 2 3 {rw ← hab},
        apply pullback.condition },
      { dsimp,
        slice_rhs 1 2 {rw limit.lift_π},
        simp [hab] } },
    { refine ⟨pullback.lift pullback.fst (pullback.snd ≫ ba) (by simp [pullback.condition, hba]), _⟩,
      { dsimp,
        slice_rhs 1 2 {rw limit.lift_π},
        simp [hba] } } }
end

def is_le_left {A : C} : ∀ (m n : sub A), intersection m n ≤ m :=
begin
  apply quotient.ind₂,
  intros m n,
  exact ⟨pullback.snd, rfl⟩,
end

def is_le_right {A : C} : ∀ (m n : sub A), intersection m n ≤ n :=
begin
  apply quotient.ind₂,
  intros m n,
  exact ⟨pullback.fst, pullback.condition.symm⟩,
end

def universal {A : C} : ∀ {k m n : sub A}, k ≤ m → k ≤ n → k ≤ intersection m n :=
begin
  intros k m n,
  apply quotient.induction_on₃ k m n,
  clear k m n,
  intros k m n,
  rintros ⟨km, hkm⟩ ⟨kn, hkn⟩,
  refine ⟨pullback.lift kn km (eq.trans hkn.symm hkm), _⟩,
  dsimp,
  simp [hkm]
end

variables {A : C} [has_power_object.{v} A]

def intersect_names {B : C} (mn : B ⟶ P A ⨯ P A) : B ⟶ P A :=
hat_sub $ intersection (hat_sub' (mn ≫ limits.prod.fst)) (hat_sub' (mn ≫ limits.prod.snd))

def intersect_prop {X Y : C} (g : X ⟶ Y) (f1 f2 : sub Y) :
  sub_map g (intersection f1 f2) = intersection (sub_map g f1) (sub_map g f2) :=
begin
  revert f1 f2,
  apply quotient.ind₂,
  intros f1 f2,
  dsimp [sub_map, intersection, postcompose, pullback_sub', postcompose_sub'],
  apply quotient.sound,
  refine ⟨_, _⟩,
  { refine ⟨_, _⟩,
    { apply pullback.lift (pullback.lift (pullback.fst ≫ pullback.fst) pullback.snd _) _ _,
      { slice_lhs 2 3 {rw pullback.condition},
        conv_rhs {rw ← pullback.condition} },
      { apply pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd _,
        conv_rhs {rw ← pullback.condition},
        simp },
    { simp } },
    { dsimp,
      slice_rhs 1 2 {rw limit.lift_π},
      dsimp,
      rw limit.lift_π,
      refl } },
  { refine ⟨_, _⟩,
    { apply pullback.lift (pullback.lift (pullback.fst ≫ pullback.fst) (pullback.snd ≫ pullback.fst) _) _ _,
      { slice_lhs 2 3 {rw pullback.condition},
        slice_rhs 2 3 {rw pullback.condition},
        slice_lhs 1 2 {rw pullback.condition},
        simp },
      { apply pullback.snd ≫ pullback.snd },
      { slice_lhs 1 2 {rw limit.lift_π},
        dsimp,
        slice_lhs 2 3 {rw pullback.condition},
        simp } },
    { simp } }
end

def intersect_names_natural {B B' : C} (f : B' ⟶ B) (mn : B ⟶ P A ⨯ P A) :
  f ≫ intersect_names mn = intersect_names (f ≫ mn) :=
begin
  dunfold intersect_names,
  rw hat_sub_natural_left,
  congr' 1,
  rw category.assoc f mn _,
  rw category.assoc f mn _,
  rw hat_sub'_natural_left (mn ≫ limits.prod.fst),
  rw hat_sub'_natural_left (mn ≫ limits.prod.snd),
  apply intersect_prop
end

def intersect (A : C) [has_power_object.{v} A] : P A ⨯ P A ⟶ P A := intersect_names (𝟙 _)

end intersect

-- def hat_sub_natural_left (A B B' : C) [has_power_object.{v} A] (k : sub (B ⨯ A)) (g : B' ⟶ B) : g ≫ hat_sub k = hat_sub (sub_map (limits.prod.map g (𝟙 A)) k) :=
-- begin
--   apply quotient.induction_on k,
--   dsimp [hat_sub, sub_map], intro a,
--   rw hat_natural_left
-- end

-- def power_obj_of_biject (A : C) (PA : C) (bij : Π B, sub (B ⨯ A) ≃ (B ⟶ PA))
--   (nat : ∀ B B' f k, f ≫ bij B k = bij B' (sub_map (limits.prod.map f (𝟙 A)) k)) :
--   has_power_object.{v} A :=
-- begin
--   refine ⟨PA, _, _, _, _, _, _⟩,
--   let r := ((bij PA).symm (𝟙 PA)),
--   have := nat _ _ (𝟙 PA) r,
--   rw id_comp at this,

-- end

-- This should land in mathlib soon so it's sorry for now.
@[priority 10000] instance [has_finite_limits.{v} C] {B : C} : has_finite_limits.{v} (over B) :=
begin
  haveI := has_finite_wide_pullbacks_of_has_finite_limits C,
  apply over.has_finite_limits,
end

def P1 (A : C) [has_power_object.{v} A] : C := equalizer (intersect.intersect A) limits.prod.fst
def P1sub (A : C) [has_power_object.{v} A] : P1 A ⟶ P A ⨯ P A := equalizer.ι (intersect.intersect A) limits.prod.fst
instance P1submono (A : C) [has_power_object.{v} A] : mono (P1sub A) := equalizer.ι_mono

section slicing

lemma leq_prop' (A B : C) (m n : sub (B ⨯ A)) [has_power_object.{v} A] :
  m ≤ n ↔ limits.prod.lift (hat_sub m) (hat_sub n) ≫ intersect.intersect A = limits.prod.lift (hat_sub m) (hat_sub n) ≫ limits.prod.fst :=
begin
  have: m ≤ n ↔ intersect.intersection m n = m,
    refine ⟨λ k, le_antisymm (intersect.is_le_left _ _) (intersect.universal (le_refl _) k), λ k, _⟩,
    convert intersect.is_le_right m n,
    exact k.symm,
  erw [this, prod.lift_fst, intersect.intersect_names_natural, comp_id, intersect.intersect_names,
       prod.lift_fst, prod.lift_snd],
  conv_rhs {congr, congr, congr, apply_congr hat_sub''.right_inv, apply_congr hat_sub''.right_inv },
  exact ⟨congr_arg hat_sub, λ k, function.injective_of_left_inverse hat_sub''.right_inv k⟩,
end

lemma leq_prop (A B R₁ R₂ : C) [has_power_object.{v} A] (m : R₁ ⟶ B ⨯ A) (n : R₂ ⟶ B ⨯ A) [mono m] [mono n] [has_power_object.{v} A] :
  (∃ (k : R₁ ⟶ R₂), m = k ≫ n) ↔ limits.prod.lift (hat m) (hat n) ≫ intersect.intersect A = limits.prod.lift (hat m) (hat n) ≫ limits.prod.fst :=
leq_prop' _ _ ⟦⟨over.mk m, _inst_3⟩⟧ ⟦⟨over.mk n, _inst_4⟩⟧

variables {B : C} (f g : over B)

set_option trace.app_builder false


def over_mono {B : C} {f g : over B} (m : f ⟶ g) [mono m] : mono m.left :=
begin
  refine ⟨λ A h k e, _⟩,
  let A' : over B := over.mk (k ≫ f.hom),
  have: h ≫ f.hom = k ≫ f.hom,
    rw ← over.w m, rw reassoc_of e,
  let h' : A' ⟶ f := over.hom_mk h,
  let k' : A' ⟶ f := over.hom_mk k,
  have: h' ≫ m = k' ≫ m,
    ext, dsimp, exact e,
  rw cancel_mono m at this,
  injection this
end

def over_mono' {B : C} {f g : over B} (m : f ⟶ g) [mono m.left] : mono m :=
{right_cancellation := λ A h k e, over.over_morphism.ext ((cancel_mono m.left).1 (congr_arg comma_morphism.left e))}

def reflect_pullback (P Q R S : over B) (f : P ⟶ Q) (g : Q ⟶ S) (h : P ⟶ R) (k : R ⟶ S)
  (comm : f ≫ g = h ≫ k) (t : is_limit (pullback_cone.mk f.left h.left (begin exact congr_arg comma_morphism.left comm end))) :
is_limit (pullback_cone.mk f h comm) :=
begin
  apply is_limit.mk',
  intro s,
  let s' : pullback_cone g.left k.left := pullback_cone.mk (pullback_cone.fst s).left (pullback_cone.snd s).left (congr_arg comma_morphism.left (pullback_cone.condition s)),
  refine ⟨over.hom_mk (t.lift s') _, _, _, _⟩,
  dsimp, change t.lift s' ≫ P.hom = _, rw ← over.w f, slice_lhs 1 2 {erw t.fac _ walking_cospan.left}, exact over.w (pullback_cone.fst s),
  ext1, dsimp, exact t.fac _ walking_cospan.left,
  ext1, dsimp, exact t.fac _ walking_cospan.right,
  intros m m₁ m₂,
  ext1,
  dsimp,
  refine t.hom_ext _,
  apply pullback_cone.equalizer_ext (pullback_cone.mk f.left h.left _),
  erw t.fac _ walking_cospan.left,
  exact congr_arg comma_morphism.left m₁,
  erw t.fac _ walking_cospan.right,
  exact congr_arg comma_morphism.left m₂,
end

def preserve_pullback {P Q R S : over B} {f : P ⟶ Q} {g : Q ⟶ S} {h : P ⟶ R} {k : R ⟶ S}
  {comm : f ≫ g = h ≫ k} (t : is_limit (pullback_cone.mk f h comm)) :
is_limit (pullback_cone.mk f.left h.left (begin exact congr_arg comma_morphism.left comm end)) :=
begin
  apply is_limit.mk',
  intro s,
  let sX' : over B := over.mk (pullback_cone.snd s ≫ R.hom),
  have: pullback_cone.fst s ≫ Q.hom = pullback_cone.snd s ≫ R.hom,
    rw [← over.w g, pullback_cone.condition_assoc s, over.w k],
  let fst' : sX' ⟶ Q := over.hom_mk (pullback_cone.fst s) (by assumption),
  let snd' : sX' ⟶ R := over.hom_mk (pullback_cone.snd s),
  have comm': fst' ≫ g = snd' ≫ k,
    ext, dsimp, apply pullback_cone.condition s,
  let q : sX' ⟶ P := t.lift (pullback_cone.mk fst' snd' comm'),
  have qf : q ≫ f = fst' := t.fac _ walking_cospan.left,
  have qh : q ≫ h = snd' := t.fac _ walking_cospan.right,
  refine ⟨q.left, congr_arg comma_morphism.left qf, congr_arg comma_morphism.left qh, _⟩,
  intros m m₁ m₂,
  have z: m ≫ P.hom = pullback_cone.snd s ≫ R.hom,
  { rw [← over.w h, ← m₂, assoc], refl },
  let m' : sX' ⟶ P := over.hom_mk m (by apply z),
  have: m' = q,
    apply t.hom_ext,
    refine pullback_cone.equalizer_ext (pullback_cone.mk f h comm) _ _,
    { erw qf,
      ext,
      dsimp,
      erw m₁ },
    { erw qh,
      ext,
      dsimp,
      erw m₂ },
  apply congr_arg comma_morphism.left this,
end

def vpaste {U V W X Y Z : C} (f : U ⟶ V) (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z)
  (up_comm : f ≫ h = g ≫ k) (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm))
  (up_pb : is_limit (pullback_cone.mk _ _ up_comm)) :
  is_limit (pullback_cone.mk f (g ≫ l) (by rw [reassoc_of up_comm, down_comm, assoc]) : pullback_cone (h ≫ m) n):=
is_limit.mk' _ $
begin
  intro s,
  let c' : pullback_cone m n := pullback_cone.mk (pullback_cone.fst s ≫ h) (pullback_cone.snd s) (by simp [pullback_cone.condition s]),
  let t : s.X ⟶ W := down_pb.lift c',
  have tl : t ≫ l = pullback_cone.snd s := down_pb.fac c' walking_cospan.right,
  have tk : t ≫ k = pullback_cone.fst s ≫ h := down_pb.fac c' walking_cospan.left,
  let c'' : pullback_cone h k := pullback_cone.mk (pullback_cone.fst s) t tk.symm,
  let u : s.X ⟶ U := up_pb.lift c'',
  have uf : u ≫ f = pullback_cone.fst s := up_pb.fac c'' walking_cospan.left,
  have ug : u ≫ g = t := up_pb.fac c'' walking_cospan.right,
  refine ⟨u, uf, by erw [reassoc_of ug, tl], _⟩,
  intros m' m₁ m₂,
  apply up_pb.hom_ext,
  apply pullback_cone.equalizer_ext (pullback_cone.mk f g up_comm),
  change m' ≫ f = u ≫ f,
  erw [m₁, uf],
  erw ug,
  apply down_pb.hom_ext,
  apply pullback_cone.equalizer_ext (pullback_cone.mk _ _ down_comm),
  { change (m' ≫ g) ≫ k = t ≫ k,
    slice_lhs 2 3 {rw ← up_comm},
    slice_lhs 1 2 {erw m₁},
    rw tk },
  { change (m' ≫ g) ≫ l = t ≫ l,
    erw [assoc, m₂, tl] }
end

variables [has_power_object.{v} B] [has_power_object.{v} f.left]

@[reducible]
def bottom : P f.left ⨯ B ⟶ P f.left ⨯ P f.left := limits.prod.map (𝟙 _) (singleton_arrow B ≫ P_map f.hom)

def Q : C := pullback (P1sub f.left) (bottom f)
def hk : Q f ⟶ P f.left ⨯ B := pullback.snd
def k : Q f ⟶ B        := hk f ≫ limits.prod.snd
def h : Q f ⟶ P f.left := hk f ≫ limits.prod.fst
def over_pow : over B  := over.mk (k f)

def up : C := pullback (mem f.left) (limits.prod.map (h f) (𝟙 f.left))
@[reducible]
def h' : up f ⟶ Q f ⨯ f.left := pullback.snd
instance : mono (h' f) := by apply_instance
instance : mono (hk f) := pullback.snd_of_mono

def hat_h' : hat (h' f) = h f :=
begin
  symmetry,
  apply unique_hat,
  refine ⟨_, _, cone_is_pullback _ _⟩,
end

@[reducible]
def over.ni (f : over B) [has_power_object.{v} B] [has_power_object.{v} f.left] : over B :=
@over.mk _ _ B (up f) (h' f ≫ limits.prod.snd ≫ f.hom)

def prop (f : over B) [has_power_object.{v} B] [has_power_object.{v} f.left] :
  ∃ q, h' f = q ≫ (pullback.snd : pullback (prod.lift f.hom (𝟙 f.left)) (limits.prod.map ((k f) : _ ⟶ B) (𝟙 f.left)) ⟶ _) :=
begin
  have: pullback.fst ≫ P1sub f.left = limits.prod.lift (h f) (k f ≫ singleton_arrow B ≫ P_map f.hom),
    rw pullback.condition,
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, h, hk, limits.prod.map_fst, comp_id] },
    { rw [assoc, prod.lift_snd, k, hk, limits.prod.map_snd, assoc] },
  rw [← seven_six_two, hat_natural_left, ← hat_h' f] at this,
  have: limits.prod.lift (hat (h' f)) (hat pullback.snd) ≫ intersect.intersect f.left = limits.prod.lift (hat (h' f)) (hat pullback.snd) ≫ limits.prod.fst,
    rw ← this,
    erw [assoc, assoc, equalizer.condition], refl,
  rw ← leq_prop at this,
  exact this
end

@[reducible]
def over.mem : over.ni f ⟶ (over_pow f) ⨯ f :=
begin
  apply prod.lift _ _,
  apply over.hom_mk _ _,
  exact h' f ≫ limits.prod.fst,
  dsimp [over_pow, over.ni, hk],
  change (((h' f : up f ⟶ _) ≫ (limits.prod.fst : Q f ⨯ f.left ⟶ Q f)) : _ ⟶ Q f) ≫ (k f : Q f ⟶ B) =
    (h' f : up f ⟶ Q f ⨯ f.left) ≫ (limits.prod.snd : Q f ⨯ f.left ⟶ f.left) ≫ (f.hom : f.left ⟶ B),
  obtain ⟨q, hq⟩ := prop f,
  have z : (pullback.fst : pullback (prod.lift f.hom (𝟙 f.left)) (limits.prod.map ((k f) : _ ⟶ B) (𝟙 f.left)) ⟶ _) ≫ _ = _ ≫ _ := pullback.condition,
    have z₁ := z =≫ limits.prod.fst,
    rw [assoc, prod.lift_fst, assoc, limits.prod.map_fst] at z₁,
    have z₂ := z =≫ limits.prod.snd,
    erw [assoc, assoc, prod.lift_snd, limits.prod.map_snd, comp_id, comp_id] at z₂,
    rw [hq, assoc, assoc, ← z₁, z₂, assoc, assoc],
  apply over.hom_mk _ _,
  exact h' f ≫ limits.prod.snd,
  simp only [assoc, auto_param_eq], refl,
end
instance over.mem_mono : mono (over.mem f) :=
begin
  refine ⟨λ Z p q eq, _⟩,
  ext1,
  rw ← cancel_mono (h' f),
  apply prod.hom_ext,
  rw [assoc, assoc],
  have e₁ := eq =≫ limits.prod.fst,
  rw [assoc, assoc, prod.lift_fst] at e₁,
  exact congr_arg comma_morphism.left e₁,
  have e₂ := eq =≫ limits.prod.snd,
  rw [assoc, assoc, prod.lift_snd] at e₂,
  rw [assoc, assoc],
  exact congr_arg comma_morphism.left e₂,
end

section hat

variables {f g}
variables {r : over B} (m : r ⟶ g ⨯ f) [mono m]

@[reducible]
def m' : r.left ⟶ (g ⨯ f).left := m.left
instance : mono (m' m) := over_mono m

def m'' : r.left ⟶ g.left ⨯ f.left := m' m ≫ magic_arrow f g
instance : mono (m'' m) :=
begin
  rw m'',
  apply_instance
end
@[reducible]
def mhat : g.left ⟶ P f.left := hat (m'' m)
@[reducible]
def l : g.left ⟶ P f.left ⨯ P f.left := prod.lift (mhat m) g.hom ≫ bottom f
lemma l_eq : l m = prod.lift (hat (m'' m)) (g.hom ≫ (singleton_arrow B : B ⟶ P B) ≫ P_map f.hom) :=
begin
 apply prod.hom_ext,
  { rw [prod.lift_fst, assoc, limits.prod.map_fst, comp_id, prod.lift_fst] },
  { rw [prod.lift_snd, assoc, limits.prod.map_snd, prod.lift_snd_assoc] },
end

lemma llem : l m ≫ intersect.intersect f.left = l m ≫ limits.prod.fst :=
begin
  have := l_eq m,
  erw [← seven_six_two, hat_natural_left] at this,
  rw [this, ← leq_prop],
  refine ⟨_, _⟩,
  { apply pullback.lift (m'' m ≫ limits.prod.snd) (m'' m) _,
    apply prod.hom_ext,
    { erw [assoc, assoc, assoc, assoc, m'', assoc, prod.lift_fst, limits.prod.map_fst],
      slice_lhs 2 3 {rw prod.lift_snd},
      slice_rhs 2 3 {rw prod.lift_fst},
      rw over.w (limits.prod.fst : g ⨯ f ⟶ g),
      rw over.w (limits.prod.snd : g ⨯ f ⟶ f) },
    { erw [assoc, assoc, assoc, assoc, assoc, prod.lift_snd, comp_id, limits.prod.map_snd, comp_id] } },
  { rw limit.lift_π, refl }
end
@[reducible]
def top : g.left ⟶ P1 f.left := equalizer.lift (l m) (llem m)
@[reducible]
def h'' : g.left ⟶ Q f := pullback.lift (top m) (prod.lift (mhat m) g.hom) (limit.lift_π _ _)
@[reducible]
def make_arrow : g ⟶ over_pow f := over.hom_mk (h'' m) $ by { dsimp [over_pow, hk, k], simp }
@[reducible]
def square_top (m : r ⟶ g ⨯ f) [mono m] : r ⟶ over.ni f :=
begin
  refine over.hom_mk (pullback.lift (square.top (m'' m)) _ _) _,
  { apply (m'' m) ≫ limits.prod.map (h'' m) (𝟙 _) },
  { rw square.commutes (m'' m), conv_rhs {rw [assoc, ← prod_functorial]}, congr' 2,
    erw [h, hk, limit.lift_π_assoc, prod.lift_fst] },
  { dsimp [h'], erw [limit.lift_π_assoc, assoc, limits.prod.map_snd_assoc, id_comp],
    erw [← over.w m, assoc, prod.lift_snd_assoc, over.w (limits.prod.snd : g ⨯ f ⟶ f)] }
end
def alt_square_commutes : square_top m ≫ over.mem f ≫ limits.prod.fst = (m ≫ limits.prod.fst) ≫ make_arrow m :=
begin
  rw [assoc, over.mem, prod.lift_fst, make_arrow],
  ext1,
  dsimp [h', m'', magic_arrow],
  rw limit.lift_π_assoc,
  dsimp,
  rw [assoc, limits.prod.map_fst, assoc, prod.lift_fst_assoc]
end
def square_commutes : square_top m ≫ over.mem f = m ≫ limits.prod.map (make_arrow m) (𝟙 _) :=
begin
  apply prod.hom_ext,
  { rw [assoc, alt_square_commutes, assoc, assoc, limits.prod.map_fst] },
  { rw [assoc, over.mem, prod.lift_snd, assoc, limits.prod.map_snd, comp_id],
    ext1,
    dsimp,
    rw limit.lift_π_assoc,
    dsimp,
    rw [assoc, limits.prod.map_snd, comp_id],
    simp [m''] }
end

def alt_square_pb : is_limit (pullback_cone.mk _ _ (alt_square_commutes m)) :=
begin
  apply reflect_pullback,
  dsimp [square_top],
  refine is_limit.mk' _ _,
  intro s,
  have lem : (pullback_cone.fst s ≫ pullback.fst) ≫ mem f.left =
    prod.lift (pullback_cone.snd s) (pullback_cone.fst s ≫ pullback.fst ≫ mem f.left ≫ limits.prod.snd) ≫
      limits.prod.map (hat (m'' m)) (𝟙 f.left),
  { apply prod.hom_ext,
    { rw [assoc, assoc, assoc, limits.prod.map_fst, prod.lift_fst_assoc,
          category_theory.limits.pullback.condition_assoc, limits.prod.map_fst],
      have : pullback_cone.fst s ≫ (over.mem f ≫ _).left = _ := pullback_cone.condition s,
      rw prod.lift_fst at this,
      dsimp [h'] at this,
      slice_lhs 1 3 {rw this},
      rw [assoc, h, hk],
      slice_lhs 2 3 {rw limit.lift_π},
      dsimp,
      rw prod.lift_fst },
    { rw [assoc, assoc, assoc, limits.prod.map_snd, comp_id, prod.lift_snd] } },
  let t : s.X ⟶ r.left := (square.is_pullback (m'' m)).lift (pullback_cone.mk _ _ lem),
  have t₃ : t ≫ m'' m ≫ limits.prod.fst = pullback_cone.snd s,
    rw ← assoc,
    erw (square.is_pullback (m'' m)).fac (pullback_cone.mk _ _ lem) walking_cospan.right,
    dsimp,
    rw prod.lift_fst,
  have t₂ : t ≫ m'' m ≫ limits.prod.snd = pullback_cone.fst s ≫ pullback.fst ≫ mem f.left ≫ limits.prod.snd,
    rw ← assoc,
    erw (square.is_pullback (m'' m)).fac (pullback_cone.mk _ _ lem) walking_cospan.right,
    dsimp,
    rw prod.lift_snd,
  have t₁: t ≫ square.top (m'' m) = pullback_cone.fst s ≫ pullback.fst,
    erw (square.is_pullback (m'' m)).fac (pullback_cone.mk _ _ lem) walking_cospan.left,
    refl,
  refine ⟨t, _, _, _⟩,
  { change t ≫ pullback.lift (square.top (m'' m)) (m'' m ≫ limits.prod.map (h'' m) (𝟙 f.left)) _ = s.π.app walking_cospan.left,
    apply pullback.hom_ext,
    { rw ← t₁, simp },
    { rw [assoc], slice_lhs 2 3 {rw limit.lift_π},
      dsimp,
      apply prod.hom_ext,
      { rw [assoc, assoc, limits.prod.map_fst],
        slice_lhs 1 3 {rw t₃},
        rw ← pullback_cone.condition s,
        rw assoc,
        change pullback_cone.fst s ≫ (over.mem f ≫ limits.prod.fst).left = s.π.app walking_cospan.left ≫ pullback.snd ≫ limits.prod.fst,
        erw prod.lift_fst,
        refl },
      { rw [assoc, assoc, limits.prod.map_snd, comp_id, t₂,
            category_theory.limits.pullback.condition_assoc, limits.prod.map_snd,
            comp_id, assoc] } } },
  { dunfold pullback_cone.snd,
    dsimp,
    rw [m'', assoc, magic_arrow, prod.lift_fst] at t₃,
    exact t₃ },
  { intros t' m₁ m₂,
    have m₁' : t' ≫ pullback.lift (square.top (m'' m)) (m'' m ≫ limits.prod.map (h'' m) (𝟙 f.left)) _ =
    pullback_cone.fst s := m₁,
    have m₂' : t' ≫ m.left ≫ _ = pullback_cone.snd s := m₂,
    clear m₁ m₂,
    rw ← cancel_mono (m'' m),
    change t' ≫ m' m ≫ magic_arrow f g = t ≫ m' m ≫ magic_arrow f g,
    apply prod.hom_ext,
    { rw [assoc, assoc],
      slice_lhs 3 4 {rw prod.lift_fst},
      rw m₂',
      rw ← t₃,
      rw assoc, refl },
    { conv_rhs {erw [assoc, t₂, ← m₁']},
      rw [assoc, assoc, assoc],
      slice_rhs 2 3 {rw limit.lift_π},
      dsimp,
      rw square.commutes (m'' m),
      rw [assoc, limits.prod.map_snd, comp_id],
      simp [m''] } }
end

end hat

def main (f : over B) [has_power_object.{v} f.left] : has_power_object.{v} f :=
{ PA := over_pow f,
  niA := over.ni f,
  memA := over.mem f,
  mem_mono' := over.mem_mono f,
  hat := λ b r m hm, by exactI make_arrow m,
  powerises' := λ g r m hm, by exactI
  begin
    refine ⟨square_top m, square_commutes m, _⟩,
    apply is_limit.mk' _ _,
    intro s,
    have comm : pullback_cone.fst s ≫ over.mem f ≫ limits.prod.fst = (pullback_cone.snd s ≫ limits.prod.fst) ≫ make_arrow m,
      rw [pullback_cone.condition_assoc s, limits.prod.map_fst, assoc],
    let s' := pullback_cone.mk _ _ comm,
    let t := (alt_square_pb m).lift s',
    have t₁ : t ≫ square_top m = pullback_cone.fst s' := (alt_square_pb m).fac s' walking_cospan.left,
    have t₂ : t ≫ m ≫ limits.prod.fst = pullback_cone.snd s' := (alt_square_pb m).fac s' walking_cospan.right,
    have t₃ := t₁ =≫ over.mem f,
      rw [assoc, square_commutes m] at t₃,
    replace t₃ := t₃ =≫ limits.prod.snd,
    rw [assoc, assoc, assoc, limits.prod.map_snd, comp_id] at t₃,
    refine ⟨(alt_square_pb m).lift s', (alt_square_pb m).fac s' walking_cospan.left, _, _⟩,
    { change t ≫ m = pullback_cone.snd s,
      apply prod.hom_ext,
      { rw [assoc, t₂], refl },
      { rw [assoc, t₃], erw [pullback_cone.condition_assoc s, limits.prod.map_snd, comp_id] } },
    { intros t' m₁ m₂,
      apply (alt_square_pb m).hom_ext,
      apply pullback_cone.equalizer_ext (pullback_cone.mk (square_top m) (m ≫ limits.prod.fst) _),
      erw t₁,
      exact m₁,
      erw [t₂, ← assoc, m₂], refl }
  end,
  uniquely' := λ g r m hm hat' p, by exactI
  begin
    ext1,
    rw ← cancel_mono (hk f),
    have z₁: hat'.left ≫ k f = g.hom := over.w hat',
    suffices z₂: hat'.left ≫ h f = (make_arrow m).left ≫ h f,
      apply prod.hom_ext,
      { erw [assoc, assoc, z₂], refl },
      { erw [assoc, z₁, make_arrow, limit.lift_π, prod.lift_snd] },
    erw [make_arrow, limit.lift_π_assoc, prod.lift_fst],
    apply unique_hat,
    rcases p with ⟨_, _, _⟩,
    have pc₁ := p_commutes =≫ limits.prod.fst,
      rw [assoc, assoc, limits.prod.map_fst, over.mem, prod.lift_fst] at pc₁,
      replace pc₁ : _ = _ := congr_arg comma_morphism.left pc₁,
      rw [over.comp_left, over.hom_mk_left, over.comp_left, over.comp_left] at pc₁,
    have pc₂ := p_commutes =≫ limits.prod.snd,
      rw [assoc, assoc, limits.prod.map_snd, over.mem, prod.lift_snd, comp_id] at pc₂,
      replace pc₂ : _ = _ := congr_arg comma_morphism.left pc₂,
      rw [over.comp_left, over.hom_mk_left, over.comp_left] at pc₂,
    have pc : p_top.left ≫ pullback.snd = m'' m ≫ limits.prod.map hat'.left (𝟙 f.left),
      apply prod.hom_ext,
      { rw [assoc, assoc, limits.prod.map_fst, pc₁, m'', assoc, prod.lift_fst_assoc] },
      { rw [assoc, assoc, pc₂, limits.prod.map_snd, comp_id, m'', assoc, prod.lift_snd] },

    refine ⟨p_top.left ≫ pullback.fst, _, _⟩,
    { rw [assoc, pullback.condition, prod_functorial, reassoc_of pc] },

    have z := preserve_pullback p_forms_pullback',
    convert (pasting p_top.left pullback.fst (m'' m) (h' f) (mem f.left) (limits.prod.map hat'.left (𝟙 f.left)) _ _ pullback.condition (cone_is_pullback _ _)).inv _,
    { rw prod_functorial },
    { rw prod_functorial },
    { exact pc },
    have: h' f = (over.mem f).left ≫ magic_arrow f (over_pow f),
    { apply prod.hom_ext,
      { rw [assoc, prod.lift_fst, ← over.comp_left, prod.lift_fst], refl },
      { rw [assoc, prod.lift_snd, ← over.comp_left, prod.lift_snd], refl } },
    convert vpaste p_top.left (m' m) (over.mem f).left _ (magic_arrow _ _) (magic_arrow _ _) _ _ _ _ z,
    { apply prod.hom_ext,
      { rw [assoc, prod.lift_fst, ← over.comp_left, assoc, limits.prod.map_fst, limits.prod.map_fst, prod.lift_fst_assoc], refl },
      { rw [assoc, prod.lift_snd, ← over.comp_left, limits.prod.map_snd, assoc, limits.prod.map_snd, prod.lift_snd_assoc], refl } },
    apply magic_pb,
  end

}

end slicing