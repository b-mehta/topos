/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.types
import pullbacks
import to_mathlib
import sub

/-!
# Power objects

Define power objects
-/
universes v u

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

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

instance has_power_object_of_has_all [has_power_objects.{v} C] {A : C} :
  has_power_object.{v} A := has_power_objects.has_power_object A

variable [has_power_objects.{v} C]

def P (A : C) : C := @has_power_object.PA _ 𝒞 _ A _
def ni (A : C) : C := @has_power_object.niA _ 𝒞 _ A _
def mem (A : C) : ni A ⟶ P A ⨯ A := has_power_object.memA A
def hat {A B R : C} (m : R ⟶ B ⨯ A) [hm : mono m] : B ⟶ P A := has_power_object.hat m
instance mem_mono (A : C) : mono (mem A) := has_power_object.mem_mono' A
def hat_powerises {A B R : C} (m : R ⟶ B ⨯ A) [mono m] : powerises (mem A) m (hat m) := has_power_object.powerises' m
def square.top {A B R : C} (m : R ⟶ B ⨯ A) [mono m] : R ⟶ ni A := (hat_powerises m).top
def square.commutes {A B R : C} (m : R ⟶ B ⨯ A) [mono m] : square.top m ≫ mem A = m ≫ limits.prod.map (hat m) (𝟙 A) := (hat_powerises m).commutes
def square.is_pullback {A B R : C} (m : R ⟶ B ⨯ A) [mono m] : is_limit (pullback_cone.mk _ _ (square.commutes m)) := (hat_powerises m).forms_pullback
lemma unique_hat {A B R : C} (m : R ⟶ B ⨯ A) [mono m] (hat' : B ⟶ P A) (hp : powerises (mem A) m hat') : hat' = hat m := has_power_object.uniquely' m hat' hp

variables {A B : C} (f : A ⟶ B)
def E : C := pullback (mem B) (limits.prod.map (𝟙 _) f)
def Emap : E f ⟶ P B ⨯ A := pullback.snd
instance : mono (Emap f) := pullback.snd_of_mono

lemma Esquare : (pullback.fst : E f ⟶ _) ≫ mem B = Emap f ≫ limits.prod.map (𝟙 _) f := pullback.condition
lemma cone_is_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : is_limit (pullback_cone.mk _ _ pullback.condition : pullback_cone f g) :=
begin
  apply is_limit.of_iso_limit,
  apply limit.is_limit,
  refine cones.ext _ _, refl,
  intro j,
  erw id_comp,
  cases j, refl, refl,
  rw limit.cone_π,
  erw ← limit.w (cospan _ _) walking_cospan.hom.inl,
  refl
end
lemma Epb : is_limit (pullback_cone.mk _ _ (Esquare f)) :=
cone_is_pullback _ _

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
  set p : pullback m (limits.prod.map (𝟙 D) f) ⟶ R := pullback.fst,
  set q : pullback m (limits.prod.map (𝟙 D) f) ⟶ D ⨯ A := pullback.snd,
  have := (pasting pullback.fst _ pullback.snd m _ (limits.prod.map (𝟙 D) f) _ pullback.condition (square.commutes m) (square.is_pullback m)).inv (cone_is_pullback _ _),
  have comm'': limits.prod.map (𝟙 D) f ≫ limits.prod.map (hat m) (𝟙 B) = _ := prod_map_comm _ _,
  set f2 : pullback m (limits.prod.map (𝟙 D) f) ⟶ P B ⨯ A := q ≫ limits.prod.map (hat m) (𝟙 A),
  set f1 : pullback m (limits.prod.map (𝟙 D) f) ⟶ ni B := p ≫ square.top m,
  have comm: f1 ≫ mem B = f2 ≫ limits.prod.map (𝟙 (P B)) f,
    slice_rhs 2 3 {rw comm''.symm},
    slice_lhs 2 3 {rw square.commutes m},
    slice_lhs 1 2 {rw pullback.condition},
    rw ← assoc,
  have comm' : f1 ≫ mem B = pullback.snd ≫ limits.prod.map (hat m) (𝟙 A) ≫ limits.prod.map (𝟙 (P B)) f,
    rw comm, rw assoc,
  have newlim: is_limit (pullback_cone.mk f1 pullback.snd comm' : pullback_cone (mem B) (limits.prod.map (hat m) (𝟙 A) ≫ limits.prod.map (𝟙 (P B)) f)),
    convert this using 2, exact comm''.symm, exact comm''.symm,
  set r := pullback.lift f1 f2 comm,
  have comm''' : r ≫ Emap f = q ≫ limits.prod.map (hat m) (𝟙 A),
    erw limit.lift_π, refl,
  have := (pasting r pullback.fst q (Emap f) (mem B) (limits.prod.map (hat m) (𝟙 A)) (limits.prod.map (𝟙 (P B)) f) comm''' pullback.condition (Epb f)).hom _,
    swap, convert newlim using 2, erw limit.lift_π, refl,
  have := (pasting r (square.top (Emap f)) q (Emap f) (mem A) (limits.prod.map (hat m) (𝟙 A)) (limits.prod.map (P_map f) (𝟙 A)) comm''' (Psquare f) (square.is_pullback _)).inv this,
  have comm4: limits.prod.map (hat m) (𝟙 A) ≫ limits.prod.map (P_map f) (𝟙 A) = limits.prod.map (hat m ≫ P_map f) (𝟙 A),
    apply prod.hom_ext,
    simp, simp, erw comp_id,
  refine ⟨r ≫ square.top (Emap f), _, _⟩,
    slice_lhs 2 3 {rw square.commutes},
    slice_lhs 1 2 {rw comm'''},
    slice_lhs 2 3 {erw comm4},
  convert this using 2,
  exact comm4.symm,
  exact comm4.symm
end

lemma lifting {A B R₁ R₂ : C} {g₁ : R₁ ⟶ B ⨯ A} {g₂ : R₂ ⟶ B ⨯ A} [mono g₁] [mono g₂] (hom : R₁ ⟶ R₂) (inv : R₂ ⟶ R₁) :
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
  slice_lhs 2 3 {rw square.commutes g₁},
  slice_lhs 1 2 {rw ← l},
  apply is_limit.of_iso_limit (square.is_pullback g₁),
  ext, swap,
  refine ⟨hom, inv, ‹_›, ‹_›⟩,
  cases j, simp, slice_rhs 1 2 {rw hi},
  erw id_comp,
  simpa,
  simp, show _ ≫ _ = _ ≫ _ ≫ _, slice_rhs 1 2 {rw hi},
  erw id_comp
end
lemma liftable {A B : C} (a b : sub' (B ⨯ A)) : (a ≈ b) → (@hat _ _ _ _ _ _ _ a.1.hom a.2 = @hat _ _ _ _ _ _ _ b.1.hom b.2) :=
begin
  rintros ⟨⟨hom, k⟩, ⟨inv, l⟩⟩,
  exact @lifting _ _ _ _ _ _ _ _ _ _ a.2 b.2 _ _ k l,
end
def hat_sub {A B : C} : sub (B ⨯ A) → (B ⟶ P A) :=
quotient.lift (λ (f : sub' (B ⨯ A)), @hat _ _ _ _ _ _ _ f.1.hom f.2) liftable

def hat_sub' {A B : C} (k : B ⟶ P A) : sub (B ⨯ A) :=
quotient.mk ⟨over.mk (pullback.snd : pullback (mem A) (limits.prod.map k (𝟙 _)) ⟶ B ⨯ A), pullback.snd_of_mono⟩

def hat_sub'' {A B : C} : (B ⟶ P A) ≃ sub (B ⨯ A) :=
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
  end
}

lemma P_map_id (X : C) : P_map (𝟙 X) = 𝟙 (P X) :=
begin
  symmetry, apply unique_hat,
  refine ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩
end
lemma P_map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : P_map (f ≫ g) = P_map g ≫ P_map f :=
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

def P_functor : Cᵒᵖ ⥤ C :=
{ obj := λ X, P X.unop,
  map := λ X Y f, P_map f.unop,
  map_id' := λ X, P_map_id _,
  map_comp' := λ X Y Z f g, P_map_comp _ _ }

def self_adj : is_right_adjoint (@P_functor C 𝒞 _ _) :=
{ left := P_functor.right_op,
  adj := adjunction.mk_of_hom_equiv
  { hom_equiv :=
    begin
      intros A B,
      apply equiv.trans _ hat_sub''.symm,
      rw functor.right_op_obj,
      apply equiv.trans (op_equiv _ _) _,
      apply equiv.trans hat_sub'',
      show sub (opposite.unop B⨯A) ≃ sub (A⨯opposite.unop B),
      -- should be easy with preserves_iso now!
    end

  }
}