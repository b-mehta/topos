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
import over
import category_theory.limits.opposites
import category_theory.limits.over
import category_theory.epi_mono
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers
import adjoint_lifting
import locally_cartesian_closed

/-!
# Power objects

Define power objects.
Show that power objects induces a (contravariant) functor `P_functor`.
Show that this is self-adjoint on the right.
Define the singleton arrow {} : B ⟶ PB and internal image (for monos only)
and show the latter is functorial too.
Show the existence of a subobject classifier and show

-/
universes v u v₂ u₂

open category_theory category_theory.category category_theory.limits

attribute [instance] has_pullbacks_of_has_finite_limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_finite_limits.{v} C]

abbreviation powerises {A PA niA B R : C} (memA : niA ⟶ PA ⨯ A) (m : R ⟶ B ⨯ A) (mhat : B ⟶ PA) :=
has_pullback_top m (limits.prod.map mhat (𝟙 A)) memA

instance {A PA niA B R : C} (memA : niA ⟶ PA ⨯ A) [mono memA] (m : R ⟶ B ⨯ A) (mhat : B ⟶ PA) :
  subsingleton (powerises memA m mhat) :=
⟨by { intros P Q, cases P, cases Q, congr, rw [← cancel_mono memA, P_comm, Q_comm] }⟩

structure is_power_object {A PA niA : C} (memA : niA ⟶ PA ⨯ A) :=
(is_mono : mono memA)
(hat : ∀ {B R} (m : R ⟶ B ⨯ A) [@mono _ 𝒞 _ _ m], B ⟶ PA)
(powerises' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m], powerises memA m (hat m))
(uniquely' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : @mono _ 𝒞 _ _ m] (hat' : B ⟶ PA), powerises memA m hat' → hat' = hat m)

class has_power_object (A : C) :=
(PA niA : C)
(memA : niA ⟶ PA ⨯ A)
(is_power : is_power_object memA)

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

def power_is_power : is_power_object (mem A) := has_power_object.is_power

instance mem_mono : mono (mem A) := (power_is_power A).is_mono

variables {A} {B R : C} (m : R ⟶ B ⨯ A) [mono m]

def hat : B ⟶ P A := (power_is_power A).hat m
def hat_powerises : powerises (mem A) m (hat m) := (power_is_power A).powerises' m
def square.top : R ⟶ ni A := (hat_powerises m).top
@[reassoc]
def square.commutes : square.top m ≫ mem A = m ≫ limits.prod.map (hat m) (𝟙 A) := (hat_powerises m).comm
def square.is_pullback : is_limit (pullback_cone.mk _ _ (square.commutes m)) := (hat_powerises m).is_pb
lemma unique_hat (hat' : B ⟶ P A) (hp : powerises (mem A) m hat') : hat' = hat m := (power_is_power A).uniquely' m hat' hp
end convenience

lemma P_unique_aux {A : C} {PA₁ niA₁ PA₂ niA₂ : C}
  (memA₁ : niA₁ ⟶ PA₁ ⨯ A) (memA₂ : niA₂ ⟶ PA₂ ⨯ A)
  (h₁ : is_power_object memA₁) (h₂ : is_power_object memA₂) :
@is_power_object.hat _ _ _ _ _ _ _ h₁ _ _ memA₂ h₂.is_mono ≫ @is_power_object.hat _ _ _ _ _ _ _ h₂ _ _ memA₁ h₁.is_mono = 𝟙 PA₂ :=
begin
  haveI := h₂.is_mono,
  haveI := h₁.is_mono,
  have: h₂.hat memA₂ = 𝟙 _,
  { symmetry,
    apply h₂.uniquely',
    change has_pullback_top _ _ _,
    rw prod_map_id_id,
    apply top_iso_has_pullback_top (𝟙 _),
    rw [id_comp, comp_id] },
  rw ← this,
  apply h₂.uniquely',
  change has_pullback_top _ _ _,
  rw prod_functorial,
  apply left_right_hpb_to_both_hpb _ (h₁.powerises' memA₂) (h₂.powerises' memA₁),
end

def P_unique_up_to_iso {A : C} {PA₁ niA₁ PA₂ niA₂ : C}
  {memA₁ : niA₁ ⟶ PA₁ ⨯ A} {memA₂ : niA₂ ⟶ PA₂ ⨯ A}
  (h₁ : is_power_object memA₁) (h₂ : is_power_object memA₂) :
PA₁ ≅ PA₂ :=
{ hom := by { haveI := h₁.is_mono, exact h₂.hat memA₁ },
  inv := by { haveI := h₂.is_mono, exact h₁.hat memA₂ },
  hom_inv_id' := P_unique_aux memA₂ memA₁ h₂ h₁,
  inv_hom_id' := P_unique_aux memA₁ memA₂ h₁ h₂ }

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

def hat_natural_left {A B B' R : C} [has_power_object.{v} A] (k : R ⟶ B ⨯ A) [mono k] (g : B' ⟶ B) :
  g ≫ hat k = hat (pullback.snd : pullback k (limits.prod.map g (𝟙 A)) ⟶ B' ⨯ A) :=
begin
  apply unique_hat,
  change has_pullback_top _ _ _,
  rw prod_functorial,
  apply left_right_hpb_to_both_hpb _ has_pullback_top_of_pb (hat_powerises k),
end

lemma easy_lemma {D R : C} (m : R ⟶ D ⨯ B) [hm : mono m] :
  hat (pullback.snd : pullback m (limits.prod.map (𝟙 D) f) ⟶ D ⨯ A) = hat m ≫ P_map f :=
begin
  symmetry,
  apply unique_hat,
  change has_pullback_top _ _ _,
  rw prod_functorial,
  apply left_right_hpb_to_both_hpb _ _ (has_pullback_top_of_is_pb (Ppb f)),
  apply right_both_hpb_to_left_hpb _ has_pullback_top_of_pb,
  rw ← prod_map_comm,
  apply left_right_hpb_to_both_hpb m has_pullback_top_of_pb (hat_powerises _),
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
{ top := square.top (f ≫ prod.lift (𝟙 X) (terminal.from X)),
  comm :=
  begin
    rw ← assoc,
    rw square.commutes (f ≫ limits.prod.lift (𝟙 X) (terminal.from X)),
    simp, erw id_comp,
  end,
  is_pb :=
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
  set top := k.top,
  have comm: top ≫ _ = _ ≫ _ := k.comm,
  have pb: is_limit (pullback_cone.mk _ _ comm) := k.is_pb,
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

variable (C)
def weak_topos_has_subobj [has_power_object.{v} (⊤_ C)] : has_subobject_classifier.{v} C :=
{ Ω := P (⊤_ C),
  Ω₀ := ni (⊤_ C),
  truth := mem (⊤_ C) ≫ (prod.right_unitor _).hom,
  truth_mono' := by apply_instance,
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
variable {C}

instance p_reflects_iso [has_power_objects.{v} C] : reflects_isomorphisms (P_functor : Cᵒᵖ ⥤ C) :=
{ reflects := λ A B f i,
  begin
    haveI := i,
    suffices: is_iso f.unop,
      refine ⟨this.inv.op, _, _⟩,
      dsimp, apply has_hom.hom.unop_inj, simp,
      dsimp, apply has_hom.hom.unop_inj, simp,
    haveI := weak_topos_has_subobj C,
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
        refine ⟨x.unop, by apply fcj.fintype_obj.complete, rfl⟩
      end },
  decidable_eq_hom :=
  begin
    intros x y f g,
    have: f.unop = g.unop ↔ f = g := ⟨@has_hom.hom.unop_inj _ _ _ _ f g, λ t, _⟩,
    rw ← this, apply_instance,
    congr, assumption
  end,
  fintype_hom := λ X Y,
  { elems :=
    begin
      have f: (opposite.unop Y ⟶ opposite.unop X) ↪ (X ⟶ Y) := ⟨has_hom.hom.op, has_hom.hom.op_inj⟩,
      exact (@fin_category.fintype_hom J _ fcj Y.unop X.unop).elems.map f,
    end,
    complete :=
    begin
      intro f,
      rw [finset.map_val, function.embedding.coe_fn_mk, multiset.mem_map],
      refine ⟨f.unop, by apply (@fin_category.fintype_hom J _ fcj Y.unop X.unop).complete, rfl⟩,
    end } }

instance pare [has_power_objects.{v} C] : monadic_right_adjoint (P_functor : Cᵒᵖ ⥤ C) :=
{ to_is_right_adjoint := self_adj,
  eqv :=
  begin
    apply reflexive_monadicity_theorem _ _ p_reflects_iso,
    { intros _ _ _ _ _, apply_instance },
    { rintros B' A' f' g' ⟨r', rf, rg⟩,
      refine { preserves := λ c t, _ },
      let e : c.X.unop ⟶ A'.unop := (cofork.π c).unop,
      haveI : split_mono g'.unop := ⟨r'.unop, by { rw [auto_param_eq, ← unop_comp, rg], refl }⟩,
      have : epi (cofork.π c) := epi_of_is_colimit_parallel_pair t,
      haveI : mono e := category_theory.unop_mono_of_epi _,
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
      exact has_hom.hom.unop_inj m₁ }
  end }

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

variables {A : C} [has_power_object.{v} A]

def intersect_names {B : C} (mn : B ⟶ P A ⨯ P A) : B ⟶ P A :=
hat_sub $ hat_sub' (mn ≫ limits.prod.fst) ⊓ hat_sub' (mn ≫ limits.prod.snd)

def intersect_prop {X Y : C} (g : X ⟶ Y) (f1 f2 : sub Y) :
  sub_map g (f1 ⊓ f2) = sub_map g f1 ⊓ sub_map g f2 :=
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
        conv_rhs {rw ← pullback.condition},
        refl },
      { apply pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd _,
        conv_rhs {rw ← pullback.condition},
        rw [assoc], refl },
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
        slice_lhs 1 2 {erw pullback.condition},
        simp },
      { apply pullback.snd ≫ pullback.snd },
      { dsimp,
        rw pullback.lift_snd_assoc,
        slice_lhs 2 3 {rw pullback.condition},
        simp } },
    { dsimp, rw pullback.lift_snd } }
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
  have: m ≤ n ↔ intersection m n = m,
    refine ⟨λ k, le_antisymm (is_le_left _ _) (universal (le_refl _) k), λ k, _⟩,
    convert is_le_right m n,
    exact k.symm,
  erw [this, prod.lift_fst, intersect.intersect_names_natural, comp_id, intersect.intersect_names,
       prod.lift_fst, prod.lift_snd],
  conv_rhs {congr, congr, congr, apply_congr hat_sub''.right_inv, apply_congr hat_sub''.right_inv },
  exact ⟨congr_arg hat_sub, λ k, hat_sub''.right_inv.injective k⟩,
end

lemma leq_prop (A B R₁ R₂ : C) [has_power_object.{v} A] (m : R₁ ⟶ B ⨯ A) (n : R₂ ⟶ B ⨯ A) [mono m] [mono n] :
  (∃ (k : R₁ ⟶ R₂), m = k ≫ n) ↔ limits.prod.lift (hat m) (hat n) ≫ intersect.intersect A = limits.prod.lift (hat m) (hat n) ≫ limits.prod.fst :=
leq_prop' _ _ ⟦⟨over.mk m, _inst_3⟩⟧ ⟦⟨over.mk n, _inst_4⟩⟧

variables {B : C} (f g : over B)

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
instance : mono (m' m) := category_theory.over_mono m

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

def main' (f : over B) [has_power_object.{v} f.left] : is_power_object (over.mem f) :=
{ is_mono := over.mem_mono f,
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
    change has_pullback_top _ _ _,
    rw prod_functorial,
    apply left_right_hpb_to_both_hpb (h' f) _ has_pullback_top_of_pb,
    have: h' f = (over.mem f).left ≫ magic_arrow f (over_pow f),
    { apply prod.hom_ext,
      { rw [assoc, prod.lift_fst, ← over.comp_left, prod.lift_fst], refl },
      { rw [assoc, prod.lift_snd, ← over.comp_left, prod.lift_snd], refl } },
    rw this,
    apply stretch_hpb_down _ _ (limits.prod.map hat' (𝟙 f)).left _ _ _ _ _ (magic_pb _ _ f hat'),
    apply over_forget_preserves_hpb _ _ _ p,
  end }

def main (f : over B) [has_power_object.{v} f.left] : has_power_object.{v} f :=
{ PA := over_pow f,
  niA := over.ni f,
  memA := over.mem f,
  is_power := main' f }

end slicing

instance fundamental_theorem (B : C) [has_power_objects.{v} C] : has_power_objects.{v} (over B) :=
{ has_power_object := λ f, main f }

def comparison [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) (h : Π (J : Type v) [small_category J] [fin_category J], preserves_limits_of_shape J F)
  (A : C) : F.obj (P A) ⟶ P (F.obj A) :=
begin
  let m := F.map (mem A) ≫ (mult_comparison F (P A) A).hom,
  letI : mono (F.map (mem A)) := preserves_mono_of_preserves_pullback F _ _ _,
  exact hat m,
end

def comp_natural' [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) (h : Π (J : Type v) [small_category J] [fin_category J], preserves_limits_of_shape J F)
  (A B : C) (f : B ⟶ A) :
  F.map (P_map f) ≫ comparison F h B = comparison F h A ≫ P_map (F.map f) :=
begin
  dsimp [comparison],
  rw [hat_natural_left, hat_natural_right],
  let m₁ := F.map (mem A) ≫ (mult_comparison F (P A) A).hom,
  let m₂ := F.map (mem B) ≫ (mult_comparison F (P B) B).hom,
  letI : mono (F.map (mem A)) := preserves_mono_of_preserves_pullback F _ _ _,
  letI : mono (F.map (mem B)) := preserves_mono_of_preserves_pullback F _ _ _,
  letI : mono (F.map (Emap f)) := preserves_mono_of_preserves_pullback F _ _ _,
  let P₁ := pullback (F.map (mem B) ≫ (mult_comparison F (P B) B).hom) (limits.prod.map (F.map (P_map f)) (𝟙 (F.obj B))),
  let P₂ := pullback (F.map (mem A) ≫ (mult_comparison F (P A) A).hom) (limits.prod.map (𝟙 _) (F.map f)),
  let h₁ : P₁ ⟶ _ := pullback.snd,
  let h₂ : P₂ ⟶ _ := pullback.snd,
  change hat h₁ = hat h₂,
  let s₁ := Ppb f,
  let s₂ := Epb f,
  let Fs₁ := preserves_pullback_cone F _ _ _ _ _ s₁,
  let Fs₂ := preserves_pullback_cone F _ _ _ _ _ s₂,
  have s₃comm : F.map (limits.prod.map (P_map f) (𝟙 B)) ≫ (mult_comparison F (P B) B).hom = (mult_comparison F (P A) B).hom ≫ limits.prod.map (F.map (P_map f)) (𝟙 (F.obj B)),
    rw [mult_comparison, mult_comparison],
    apply prod.hom_ext,
    { erw [assoc, prod.lift_fst, assoc, limits.prod.map_fst, ← F.map_comp, limits.prod.map_fst, prod.lift_fst_assoc, F.map_comp] },
    { erw [assoc, prod.lift_snd, assoc, limits.prod.map_snd, comp_id, ← F.map_comp, limits.prod.map_snd, comp_id, prod.lift_snd] },
  let s₃ := pullback_square_iso (F.map (limits.prod.map (P_map f) (𝟙 _))) (mult_comparison F (P A) B).hom (mult_comparison F (P B) B).hom (limits.prod.map (F.map (P_map f)) (𝟙 _)) s₃comm,
  let Fs₁s₃ := vpaste _ _ _ _ _ _ _ _ _ s₃ Fs₁,
  have eq₁: hat h₁ = hat (F.map (Emap f) ≫ (mult_comparison F (P A) B).hom),
  { apply lifting _ _ _ _,
    { apply Fs₁s₃.lift (limit.cone _) },
    { apply limit.lift _ (pullback_cone.mk (F.map (square.top (Emap f))) (F.map (Emap f) ≫ (mult_comparison F (P A) B).hom) _),
      rw [assoc, ← s₃comm, ← assoc, ← F.map_comp, square.commutes, F.map_comp, assoc], refl },
    { exact (Fs₁s₃.fac (limit.cone _) walking_cospan.right).symm },
    { rw limit.lift_π, refl } },
  have s₄comm : F.map (limits.prod.map (𝟙 (P A)) f) ≫ (mult_comparison F (P A) A).hom = (mult_comparison F (P A) B).hom ≫ limits.prod.map (𝟙 (F.obj (P A))) (F.map f),
    rw [mult_comparison, mult_comparison],
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, assoc, limits.prod.map_fst, ← F.map_comp, limits.prod.map_fst, comp_id, comp_id, prod.lift_fst] },
    { rw [assoc, prod.lift_snd, assoc, limits.prod.map_snd, ← F.map_comp, limits.prod.map_snd, prod.lift_snd_assoc, F.map_comp] },
  let s₄ := pullback_square_iso (F.map (limits.prod.map (𝟙 _) f)) (mult_comparison F (P A) B).hom (mult_comparison F (P A) A).hom (limits.prod.map (𝟙 _) (F.map f)) s₄comm,
  let Fs₂s₄ := vpaste _ _ _ _ _ _ _ _ _ s₄ Fs₂,
  have eq₂: hat h₂ = hat (F.map (Emap f) ≫ (mult_comparison F (P A) B).hom),
  { apply lifting _ _ _ _,
    { apply Fs₂s₄.lift (limit.cone _) },
    { apply limit.lift _ (pullback_cone.mk (F.map pullback.fst) (F.map (Emap f) ≫ (mult_comparison F (P A) B).hom) _),
      rw [assoc, ← s₄comm, ← assoc, ← F.map_comp, pullback.condition, F.map_comp, assoc], refl },
    { exact (Fs₂s₄.fac (limit.cone _) walking_cospan.right).symm },
    { rw limit.lift_π, refl } },
  rw [eq₁, eq₂],
end

-- Define F as a logical functor if this is an iso.
def comp_natural [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) [h : Π (J : Type v) [small_category J] [fin_category J], preserves_limits_of_shape J F] :
  (P_functor ⋙ F) ⟶ (F.op ⋙ P_functor) :=
{ app := λ A, comparison F h A.unop,
  naturality' := λ A B g, comp_natural' F h A.unop B.unop g.unop }

def star_power (A B : C) [has_power_object.{v} A] : (star B).obj (ni A) ⟶ (star B).obj (P A) ⨯ (star B).obj A :=
begin
  haveI := adjunction.right_adjoint_preserves_limits (forget_adj_star B),
  exact (star B).map (mem A) ≫ (mult_comparison (star B) (P A) A).hom
end
instance (A B : C) [has_power_object.{v} A] : mono (star_power A B) :=
begin
  haveI : mono ((star B).map (mem A)) := right_adjoint_preserves_mono (forget_adj_star B) (by apply_instance),
  rw star_power,
  apply_instance
end

def alt_prod (A : C) {B : C} (g : over B) : over B := over.mk ((limits.prod.fst : g.left ⨯ A ⟶ g.left) ≫ g.hom)

@[simps]
def the_iso (A : C) {B : C} (g : over B) : g ⨯ (star B).obj A ≅ alt_prod A g :=
{ hom :=
  begin
    apply over.hom_mk _ _,
    apply prod.lift (limits.prod.fst : g ⨯ _ ⟶ _).left _,
    refine (limits.prod.snd : g ⨯ _ ⟶ _).left ≫ limits.prod.snd,
    erw limit.lift_π_assoc,
    exact over.w (limits.prod.fst : g ⨯ (star B).obj A ⟶ _),
  end,
  inv :=
  begin
    apply prod.lift,
    refine over.hom_mk limits.prod.fst rfl,
    refine over.hom_mk (limits.prod.map g.hom (𝟙 _)) (limits.prod.map_fst _ _),
  end,
  hom_inv_id' :=
  begin
    ext1,
    dsimp,
    rw ← cancel_mono (magic_arrow ((star B).obj A) g),
    rw id_comp,
    apply prod.hom_ext,
    rw [prod.lift_fst, assoc, prod.lift_fst, assoc, ← over.comp_left, prod.lift_fst, over.hom_mk_left, prod.lift_fst],
    rw [prod.lift_snd, assoc, prod.lift_snd, assoc, ← over.comp_left, prod.lift_snd, over.hom_mk_left],
    apply prod.hom_ext,
    rw [assoc, limits.prod.map_fst, prod.lift_fst_assoc, over.w (limits.prod.fst : g ⨯ (star B).obj A ⟶ _)],
    exact (over.w (limits.prod.snd : g ⨯ (star B).obj A ⟶ _)).symm,
    rw [assoc, limits.prod.map_snd, prod.lift_snd_assoc, comp_id],
  end,
  inv_hom_id' :=
  begin
    ext,
    dsimp,
    rw [assoc, prod.lift_fst, ← over.comp_left, prod.lift_fst, id_comp], refl,
    rw [over.comp_left, assoc, over.hom_mk_left, prod.lift_snd, ← assoc, ← over.comp_left,
        prod.lift_snd, over.hom_mk_left, limits.prod.map_snd, over.id_left, id_comp, comp_id],
  end }


def star_hat {A B : C} [has_power_object.{v} A] {g r : over B} (m : r ⟶ g ⨯ (star B).obj A) (k : g.left ⟶ P A) [mono m] : g ⟶ (star B).obj (P A):=
over.hom_mk (prod.lift g.hom k) (limit.lift_π _ _)

def seven_eleven_r_comm (A B : C) [has_power_object.{v} A] :
  𝟙 (B ⨯ _) ≫ limits.prod.map (𝟙 _) (mem A) = (star_power A B ≫ (the_iso A ((star B).obj (P A))).hom).left ≫ (prod.associator B (P A) A).hom :=
begin
  dsimp [star_power, the_iso, mult_comparison],
  rw [assoc, assoc, id_comp],
  apply prod.hom_ext,
  rw [assoc, assoc, assoc, prod.lift_fst, prod.lift_fst_assoc, limits.prod.map_fst, comp_id],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_fst, over.hom_mk_left, ← assoc, ← prod_functorial', limits.prod.map_fst, comp_id],
  rw [assoc, assoc, assoc, prod.lift_snd, limits.prod.map_snd],
  apply prod.hom_ext,
  rw [assoc, assoc, assoc, assoc, prod.lift_fst, prod.lift_fst_assoc],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_fst, over.hom_mk_left, ← assoc, ← assoc, ← prod_functorial', limits.prod.map_snd, assoc],
  rw [assoc, assoc, assoc, assoc, prod.lift_snd, prod.lift_snd],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_snd, over.hom_mk_left, ← assoc, ← assoc, ← prod_functorial', limits.prod.map_snd, assoc],
end

def seven_eleven_aux (A B : C) [has_power_object.{v} A] (g r : over B) (m : r ⟶ g ⨯ (star B).obj A) [mono m] (k : g.left ⟶ P A) :
  powerises (mem A) (m ≫ (the_iso A g).hom).left k ≅ powerises (star_power A B) m (star_hat m k) :=
begin
  have bottom_comm :
    limits.prod.map (star_hat m k) (𝟙 _) ≫ (the_iso A _).hom =
    (the_iso A g).hom ≫ over.hom_mk (limits.prod.map (prod.lift g.hom k) (𝟙 A))
      (by { dsimp, erw [limits.prod.map_fst_assoc, limits.prod.lift_fst], refl }),
  { dsimp [the_iso], ext : 2,
    { rw [over.comp_left, over.comp_left, over.hom_mk_left, assoc, prod.lift_fst,
          ← over.comp_left, limits.prod.map_fst, over.comp_left, star_hat, over.hom_mk_left,
          over.hom_mk_left, over.hom_mk_left, prod.lift_map, prod.lift_fst] },
    { rw [over.comp_left, over.comp_left, over.hom_mk_left, assoc, prod.lift_snd, ← assoc,
          ← over.comp_left, limits.prod.map_snd, comp_id, over.hom_mk_left, over.hom_mk_left,
          prod.lift_map, comp_id, prod.lift_snd] } },

  have b_pb : is_limit (pullback_cone.mk _ _ bottom_comm) := pullback_square_iso _ _ _ _ bottom_comm,
  have right₁_comm : 𝟙 (B ⨯ _) ≫ limits.prod.map (𝟙 _) (mem A) = (star_power A B ≫ (the_iso A ((star B).obj (P A))).hom).left ≫ (prod.associator B (P A) A).hom,
    apply seven_eleven_r_comm,
  have r₁_pb := pullback_square_iso' _ _ _ _ right₁_comm,
  have r₂_pb := pullback_prod' (mem A) B,
  have r_pb := (left_pb_to_both_pb _ _ _ _ _ _ _ _ _ r₁_pb) r₂_pb,
  have p : limits.prod.map (prod.lift g.hom k) (𝟙 A) ≫ (prod.associator B (P A) A).hom ≫ limits.prod.snd = limits.prod.map k (𝟙 A),
    erw [limits.prod.lift_snd],
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, limits.prod.map_fst, prod.map_fst_assoc, prod.lift_snd] },
    { rw [assoc, prod.lift_snd, limits.prod.map_snd, limits.prod.map_snd] },
  refine ⟨_, _, subsingleton.elim _ _, subsingleton.elim _ _⟩,
  { intro q,
    refine ⟨over.hom_mk (prod.lift r.hom q.top) (prod.lift_fst _ _), _, _⟩,
    { apply prod.hom_ext,
      { rw [assoc, star_power, mult_comparison, assoc, prod.lift_fst, assoc, limits.prod.map_fst,
            ← (star B).map_comp, star_hat],
        ext1,
        dsimp, apply prod.hom_ext,
        { rw [assoc, limits.prod.map_fst, comp_id, prod.lift_fst, assoc, assoc, prod.lift_fst,
              ← over.w m, ← over.w (limits.prod.fst : g ⨯ (star B).obj A ⟶ g)] },
        { rw [assoc, limits.prod.map_snd, assoc, assoc, prod.lift_snd, prod.lift_snd_assoc,
              reassoc_of q.comm, over.comp_left, limits.prod.map_fst, the_iso, assoc],
          dsimp, rw [prod.lift_fst_assoc] } },
      { rw [assoc, star_power, assoc, mult_comparison, prod.lift_snd, assoc, limits.prod.map_snd,
            comp_id, ← (star B).map_comp],
        ext1,
        dsimp, apply prod.hom_ext,
        { rw [assoc, limits.prod.map_fst, comp_id, prod.lift_fst, ← over.w m, assoc,
              ← over.w (limits.prod.snd : g ⨯ (star B).obj A ⟶ _)], refl },
        { rw [assoc, limits.prod.map_snd, prod.lift_snd_assoc, reassoc_of q.comm, over.comp_left,
              limits.prod.map_snd, comp_id, assoc, the_iso],
          dsimp, rw [prod.lift_snd, assoc] } } },
    refine vpaste' _ _ _ _ _ _ _ _ bottom_comm b_pb _,
    apply reflect_pullback,
    dsimp,
    apply (both_pb_to_left_pb _ _ _ _ _ _ _ _ _ r_pb) _,
    convert q.is_pb,
    rw [id_comp, prod.lift_snd] },
  { intro q,
    refine ⟨q.top.left ≫ (𝟙 _) ≫ limits.prod.snd, _, _⟩,
    { have q₁ := q.comm =≫ limits.prod.fst,
      have q₂ := q.comm =≫ limits.prod.snd,
      simp only [assoc, star_power, limits.prod.map_fst, mult_comparison,
                prod.lift_fst, limits.prod.map_snd, prod.lift_snd, comp_id, star_hat] at q₁ q₂,
      replace q₁ : (q.top.left ≫ limits.prod.map (𝟙 B) (mem A) ≫ limits.prod.map (𝟙 B) limits.prod.fst) ≫ _ = (m.left ≫ _ ≫ prod.lift g.hom k) ≫ _ := congr_arg comma_morphism.left q₁ =≫ limits.prod.snd,
      replace q₂ : (q.top.left ≫ limits.prod.map (𝟙 _) (mem A) ≫ limits.prod.map _ _) ≫ _ = (m.left ≫ _) ≫ _ := congr_arg comma_morphism.left q₂ =≫ limits.prod.snd,
      rw [← prod_functorial'] at q₁ q₂,
      rw [the_iso, id_comp, assoc, over.comp_left, assoc], dsimp,
      rw [prod.lift_map, comp_id],
      apply prod.hom_ext,
      simpa using q₁,
      simpa using q₂ },
    have pb := vpaste _ _ _ _ _ _ _ _ _ b_pb q.is_pb,
    have := p.symm,
    convert (left_pb_to_both_pb _ _ _ _ _ _ _ _ _) (preserve_pullback pb) r_pb }
end

def seven_eleven (A B : C) [has_power_object.{v} A] : is_power_object (star_power A B) :=
{ is_mono := by apply_instance,
  hat := λ g r m hm, by exactI over.hom_mk (prod.lift g.hom (hat (m ≫ (the_iso A g).hom).left)) (limit.lift_π _ _),
  powerises' := λ g r m hm, by exactI
  begin
    apply (seven_eleven_aux A B g r m (hat (m ≫ (the_iso A g).hom).left)).hom,
    exact hat_powerises (m ≫ (the_iso A g).hom).left,
  end,
  uniquely' := λ g r m hm hat' pow, by exactI
  begin
    ext,
    rw [over.hom_mk_left, prod.lift_fst, ← over.w hat'], refl,
    rw [over.hom_mk_left, prod.lift_snd],
    apply unique_hat,
    apply (seven_eleven_aux A B g r m (hat'.left ≫ limits.prod.snd)).inv,
    convert pow,
    rw [star_hat],
    ext,
    rw [over.hom_mk_left, prod.lift_fst, ← over.w hat'], refl,
    rw [over.hom_mk_left, prod.lift_snd]
  end }

def logical_star [has_power_objects.{v} C] (B : C) : P_functor ⋙ star B ≅ (star B).op ⋙ P_functor :=
begin
  apply nat_iso.of_components _ _,
  intro A,
  exact P_unique_up_to_iso (seven_eleven A.unop B) (power_is_power _),
  intros X Y g,
  haveI := adjunction.right_adjoint_preserves_limits (forget_adj_star B),
  have := comp_natural' (star B) _ X.unop Y.unop g.unop,
  convert this,
  apply_instance,
end

def cc_of_pow [has_power_objects.{v} C] : is_cartesian_closed.{v} C :=
{ cart_closed := λ B,
  begin
    haveI : is_right_adjoint (star B) := ⟨over.forget, forget_adj_star B⟩,
    have := monad.adjoint_lifting (logical_star B).symm (λ f g X Y r, by apply_instance),
    exact exponentiable_of_star_is_left_adj B left_adjoint_of_right_adjoint_op,
  end }

def lcc_of_pow [has_power_objects.{v} C] : is_locally_cartesian_closed.{v} C :=
{ overs_cc := λ B, cc_of_pow }

def subobj_hat {A B R : C} [exponentiable A] [has_subobject_classifier.{v} C] (m : R ⟶ B ⨯ A) [mono m] :
  B ⟶ A⟹subobj.Ω C :=
cart_closed.curry ((limits.prod.braiding _ _).inv ≫ subobj.classifier_of m)

def power_of_subobj (A : C) [exponentiable A] [has_subobject_classifier.{v} C] : has_power_object.{v} A :=
{ PA := A ⟹ subobj.Ω C,
  niA := pullback (subobj.truth C) ((limits.prod.braiding _ _).hom ≫ ev A _),
  memA := pullback.snd,
  is_power :=
  { is_mono := by apply_instance,
    hat := λ B R m hm, by exactI subobj_hat m,
    powerises' := λ B R m hm,
    begin
      haveI := hm,
      apply right_both_hpb_to_left_hpb _ has_pullback_top_of_pb,
      rw [braid_natural_assoc, subobj_hat, curry_eq, prod_functorial', assoc, ev_nat, ev_coev_assoc, iso.hom_inv_id_assoc],
      apply subobj.classifies m,
    end,
    uniquely' := λ B R m hm hat' p,
    begin
      rw [subobj_hat, eq_curry_iff, iso.eq_inv_comp],
      apply has_subobject_classifier.uniquely,
      change has_pullback_top _ _ _,
      rw [uncurry_eq, ← braid_natural_assoc],
      apply left_right_hpb_to_both_hpb pullback.snd p has_pullback_top_of_pb,
    end } }

instance topos_has_power [has_subobject_classifier.{v} C] [is_cartesian_closed.{v} C] : has_power_objects.{v} C :=
⟨λ A, power_of_subobj A⟩

instance topos_is_lcc [has_subobject_classifier.{v} C] [is_cartesian_closed.{v} C] : is_locally_cartesian_closed.{v} C :=
lcc_of_pow

instance topos_has_finite_colims [has_subobject_classifier.{v} C] [is_cartesian_closed.{v} C] : has_finite_colimits.{v} C :=
has_colim

def raise_le [has_subobject_classifier.{v} C] {B : C} {m₁ m₂ : sub' B} (h : m₁ ≤ m₂) : m₁.1.left ⟶ m₂.1.left :=
begin
  haveI := m₂.2,
  apply (subobj.square.is_pullback m₂.1.hom).lift (pullback_cone.mk (default _) m₁.1.hom _),
  cases h,
  rw [h_h, assoc, ← subobj.square.commutes m₂.1.hom, ← assoc, cancel_mono (subobj.truth C)],
  apply subsingleton.elim
end

@[reassoc] lemma raise_le_prop [has_subobject_classifier.{v} C] {B : C} {m₁ m₂ : sub' B} (h : m₁ ≤ m₂) : raise_le h ≫ m₂.1.hom = m₁.1.hom :=
begin
  haveI := m₂.2,
  apply (subobj.square.is_pullback m₂.1.hom).fac _ walking_cospan.right,
end

-- instance some_colims (J : Type v) [small_category J] [has_power_objects.{v} C] [has_limits_of_shape Jᵒᵖ C] : has_colimits_of_shape J C :=
-- { has_colimit := λ F, by exactI
--   begin
--     suffices: has_colimit (F ⋙ op_op_equivalence.inverse),
--       apply adjunction.has_colimit_of_comp_equivalence F op_op_equivalence.inverse,
--     let F'' : Jᵒᵖ ⥤ Cᵒᵖ := (F ⋙ op_op_equivalence.inverse).left_op,
--     suffices : has_limit F'',
--       apply limits.has_colimit_of_has_limit_left_op,
--     suffices : has_limit (F'' ⋙ P_functor),
--       apply monadic_creates_limits F'' P_functor,
--     apply_instance
--   end }

-- def has_colim [has_power_objects.{v} C] : has_finite_colimits.{v} C :=
-- { has_colimits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI { has_colimit := λ F, by apply_instance } }