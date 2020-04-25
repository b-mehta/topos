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
import category_theory.limits.shapes.equalizers

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

instance has_power_object_of_has_all [has_power_objects.{v} C] {A : C} :
  has_power_object.{v} A := has_power_objects.has_power_object A

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
def hat_natural_left {A B B' R : C} [has_power_object.{v} A] (k : R ⟶ B ⨯ A) [mono k] (g : B' ⟶ B) : g ≫ hat k = hat (pullback.snd : pullback k (limits.prod.map g (𝟙 A)) ⟶ B' ⨯ A) := -- hat_sub (sub_map (limits.prod.map g (𝟙 A)) k) :=
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

def singleton_arrow (A : C) [has_power_object.{v} A] : A ⟶ P A := hat (diagonal A)

lemma seven_six_one {A B : C} [has_power_object.{v} B] (f : A ⟶ B) : hat (limits.prod.lift (𝟙 A) f) = f ≫ singleton_arrow B :=
begin
  erw hat_natural_left,
  refine lifting (pullback.lift f (limits.prod.lift (𝟙 A) f) _) (pullback.snd ≫ limits.prod.fst) _ _,
  apply prod.hom_ext,
  simp, erw id_comp, simp, erw comp_id,
  simp, apply prod.hom_ext, simp,
  slice_rhs 3 4 {rw limit.lift_π},
  have: (_ ≫ diagonal B) ≫ _ = (_ ≫ limits.prod.map f (𝟙 B)) ≫ _ := pullback.condition =≫ limits.prod.fst,
  simp at this, erw ← this,
  have: (_ ≫ diagonal B) ≫ _ = (_ ≫ limits.prod.map f (𝟙 B)) ≫ _ := pullback.condition =≫ limits.prod.snd,
  simp at this, rw this, dsimp, rw comp_id
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
  simp at this, erw ← this,
  have: (_ ≫ diagonal B) ≫ _ = (_ ≫ limits.prod.map (𝟙 B) f) ≫ _ := pullback.condition =≫ limits.prod.fst,
  simp at this, rw this, dsimp, simp,
  simp
end

instance singleton_mono (A : C) [has_power_object.{v} A] : mono (singleton_arrow A) :=
begin
  split,
  intros,
  rw ← seven_six_one at w, rw ← seven_six_one at w,
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
lemma naturalish {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] {R D : C} (m : R ⟶ D ⨯ A) [mono m] :
  hat m ≫ internal_image f = hat (m ≫ limits.prod.map (𝟙 D) f) :=
begin
  rw internal_image,
  rw hat_natural_left,
  have comm: pullback.fst ≫ mem A = prod.lift (pullback.snd ≫ limits.prod.fst) (pullback.fst ≫ mem A ≫ limits.prod.snd) ≫ limits.prod.map (hat m) (𝟙 A),
  { have q: pullback.fst ≫ mem A ≫ limits.prod.map (𝟙 (P A)) f = pullback.snd ≫ limits.prod.map (hat m) (𝟙 B) := pullback.condition,
    have q1 := q =≫ limits.prod.fst,
    simp only [prod_left_def, map_pair_left, assoc, limit.map_π] at q1, erw comp_id at q1,
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
    simp at this, rwa [assoc, assoc, assoc],
  set l: X ⟶ D := t.lift (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2),
  have lprop₁: l ≫ h = π₁ ≫ mem A ≫ limits.prod.snd,
    exact t.fac (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2) walking_cospan.left,
  have lprop₂: l ≫ k = π₂ ≫ limits.prod.snd,
    exact t.fac (pullback_cone.mk (π₁ ≫ mem A ≫ limits.prod.snd) (π₂ ≫ limits.prod.snd) comm2) walking_cospan.right,
  have comm3: π₁ ≫ mem A ≫ limits.prod.fst = π₂ ≫ limits.prod.fst,
    have: (π₁ ≫ _) ≫ _ = (_ ≫ _) ≫ _ := pullback.condition =≫ limits.prod.fst,
    simp at this, erw [comp_id, comp_id] at this, assumption,
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
      let A := A'.unop,
      let B := B'.unop,
      let E := c.X.unop,
      let f : A ⟶ B := f'.unop,
      let g : A ⟶ B := g'.unop,
      let r : B ⟶ A := r'.unop,
      let e : E ⟶ A := (cofork.π c).unop,
      have comm: e ≫ f = e ≫ g,
        rw ← unop_comp, rw cofork.condition c, refl,
      have fr: f ≫ r = 𝟙 A,
        rw ← unop_comp, rw rf, refl,
      haveI : split_mono f := ⟨r, fr⟩,
      haveI : mono f := split_mono.mono f,
      have gr: g ≫ r = 𝟙 A,
        rw ← unop_comp, rw rg, refl,
      haveI : split_mono g := ⟨r, gr⟩,
      haveI: mono g := split_mono.mono g,
      have: epi (cofork.π c) := epi_of_is_colimit_parallel_pair t,
      haveI: mono e := unop_mono_of_epi _,
      have equal_legs: Π (s : pullback_cone g f), pullback_cone.fst s = pullback_cone.snd s,
        intro s,
        rw [← comp_id (pullback_cone.fst s), ← gr, ← assoc, pullback_cone.condition s, assoc, fr, comp_id],
      have make_w: Π (s : pullback_cone g f), f' ≫ has_hom.hom.op (pullback_cone.fst s) = g' ≫ has_hom.hom.op (pullback_cone.fst s),
        intro s,
        apply has_hom.hom.unop_inj, dsimp, rw pullback_cone.condition s, rw equal_legs s,
      let make_cofork: pullback_cone g f → cofork f' g' := λ s, cofork.of_π (pullback_cone.fst s).op (make_w s),
      have fac: Π (s : pullback_cone g f), (t.desc (make_cofork s)).unop ≫ e = pullback_cone.fst s,
        intro s,
        rw ← unop_comp, erw t.fac (make_cofork s) walking_parallel_pair.one, refl,
      have: is_limit (pullback_cone.mk e e comm.symm),
        refine pullback_cone.is_limit.mk _ _ _ _ _,
        { intro s, exact (t.desc (make_cofork s)).unop },
        { intro s, exact fac s },
        { intro s, exact (fac s).trans (equal_legs s) },
        { intros s m w, apply has_hom.hom.op_inj, dsimp,
          apply t.hom_ext,
          apply cofork.coequalizer_ext,
          rw is_colimit.fac,
          erw ← w walking_cospan.left,
          refl },
      have := beck_chevalley _ this,
      apply colimit_of_splits (functor.map_cocone P_functor c) (internal_image e) (internal_image g) (exists_power e) (exists_power g) this }
  end }

@[simps]


instance has_colim [has_power_objects.{v} C] : has_finite_colimits.{v} C :=
{ has_colimits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI
  { has_colimit := λ F,
    begin
      suffices: has_colimit (F ⋙ op_op_equivalence.inverse),
        apply adjunction.has_colimit_of_comp_equivalence F op_op_equivalence.inverse,
      let F'' : Jᵒᵖ ⥤ Cᵒᵖ := (F ⋙ op_op_equivalence.inverse).left_op,
      suffices : has_limit F'',
        apply limits.has_colimit_of_has_limit_left_op,
      haveI q : has_limit (F'' ⋙ P_functor) := has_limits_of_shape.has_limit _,
      apply monadic_creates_limits F'' P_functor,
    end } }

namespace intersect

variables (A : C) [has_power_object.{v} A]

@[reducible]
def π₁₃ : (P A ⨯ P A) ⨯ A ⟶ P A ⨯ A := limits.prod.map limits.prod.fst (𝟙 A)
@[reducible]
def π₂₃ : (P A ⨯ P A) ⨯ A ⟶ P A ⨯ A := limits.prod.map limits.prod.snd (𝟙 A)

def L1 : C := pullback (mem A) (π₁₃ A)
def R1 : C := pullback (mem A) (π₂₃ A)

@[reducible]
def left : L1 A ⟶ (P A ⨯ P A) ⨯ A := pullback.snd
def right : R1 A ⟶ (P A ⨯ P A) ⨯ A := pullback.snd

instance mono_right: mono (right A) :=
begin
  dunfold right,
  apply_instance
end

@[reducible]
def both : pullback (left A) (right A) ⟶ (P A ⨯ P A) ⨯ A := pullback.fst ≫ left A

def intersect : P A ⨯ P A ⟶ P A := hat (both A)

end intersect

-- lemma intersect_prop (R₁ R₂ : C) (f₁ : R₁ ⟶ B ⨯ A) (f₂ : R₂ ⟶ B ⨯ A) [mono f₁] [mono f₂] :
--   hat ((pullback.fst : pullback f₁ f₂ ⟶ R₁) ≫ f₁) = limits.prod.lift (hat f₁) (hat f₂) ≫ intersect.intersect A :=
-- begin
--   symmetry,
--   apply unique_hat,
--   refine ⟨_ ≫ square.top (intersect.both A), _, _⟩,
--   { apply pullback.lift _ _ _,
--     { apply pullback.lift _ _ _,
--       { apply pullback.fst ≫ square.top f₁ },
--       { apply pullback.fst ≫ f₁ ≫ limits.prod.map (limits.prod.lift (hat f₁) (hat f₂)) (𝟙 A) },
--       { slice_lhs 2 3 {rw square.commutes f₁},
--         rw [assoc, assoc, ← prod_functorial, limit.lift_π], refl } },
--     { apply pullback.lift _ _ _,
--       { apply pullback.snd ≫ square.top f₂ },
--       { apply pullback.fst ≫ f₁ ≫ limits.prod.map (limits.prod.lift (hat f₁) (hat f₂)) (𝟙 A) },
--       { slice_lhs 2 3 {rw square.commutes f₂},
--         slice_lhs 1 2 {rw ← pullback.condition},
--         rw [assoc, assoc, assoc, ← prod_functorial, limit.lift_π], refl } },
--     { rw [limit.lift_π], dsimp, erw [limit.lift_π], dsimp, refl } },
--   { slice_lhs 2 3 {rw square.commutes (intersect.both A)},
--     dunfold intersect.both,
--     slice_lhs 1 2 {rw limit.lift_π},
--     dsimp,
--     slice_lhs 1 2 {rw limit.lift_π},
--     dsimp,
--     rw [assoc, assoc, assoc],
--     rw prod_functorial,
--     refl },
--   { refine ⟨_, _, _⟩,
--     { intro s,
--       set toB' : s.X ⟶ pullback (intersect.left A) (intersect.right A) := (square.is_pullback (intersect.both A)).lift (pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.map (limits.prod.lift (hat f₁) (hat f₂)) (𝟙 A)) _),


--     }

--   }
-- end
