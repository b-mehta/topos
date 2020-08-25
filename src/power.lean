/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.finite_limits
import category_theory.limits.types
import category_theory.adjunction.limits
import category_theory.monad.limits
import category_theory.limits.opposites
import category_theory.limits.over
import category_theory.epi_mono
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers
import category_theory.limits.shapes.constructions.preserve_binary_products
import category.adjoint_lifting
import locally_cartesian_closed
import subobject_classifier

/-!
# Power objects

Define power objects.
Show that power objects induce a (contravariant) functor `P_functor`.
Show that this is self-adjoint on the right.
Define the singleton arrow {} : B ⟶ PB and internal image (for monos only)
and show the latter is functorial too.
Show the existence of a subobject classifier given power objects and show

-/
universes v u v₂ u₂

namespace category_theory

open category_theory category limits

attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits

variables {C : Type u} [category.{v} C]

variables [has_finite_limits.{v} C]

abbreviation powerises {A PA niA B R : C} (memA : niA ⟶ PA ⨯ A) (m : R ⟶ B ⨯ A) (mhat : B ⟶ PA) :=
has_pullback_top m (limits.prod.map mhat (𝟙 A)) memA

instance subsingleton_powerises {A PA niA B R : C} (memA : niA ⟶ PA ⨯ A) [mono memA] (m : R ⟶ B ⨯ A) (mhat : B ⟶ PA) :
  subsingleton (powerises memA m mhat) :=
⟨by { intros P Q, cases P, cases Q, congr, rw [← cancel_mono memA, P_comm, Q_comm] }⟩

structure is_power_object {A PA niA : C} (memA : niA ⟶ PA ⨯ A) :=
(hat : ∀ {B R} (m : R ⟶ B ⨯ A) [mono.{v} m], B ⟶ PA)
(powerises' : ∀ {B R} (m : R ⟶ B ⨯ A) [hm : mono m], powerises memA m (hat m))
(uniquely' : ∀ {B R} {m : R ⟶ B ⨯ A} [hm : mono m] {hat' : B ⟶ PA}, powerises memA m hat' → hat m = hat')

class has_power_object (A : C) :=
(PA niA : C)
(memA : niA ⟶ PA ⨯ A)
[is_mono : mono memA]
(is_power : is_power_object memA)

attribute [instance] has_power_object.is_mono

variable (C)

class has_power_objects :=
(has_power_object : Π (A : C), has_power_object.{v} A)

variable {C}

attribute [instance, priority 990] has_power_objects.has_power_object
attribute [simp] pullback.condition

section convenience

variables (A : C) [has_power_object.{v} A]

def P : C := has_power_object.PA.{v} A
def ni : C := has_power_object.niA.{v} A
def mem : ni A ⟶ P A ⨯ A := has_power_object.memA
def power_is_power : is_power_object (mem A) := has_power_object.is_power
instance mono_mem : mono (mem A) := has_power_object.is_mono

def mem_sub : sub (P A ⨯ A) := sub.mk' (mem A)
def mem_subq : subq (P A ⨯ A) := ⟦mem_sub A⟧

variables {A} {B R : C} (m : R ⟶ B ⨯ A) [mono m]

def hat : B ⟶ P A := (power_is_power A).hat m
def hat_powerises : powerises (mem A) m (hat m) := (power_is_power A).powerises' m

variable {m}
lemma unique_hat {hat' : B ⟶ P A} (hp : powerises (mem A) m hat') : hat m = hat' := (power_is_power A).uniquely' hp
end convenience

lemma P_unique_aux {A : C} {PA₁ niA₁ PA₂ niA₂ : C}
  (memA₁ : niA₁ ⟶ PA₁ ⨯ A) (memA₂ : niA₂ ⟶ PA₂ ⨯ A) [mono memA₁] [mono memA₂]
  (h₁ : is_power_object memA₁) (h₂ : is_power_object memA₂) :
h₁.hat memA₂ ≫ h₂.hat memA₁ = 𝟙 PA₂ :=
begin
  have: h₂.hat memA₂ = 𝟙 _,
  { apply h₂.uniquely',
    change has_pullback_top _ _ _,
    rw prod_map_id_id,
    apply top_iso_has_pullback_top (𝟙 _),
    rw [id_comp, comp_id] },
  rw ← this,
  symmetry,
  apply h₂.uniquely',
  change has_pullback_top _ _ _,
  rw prod_map_comp_id,
  apply left_right_hpb_to_both_hpb _ (h₁.powerises' memA₂) (h₂.powerises' memA₁),
end

def P_unique_up_to_iso {A : C} {PA₁ niA₁ PA₂ niA₂ : C}
  {memA₁ : niA₁ ⟶ PA₁ ⨯ A} {memA₂ : niA₂ ⟶ PA₂ ⨯ A} [mono memA₁] [mono memA₂]
  (h₁ : is_power_object memA₁) (h₂ : is_power_object memA₂) :
PA₁ ≅ PA₂ :=
{ hom := h₂.hat memA₁,
  inv := h₁.hat memA₂,
  hom_inv_id' := P_unique_aux memA₂ memA₁ h₂ h₁,
  inv_hom_id' := P_unique_aux memA₁ memA₂ h₁ h₂ }

variables {A B : C} [has_power_object.{v} A]

lemma hat_lift_of_is_iso {B R₁ R₂ : C} {g₁ : R₁ ⟶ B ⨯ A} {g₂ : R₂ ⟶ B ⨯ A} [mono g₁] [mono g₂] (hom : R₁ ⟶ R₂) [is_iso hom] (k : hom ≫ g₂ = g₁) :
  hat g₁ = hat g₂ :=
begin
  apply unique_hat,
  change has_pullback_top _ _ _,
  rw [← id_comp (limits.prod.map _ _)],
  refine left_right_hpb_to_both_hpb g₂ (top_iso_has_pullback_top hom _ _ _ (by simp [k])) (hat_powerises g₂),
end

lemma hat_lift_of_iso {B R₁ R₂ : C} {g₁ : R₁ ⟶ B ⨯ A} {g₂ : R₂ ⟶ B ⨯ A} [mono g₁] [mono g₂] (h : R₁ ≅ R₂) (k : h.hom ≫ g₂ = g₁) :
  hat g₁ = hat g₂ :=
hat_lift_of_is_iso h.hom k

-- We need to assume g₁ = hom ≫ g₂. From here if we know that hom,inv cancel then we get g₂ = inv ≫ g₁.
-- Instead we assume this and derive that hom,inv cancel
lemma lifting {A B R₁ R₂ : C} [has_power_object.{v} A] {g₁ : R₁ ⟶ B ⨯ A} {g₂ : R₂ ⟶ B ⨯ A} [mono g₁] [mono g₂] (hom : R₁ ⟶ R₂) (inv : R₂ ⟶ R₁) :
  hom ≫ g₂ = g₁ → inv ≫ g₁ = g₂ → hat g₁ = hat g₂ :=
begin
  intros k l,
  apply hat_lift_of_iso ⟨hom, inv, _, _⟩ k;
  simp [← cancel_mono g₁, ← cancel_mono g₂, l, k],
end

lemma liftable {B : C} (a b : sub (B ⨯ A)) (i : a ≈ b) : hat a.arrow = hat b.arrow :=
nonempty.elim i (λ i, lifting _ _ (sub.w i.hom) (sub.w i.inv))

def get_named_object {B : C} (k : B ⟶ P A) : C := pullback (mem A) (limits.prod.map k (𝟙 _))
def get_named_arrow {B : C} (k : B ⟶ P A) : get_named_object k ⟶ B ⨯ A := pullback.snd
instance get_named_mono {B : C} (k : B ⟶ P A) : mono (get_named_arrow k) := pullback.snd_of_mono
lemma hat_get_named_arrow {B : C} (k : B ⟶ P A) : hat (get_named_arrow k) = k :=
unique_hat has_pullback_top_of_pb

def hat_natural_left {B B' R : C} (k : R ⟶ B ⨯ A) [mono k] (g : B' ⟶ B) :
  hat (pullback.snd : pullback k (limits.prod.map g (𝟙 A)) ⟶ B' ⨯ A) = g ≫ hat k :=
begin
  apply unique_hat,
  change has_pullback_top _ _ _,
  rw prod_map_comp_id,
  apply left_right_hpb_to_both_hpb _ has_pullback_top_of_pb (hat_powerises k),
end

@[simps]
def name_bijection {A B : C} [has_power_object.{v} A] : (B ⟶ P A) ≃ subq (B ⨯ A) :=
{ to_fun := λ k, ⟦sub.mk' (get_named_arrow k)⟧,
  inv_fun := quotient.lift (λ (f : sub (B ⨯ A)), hat f.arrow) liftable,
  left_inv := hat_get_named_arrow,
  right_inv := quotient.ind
  begin
    intro g,
    apply quotient.sound,
    exact equiv_of_both_ways
      (sub.hom_mk _ ((hat_powerises g.arrow).is_pb.fac _ walking_cospan.right))
      (sub.hom_mk _ (pullback.lift_snd _ _ (hat_powerises g.arrow).comm)),
  end }

abbreviation name_subobject {B : C} : subq (B ⨯ A) → (B ⟶ P A) := name_bijection.symm

lemma get_named_subobject_eq_pullback_mem {B : C} (k : B ⟶ P A) :
  name_bijection k = (subq.pullback (limits.prod.map k (𝟙 _))).obj (mem_subq A) := rfl

def get_named_subobject_natural_left {B B' : C} (k : B ⟶ P A) (g : B' ⟶ B) :
  name_bijection (g ≫ k) = (subq.pullback (limits.prod.map g (𝟙 A))).obj (name_bijection k) :=
by { rw [get_named_subobject_eq_pullback_mem, prod_map_comp_id, subq.pullback_comp], refl }

lemma name_pullback {B' : C} (g : subq (B ⨯ A)) (f : B' ⟶ B) :
  name_subobject ((subq.pullback (limits.prod.map f (𝟙 _))).obj g) = f ≫ name_subobject g :=
quotient.induction_on g (λ a, hat_natural_left a.arrow _)

lemma pullback_along_hat_eq_self {R : C} (m : R ⟶ B ⨯ A) [mono m] :
  (subq.pullback (limits.prod.map (hat m) (𝟙 A))).obj (mem_subq A) = ⟦sub.mk' m⟧ :=
begin
  rw ← get_named_subobject_eq_pullback_mem,
  erw name_bijection.apply_eq_iff_eq_symm_apply,
  refl
end

section functor_setup

variables (f : A ⟶ B) [has_power_object.{v} B]
def E : C := pullback (mem B) (limits.prod.map (𝟙 _) f)
def Emap : E f ⟶ P B ⨯ A := pullback.snd
instance Emap_mono : mono (Emap f) := pullback.snd_of_mono
def Esubq : subq (P B ⨯ A) := (subq.pullback (limits.prod.map (𝟙 _) f)).obj (mem_subq B)
lemma Esquare : (pullback.fst : E f ⟶ _) ≫ mem B = Emap f ≫ limits.prod.map (𝟙 _) f := pullback.condition
lemma Epb : is_limit (pullback_cone.mk _ _ (Esquare f)) :=
cone_is_pullback _ _

variable [has_power_object.{v} A]
def P_map : P B ⟶ P A :=
name_subobject (Esubq f)

lemma hat_natural_right {D R : C} (m : R ⟶ D ⨯ B) [hm : mono m] :
  hat (pullback.snd : pullback m (limits.prod.map (𝟙 D) f) ⟶ D ⨯ A) = hat m ≫ P_map f :=
begin
  apply unique_hat,
  change has_pullback_top _ _ _,
  rw prod_map_comp_id,
  apply left_right_hpb_to_both_hpb _ _ (hat_powerises _),
  apply right_both_hpb_to_left_hpb _ _ _ has_pullback_top_of_pb,
  rw ← prod_map_map,
  apply left_right_hpb_to_both_hpb m has_pullback_top_of_pb (hat_powerises _),
end

lemma name_other_pullback {D : C} :
  ∀ m, name_subobject ((subq.pullback (limits.prod.map (𝟙 D) f)).obj m) = name_subobject m ≫ P_map f :=
quotient.ind (by { intro a, apply hat_natural_right })

@[simp] lemma lift'_right {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : pullback_cone f g} (ht : is_limit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
  (pullback_cone.is_limit.lift' ht h k w).val ≫ t.snd = k :=
(pullback_cone.is_limit.lift' ht h k w).2.2

def how_inj_is_hat {B R₁ R₂ : C} {f₁ : R₁ ⟶ B ⨯ A} {f₂ : R₂ ⟶ B ⨯ A} [mono f₁] [mono f₂] (h : hat f₁ = hat f₂) :
  R₁ ≅ R₂ :=
{ hom := (pullback_cone.is_limit.lift' (hat_powerises f₂).is_pb (hat_powerises f₁).top f₁ (h ▸ (hat_powerises f₁).comm)).1,
  inv := (pullback_cone.is_limit.lift' (hat_powerises f₁).is_pb (hat_powerises f₂).top f₂ (h.symm ▸ (hat_powerises f₂).comm)).1,
  hom_inv_id' := by erw [← cancel_mono_id f₁, assoc, lift'_right, lift'_right],
  inv_hom_id' := by erw [← cancel_mono_id f₂, assoc, lift'_right, lift'_right] }

lemma very_inj {B R₁ R₂ : C} {f₁ : R₁ ⟶ B ⨯ A} {f₂ : R₂ ⟶ B ⨯ A} [mono f₁] [mono f₂] (h : hat f₁ = hat f₂) :
  (how_inj_is_hat h).hom ≫ f₂ = f₁ :=
lift'_right _ _ _ _

lemma P_map_id (X : C) [has_power_object.{v} X] : P_map (𝟙 X) = 𝟙 (P X) :=
hat_get_named_arrow _

lemma P_map_comp {X Y Z : C} [has_power_object.{v} X] [has_power_object.{v} Y] [has_power_object.{v} Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
  P_map (f ≫ g) = P_map g ≫ P_map f :=
by { erw [← name_other_pullback, Esubq, ← subq.pullback_comp, ← prod_map_id_comp], refl }

@[simps]
def P_functor [has_power_objects.{v} C] : Cᵒᵖ ⥤ C :=
{ obj := λ X, P X.unop,
  map := λ X Y f, P_map f.unop,
  map_id' := λ X, P_map_id _,
  map_comp' := λ X Y Z f g, P_map_comp _ _ }

end functor_setup

def self_adj [has_power_objects.{v} C] : is_right_adjoint (P_functor : Cᵒᵖ ⥤ C) :=
{ left := P_functor.right_op,
  adj := adjunction.mk_of_hom_equiv
  { hom_equiv := λ A B,
    begin
      apply equiv.trans (op_equiv (opposite.op (P A)) B),
      apply equiv.trans name_bijection,
      apply equiv.trans _ name_bijection.symm,
      apply postcompose_sub_equiv_of_iso (limits.prod.braiding _ _),
    end,
    hom_equiv_naturality_left_symm' := λ X' X Y f g,
    begin
      rw ← has_hom.hom.unop_inj.eq_iff,
      change name_subobject ((subq.post _).obj (name_bijection (f ≫ g))) =
             name_subobject ((subq.post _).obj (name_bijection g)) ≫ P_map f,
      rw [← name_other_pullback, get_named_subobject_natural_left],
      congr' 1,
      exact postcompose_pullback_comm _ (pullback_square_iso _ _ _ _ (braid_natural _ _)) _,
    end,
    hom_equiv_naturality_right' := λ X Y Y' f g,
    begin
      change name_subobject ((subq.post _).obj (name_bijection (g.unop ≫ f.unop))) =
             name_subobject ((subq.post _).obj (name_bijection f.unop)) ≫ P_map g.unop,
      rw [← name_other_pullback, get_named_subobject_natural_left],
      congr' 1,
      exact postcompose_pullback_comm _ (pullback_square_iso _ _ _ _ (braid_natural _ _)) _,
    end } }

def diagonal (A : C) : A ⟶ A ⨯ A := limits.prod.lift (𝟙 A) (𝟙 A)

instance mono_diagonal (A : C) : mono.{v} (diagonal A) := category_theory.mono_prod_lift_of_left _ _

def diagonal_sub (A : C) : sub (A ⨯ A) := sub.mk' (diagonal A)
def diagonal_subq (A : C) : subq (A ⨯ A) := ⟦diagonal_sub A⟧

-- @[reducible]
def singleton_arrow (A : C) [has_power_object.{v} A] : A ⟶ P A := hat (diagonal A)

lemma seven_six_one {A B : C} [has_power_object.{v} B] (f : A ⟶ B) :
  hat (limits.prod.lift (𝟙 A) f) = f ≫ singleton_arrow B :=
begin
  rw [singleton_arrow, ← hat_natural_left],
  apply lifting (pullback.lift f _ _) (pullback.snd ≫ limits.prod.fst) (pullback.lift_snd _ _ _) _,
  { rw [prod.lift_map, diagonal],
    apply prod.hom_ext; simp },
  { apply prod.hom_ext,
    { simp only [prod.lift_fst, assoc, comp_id] },
    { rw [assoc, prod.lift_snd, assoc, ← limits.prod.map_fst f (𝟙 _), ← comp_id limits.prod.snd,
          ← limits.prod.map_snd f _, ← pullback.condition_assoc, ← pullback.condition_assoc, diagonal],
      simp } }
end

lemma seven_six_two {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) :
  hat (limits.prod.lift f (𝟙 A)) = singleton_arrow B ≫ P_map f :=
begin
  rw [singleton_arrow, ← hat_natural_right],
  apply lifting (pullback.lift f _ _) (pullback.snd ≫ limits.prod.snd) (pullback.lift_snd _ _ _) _,
  { rw [prod.lift_map, diagonal],
    apply prod.hom_ext; simp },
  { apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, assoc,  ← limits.prod.map_snd (𝟙 _) f, ← pullback.condition_assoc,
          ← comp_id limits.prod.fst, ← limits.prod.map_fst (𝟙 _) f, ← pullback.condition_assoc, diagonal],
      simp },
    { simp only [assoc, comp_id, prod.lift_snd] } },
end

instance singleton_mono (A : C) [has_power_object.{v} A] : mono (singleton_arrow A) :=
⟨λ Z g h w,
begin
  rw [← seven_six_one, ← seven_six_one] at w,
  have q := very_inj w =≫ limits.prod.fst,
  have r := very_inj w =≫ limits.prod.snd,
  simp only [prod.lift_fst, assoc, comp_id] at q,
  simpa [q] using r.symm,
end⟩

lemma p_faithful {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] {f g : A ⟶ B} (k : P_map f = P_map g) :
  f = g :=
begin
  have w := singleton_arrow _ ≫= k,
  rw [← seven_six_two, ← seven_six_two] at w,
  have q := very_inj w =≫ limits.prod.fst,
  have r := very_inj w =≫ limits.prod.snd,
  simp only [prod.lift_snd, assoc, comp_id] at r,
  simpa [r] using q.symm,
end

instance pfaithful [has_power_objects.{v} C] : faithful (P_functor : Cᵒᵖ ⥤ C) :=
⟨λ A B f g k, has_hom.hom.unop_inj (p_faithful k)⟩

def internal_image {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] : P A ⟶ P B :=
hat (mem A ≫ limits.prod.map (𝟙 (P A)) f)

-- TODO: this doesn't use pasting so it's super long. can we make it nicer by using pasting?
-- TODO: if not, it's still a horribly long proof which desperately needs a cleanup
lemma naturalish {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] {R D : C} (m : R ⟶ D ⨯ A) [mono m] :
  hat m ≫ internal_image f = hat (m ≫ limits.prod.map (𝟙 D) f) :=
begin
  have comm : limits.prod.map (hat m) (𝟙 _) ≫ limits.prod.map (𝟙 _) f = limits.prod.map (𝟙 _) f ≫ limits.prod.map (hat m) (𝟙 _),
    rw prod_map_map,
  change hat m ≫ name_bijection.symm ((subq.post (limits.prod.map _ _)).obj (mem_subq A)) = name_bijection.symm ((subq.post _).obj ⟦sub.mk' m⟧),
  rw [← name_pullback, ← postcompose_pullback_comm comm _, pullback_along_hat_eq_self], refl,
  refine is_limit.mk''' _ _ _,
    exact (category_theory.mono_prod_map (𝟙 D) f),
  intro s,
  refine ⟨_, _⟩,
  apply prod.lift (s.snd ≫ limits.prod.fst) (s.fst ≫ limits.prod.snd),
  erw [prod.lift_map, comp_id, assoc, ← limits.prod.map_snd (𝟙 _), s.condition_assoc,
       limits.prod.map_snd, comp_id],
  apply prod.hom_ext; simp,
end

lemma internal_image_map_comp {X Y Z : C} [has_power_object.{v} X] [has_power_object.{v} Y] [has_power_object.{v} Z]
  (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  internal_image (f ≫ g) = internal_image f ≫ internal_image g :=
begin
  erw [naturalish, internal_image],
  congr' 1,
  rw [assoc, prod_map_id_comp],
end

lemma internal_image_map_id {X : C} [has_power_object.{v} X] : internal_image (𝟙 X) = 𝟙 (P X) :=
begin
  change name_subobject ((subq.post (limits.prod.map _ _)).obj (mem_subq _)) = _,
  rw [name_bijection.symm_apply_eq, get_named_subobject_eq_pullback_mem],
  conv { for (limits.prod.map _ _) [1, 2] { rw prod_map_id_id } },
  rw [subq.post_id, subq.pullback_id],
end

theorem beck_chevalley {A B C' D : C}
  [has_power_object.{v} A] [has_power_object.{v} B]
  [has_power_object.{v} C'] [has_power_object.{v} D]
  {h : D ⟶ A} {f : A ⟶ C'} {k : D ⟶ B} {g : B ⟶ C'} (comm : h ≫ f = k ≫ g) [mono f] [mono k]
  (t : is_limit (pullback_cone.mk h k comm)) :
  internal_image f ≫ P_map g = P_map h ≫ internal_image k :=
begin
  erw [← hat_natural_right, naturalish],
  change name_subobject ((subq.pullback _).obj ((subq.post (limits.prod.map _ _)).obj (mem_subq A))) =
         name_subobject ((subq.post (limits.prod.map _ _)).obj ((subq.pullback _).obj (mem_subq A))),
  rw equiv.apply_eq_iff_eq,
  symmetry,
  apply postcompose_pullback_comm _ _,
  rw [← prod_map_id_comp, comm, prod_map_id_comp],
  haveI : preserves_limits_of_shape walking_cospan _ := prod_preserves_connected_limits (P A),
  apply preserves_pullback_cone (prod_functor.obj (P A)) _ _ _ _ comm t,
end

variable (C)
def weak_topos_has_subobj [has_power_object.{v} (⊤_ C)] : has_subobject_classifier.{v} C :=
{ Ω := P (⊤_ C),
  Ω₀ := ni (⊤_ C),
  truth := mem (⊤_ C) ≫ (prod.right_unitor _).hom,
  is_subobj_classifier :=
  { classifier_of := λ U X f hf, by exactI hat (f ≫ (prod.right_unitor _).inv),
    classifies' := λ U X f hf, by exactI
    begin
      change has_pullback_top _ _ _,
      conv {congr, rw [← comp_id f, ← (prod.right_unitor X).inv_hom_id, ← assoc] },
      apply stretch_hpb_down _ _ _ limits.prod.fst _ _ (hat_powerises _) (limits.prod.map_fst _ _),
      apply pullback_flip (pullback_prod _ _),
    end,
    uniquely' := λ U X f hf χ₁ k,
    begin
      apply unique_hat,
      apply cut_hpb_up _ _ _ (prod.right_unitor _).hom (prod.right_unitor _).hom _ _ _ (pullback_flip (pullback_prod _ _)),
      { apply_instance },
      { rw [assoc, (prod.right_unitor X).inv_hom_id, comp_id],
        exact k },
      { apply limits.prod.map_fst }
    end } }
variable {C}

instance p_reflects_iso [has_power_objects.{v} C] : reflects_isomorphisms (P_functor : Cᵒᵖ ⥤ C) :=
{ reflects := λ A B f i, by exactI
begin
  suffices : is_iso f.unop,
    resetI,
    refine ⟨this.inv.op,
            has_hom.hom.unop_inj (is_iso.inv_hom_id f.unop),
            has_hom.hom.unop_inj (is_iso.hom_inv_id f.unop)⟩,
  haveI : has_subobject_classifier.{v} C := weak_topos_has_subobj _,
  haveI := reflects_isos _ (P_functor.right_op : C ⥤ _),
  haveI : is_iso (P_functor.right_op.map f.unop) :=
    ⟨i.inv.op, has_hom.hom.unop_inj (is_iso.inv_hom_id _),
               has_hom.hom.unop_inj (is_iso.hom_inv_id _)⟩,
  refine is_iso_of_reflects_iso f.unop P_functor.right_op,
end }

def exists_power {A B : C} [has_power_object.{v} A] [has_power_object.{v} B] (f : A ⟶ B) [mono f] :
  internal_image f ≫ P_map f = 𝟙 (P A) :=
by rw [beck_chevalley _ (pullback_of_mono f), P_map_id, internal_image_map_id, comp_id]

instance fin_category_op (J : Type v) [small_category J] [fcj : fin_category J] : fin_category Jᵒᵖ :=
{ decidable_eq_obj := λ x y, decidable_of_decidable_of_iff infer_instance opposite.unop_injective.eq_iff,
  fintype_obj :=
    { elems := finset.map ⟨opposite.op, opposite.op_injective⟩ _,
      complete := λ x, finset.mem_map_of_mem _ (fintype.complete x.unop) },
  decidable_eq_hom := λ x y f g, decidable_of_decidable_of_iff infer_instance has_hom.hom.unop_inj.eq_iff,
  fintype_hom := λ X Y,
  { elems := (@fin_category.fintype_hom J _ fcj Y.unop X.unop).elems.map ⟨has_hom.hom.op, has_hom.hom.op_inj⟩,
    complete := λ f, finset.mem_map_of_mem _ (fintype.complete f.unop) } }

local attribute [instance] has_colimits_of_shape_op_of_has_limits_of_shape

instance pare [has_power_objects.{v} C] : monadic_right_adjoint (P_functor : Cᵒᵖ ⥤ C) :=
{ to_is_right_adjoint := self_adj,
  eqv :=
  begin
    apply reflexive_monadicity_theorem _ _ category_theory.p_reflects_iso,
    { intros _ _ _ _ _, apply_instance },
    { rintros B' A' f' g' ⟨r', rf, rg⟩,
      refine { preserves := λ c t, _ },
      let e : c.X.unop ⟶ A'.unop := (cofork.π c).unop,
      haveI : split_mono g'.unop := ⟨r'.unop, by { rw [auto_param_eq, ← unop_comp, rg], refl }⟩,
      haveI : epi (cofork.π c) := epi_of_is_colimit_parallel_pair t,
      haveI mono_e : mono e := category_theory.unop_mono_of_epi _,
      have : internal_image g'.unop ≫ P_map f'.unop = P_map e ≫ internal_image e := beck_chevalley _ _,
      apply colimit_of_splits (P_functor.map_cocone c) _ (internal_image g'.unop) (exists_power e) (exists_power g'.unop) this,
        rw [← unop_comp, ← cofork.condition c], refl,
      refine is_limit.mk''' _ mono_e (λ s, _),
      have equal_legs : s.fst = s.snd,
        simpa [← unop_comp, rf, rg] using s.condition =≫ r'.unop,
      refine ⟨(cofork.is_colimit.desc' t s.fst.op _).1.unop, _⟩,
      { rw [← has_hom.hom.unop_inj.eq_iff],
        dsimp, rw [s.condition, equal_legs] },
      change (cofork.π c ≫ (cofork.is_colimit.desc' t s.fst.op _).1).unop = _,
      rwa (cofork.is_colimit.desc' t s.fst.op _).2 }
  end }

def some_colims (J : Type v) [small_category J] [has_power_objects.{v} C] [has_limits_of_shape Jᵒᵖ C] : has_colimits_of_shape J C :=
{ has_colimit := λ F, by exactI
  begin
    suffices: has_colimit (F ⋙ op_op_equivalence.inverse),
      resetI,
      apply adjunction.has_colimit_of_comp_equivalence F op_op_equivalence.inverse,
    let F'' : Jᵒᵖ ⥤ Cᵒᵖ := (F ⋙ op_op_equivalence.inverse).left_op,
    suffices : has_limit F'',
      resetI,
      apply limits.has_colimit_of_has_limit_left_op,
    suffices : has_limit (F'' ⋙ P_functor),
      apply monadic_creates_limits F'' P_functor,
    apply_instance
  end }

namespace intersect

variables {A} [has_power_object.{v} A]

def intersect_names {B : C} (m n : B ⟶ P A) : B ⟶ P A :=
name_subobject $ name_bijection m ⊓ name_bijection n

def intersect_names_natural {B B' : C} (f : B' ⟶ B) (m n : B ⟶ P A) :
  f ≫ intersect_names m n = intersect_names (f ≫ m) (f ≫ n) :=
begin
  dunfold intersect_names,
  rw [get_named_subobject_natural_left, get_named_subobject_natural_left, ← inf_pullback,
      name_bijection.eq_symm_apply, get_named_subobject_natural_left, name_bijection.apply_symm_apply],
end

def intersect (A : C) [has_power_object.{v} A] : P A ⨯ P A ⟶ P A := intersect_names limits.prod.fst limits.prod.snd

end intersect

@[priority 10000] instance [has_finite_limits.{v} C] {B : C} : has_finite_limits.{v} (over B) :=
begin
  haveI := has_finite_wide_pullbacks_of_has_finite_limits C,
  apply over.has_finite_limits,
end

def P₁_obj (A : C) [has_power_object.{v} A] : C := equalizer (intersect.intersect A) limits.prod.fst
def P₁_arrow (A : C) [has_power_object.{v} A] : P₁_obj A ⟶ P A ⨯ P A := equalizer.ι (intersect.intersect A) limits.prod.fst
instance P₁_arrow_mono (A : C) [has_power_object.{v} A] : mono (P₁_arrow A) := equalizer.ι_mono
def P₁_sub (A : C) [has_power_object.{v} A] : subq (P A ⨯ P A) := ⟦sub.mk' (P₁_arrow A)⟧

lemma leq_prop' (A B : C) (m n : subq (B ⨯ A)) [has_power_object.{v} A] :
  m ≤ n ↔ limits.prod.lift (name_subobject m) (name_subobject n) ≫ intersect.intersect A = limits.prod.lift (name_subobject m) (name_subobject n) ≫ limits.prod.fst :=
begin
  rw [← inf_eq_left, intersect.intersect, intersect.intersect_names_natural, prod.lift_fst,
      prod.lift_snd, intersect.intersect_names, name_bijection.eq_symm_apply],
  simp only [name_bijection.apply_symm_apply],
end

lemma leq_prop (A B R₁ R₂ : C) [has_power_object.{v} A] (m : R₁ ⟶ B ⨯ A) (n : R₂ ⟶ B ⨯ A) [mono m] [mono n] :
  factors_through m n ↔ limits.prod.lift (hat m) (hat n) ≫ intersect.intersect A = limits.prod.lift (hat m) (hat n) ≫ limits.prod.fst :=
leq_prop' _ _ ⟦sub.mk' m⟧ ⟦sub.mk' n⟧

-- lemma leq_iff_factor (A B R₁ R₂ : C) [has_power_object.{v} A] (m : R₁ ⟶ B ⨯ A) (n : R₂ ⟶ B ⨯ A) [mono m] [mono n] :
--   factors_through m n ↔ factors_through (prod.lift (hat m) (hat n)) (P₁_arrow A) :=
-- begin
--   rw [leq_prop, factors_through],

--   -- refine ⟨λ k, ⟨_, (equalizer.lift' _ k).2⟩, _⟩,
--   -- rintro ⟨k, hk⟩,
--   -- simp [←hk, P₁_arrow, equalizer.condition],
-- end

namespace slicing

-- EVERYTHING FROM HERE DOWN NEEDS TIDYING!!

-- def lift_exists_of_regular {X Y : C} {r : X ⟶ Y} [hr : regular_mono r] {Z : C} {l : Z ⟶ Y} (h : ∃ (q : Z ⟶ X), q ≫ r = l) : {q // q ≫ r = l} :=
-- begin
--   apply fork.is_limit.lift' hr.is_limit l,
--   cases h,
--   simp [← h_h, hr.w],
-- end

-- def power_object_of_hats {A PA : C} (mem : sub'.{v} (PA ⨯ A)) (hats : Π {B} (f : sub'.{v} (B ⨯ A)), B ⟶ PA)
--   [regular_mono mem.arrow.hom]
--   (mediate : Π {B} (f : sub'.{v} (B ⨯ A)), { k : pullback mem.arrow.hom (limits.prod.map (hats f) (𝟙 _)) ≅ f.arrow.left // k.hom ≫ f.arrow.hom = pullback.snd }) :
-- is_power_object.{v} mem.arrow.hom :=
-- { hat := λ B R m hm, by exactI hats (sub'.mk' m),
--   powerises' := λ B R m hm, by exactI
--   begin
--     change has_pullback_top _ _ _,
--     obtain ⟨⟨hom, inv, hom_inv_id, inv_hom_id⟩, hq⟩ := mediate (sub'.mk' m),
--     dsimp at hom inv hom_inv_id inv_hom_id hq,
--     -- let q' : R ⟶ pullback mem.arrow.hom (limits.prod.map (hats (sub'.mk' m)) (𝟙 A)) := pullback.lift _ m _,
--     -- sorry,
--     -- refine ⟨_, _, _⟩,
--   end

-- }

variables {B} (f g : over B)

-- def reflect_pullback (P Q R S : over B) (f : P ⟶ Q) (g : Q ⟶ S) (h : P ⟶ R) (k : R ⟶ S)
--   (comm : f ≫ g = h ≫ k) (t : is_limit (pullback_cone.mk f.left h.left (begin exact congr_arg comma_morphism.left comm end))) :
-- is_limit (pullback_cone.mk f h comm) :=
-- begin
--   apply is_limit.mk',
--   intro s,
--   let s' : pullback_cone g.left k.left := pullback_cone.mk (pullback_cone.fst s).left (pullback_cone.snd s).left (congr_arg comma_morphism.left (pullback_cone.condition s)),
--   refine ⟨over.hom_mk (t.lift s') _, _, _, _⟩,
--   dsimp, change t.lift s' ≫ P.hom = _, rw ← over.w f, slice_lhs 1 2 {erw t.fac _ walking_cospan.left}, exact over.w (pullback_cone.fst s),
--   ext1, dsimp, exact t.fac _ walking_cospan.left,
--   ext1, dsimp, exact t.fac _ walking_cospan.right,
--   intros m m₁ m₂,
--   ext1,
--   dsimp,
--   refine t.hom_ext _,
--   apply pullback_cone.equalizer_ext (pullback_cone.mk f.left h.left _),
--   erw t.fac _ walking_cospan.left,
--   exact congr_arg comma_morphism.left m₁,
--   erw t.fac _ walking_cospan.right,
--   exact congr_arg comma_morphism.left m₂,
-- end

-- def preserve_pullback {P Q R S : over B} {f : P ⟶ Q} {g : Q ⟶ S} {h : P ⟶ R} {k : R ⟶ S}
--   {comm : f ≫ g = h ≫ k} (t : is_limit (pullback_cone.mk f h comm)) :
-- is_limit (pullback_cone.mk f.left h.left (begin exact congr_arg comma_morphism.left comm end)) :=
-- begin
--   apply is_limit.mk',
--   intro s,
--   let sX' : over B := over.mk (pullback_cone.snd s ≫ R.hom),
--   have: pullback_cone.fst s ≫ Q.hom = pullback_cone.snd s ≫ R.hom,
--     rw [← over.w g, pullback_cone.condition_assoc s, over.w k],
--   let fst' : sX' ⟶ Q := over.hom_mk (pullback_cone.fst s) (by assumption),
--   let snd' : sX' ⟶ R := over.hom_mk (pullback_cone.snd s),
--   have comm': fst' ≫ g = snd' ≫ k,
--     ext, dsimp, apply pullback_cone.condition s,
--   let q : sX' ⟶ P := t.lift (pullback_cone.mk fst' snd' comm'),
--   have qf : q ≫ f = fst' := t.fac _ walking_cospan.left,
--   have qh : q ≫ h = snd' := t.fac _ walking_cospan.right,
--   refine ⟨q.left, congr_arg comma_morphism.left qf, congr_arg comma_morphism.left qh, _⟩,
--   intros m m₁ m₂,
--   have z: m ≫ P.hom = pullback_cone.snd s ≫ R.hom,
--   { rw [← over.w h, ← m₂, assoc], refl },
--   let m' : sX' ⟶ P := over.hom_mk m (by apply z),
--   have: m' = q,
--     apply t.hom_ext,
--     refine pullback_cone.equalizer_ext (pullback_cone.mk f h comm) _ _,
--     { erw qf,
--       ext,
--       dsimp,
--       erw m₁ },
--     { erw qh,
--       ext,
--       dsimp,
--       erw m₂ },
--   apply congr_arg comma_morphism.left this,
-- end

variables [has_power_object.{v} B] [has_power_object.{v} f.left]

-- @[reducible]
def bottom : P f.left ⨯ B ⟶ P f.left ⨯ P f.left := limits.prod.map (𝟙 _) (singleton_arrow B ≫ P_map f.hom)

def Q : C := pullback (P₁_arrow f.left) (bottom f)
def hk : Q f ⟶ P f.left ⨯ B := pullback.snd
def k : Q f ⟶ B        := hk f ≫ limits.prod.snd
def h : Q f ⟶ P f.left := hk f ≫ limits.prod.fst
def over_pow : over B  := over.mk (k f)

def up : C := pullback (mem f.left) (limits.prod.map (h f) (𝟙 f.left))
def h' : up f ⟶ Q f ⨯ f.left := pullback.snd
instance mono_h' : mono (h' f) := pullback.snd_of_mono
instance mono_hk : mono (hk f) := pullback.snd_of_mono

def hat_h' : hat (h' f) = h f :=
unique_hat has_pullback_top_of_pb

def over.ni (f : over B) [has_power_object.{v} B] [has_power_object.{v} f.left] : over B :=
over.mk (h' f ≫ limits.prod.snd ≫ f.hom)

-- fix me.
def prop (f : over B) [has_power_object.{v} B] [has_power_object.{v} f.left] :
  ∃ q, q ≫ (pullback.snd : pullback (prod.lift f.hom (𝟙 f.left)) (limits.prod.map ((k f) : _ ⟶ B) (𝟙 f.left)) ⟶ _) = h' f :=
begin
  have: pullback.fst ≫ P₁_arrow f.left = limits.prod.lift (h f) (k f ≫ singleton_arrow B ≫ P_map f.hom),
    rw [pullback.condition],
    dunfold bottom,
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, h, hk, limits.prod.map_fst, comp_id] },
    { rw [assoc, prod.lift_snd, k, hk, limits.prod.map_snd, assoc] },
  rw [← seven_six_two, ← hat_natural_left, ← hat_h' f] at this,
  have: limits.prod.lift (hat (h' f)) (hat pullback.snd) ≫ intersect.intersect f.left = limits.prod.lift (hat (h' f)) (hat pullback.snd) ≫ limits.prod.fst,
    rw ← this,
    erw [assoc, assoc, equalizer.condition], refl,
  rw ← leq_prop at this,
  cases this with a,
  refine ⟨_, over.w a⟩,
end

-- @[reducible]
def over.mem : over.ni f ⟶ over_pow f ⨯ f :=
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
    rw [← hq, assoc, assoc, ← z₁, z₂, assoc, assoc],
  apply over.hom_mk _ _,
  exact h' f ≫ limits.prod.snd,
  simp only [assoc, auto_param_eq], refl,
end
-- pretty gross.
instance over.mem_mono : mono (over.mem f) :=
begin
  refine ⟨λ Z p q eq, _⟩,
  ext1,
  rw ← cancel_mono (h' f),
  apply prod.hom_ext,
  rw [assoc, assoc],
  have e₁ := eq =≫ limits.prod.fst,
  rw [over.mem, assoc, assoc, prod.lift_fst] at e₁,
  exact congr_arg comma_morphism.left e₁,
  have e₂ := eq =≫ limits.prod.snd,
  rw [over.mem, assoc, assoc, prod.lift_snd] at e₂,
  rw [assoc, assoc],
  exact congr_arg comma_morphism.left e₂,
end

section hat

variables {f g}
variables {r : over B} (m : r ⟶ g ⨯ f) [mono m]

def m' : r.left ⟶ (g ⨯ f).left := m.left
instance m'_mono : mono (m' m) := category_theory.over_mono m

def m'' : r.left ⟶ g.left ⨯ f.left := m' m ≫ magic_arrow f g
instance m''_mono : mono (m'' m) := mono_comp _ _

-- @[reducible]
def mhat : g.left ⟶ P f.left := hat (m'' m)
-- @[reducible]
def l : g.left ⟶ P f.left ⨯ P f.left := prod.lift (mhat m) g.hom ≫ bottom f
lemma l_eq : l m = prod.lift (hat (m'' m)) (g.hom ≫ (singleton_arrow B : B ⟶ P B) ≫ P_map f.hom) :=
begin
  rw [l, bottom, prod.lift_map, comp_id], refl,
end

lemma llem : l m ≫ intersect.intersect f.left = l m ≫ limits.prod.fst :=
begin
  have := l_eq m,
  erw [← seven_six_two, ← hat_natural_left] at this,
  rw [this, ← leq_prop],
  refine ⟨_⟩,
  apply over.hom_mk _ _,
  { apply pullback.lift (m'' m ≫ limits.prod.snd) (m'' m) _,
    apply prod.hom_ext,
    { erw [assoc, assoc, assoc, assoc, m'', assoc, prod.lift_fst, limits.prod.map_fst],
      slice_lhs 2 3 {rw prod.lift_snd},
      slice_rhs 2 3 {rw prod.lift_fst},
      rw over.w (limits.prod.fst : g ⨯ f ⟶ g),
      rw over.w (limits.prod.snd : g ⨯ f ⟶ f) },
    { erw [assoc, assoc, assoc, assoc, assoc, prod.lift_snd, comp_id, limits.prod.map_snd, comp_id] } },
  { dsimp, rw limit.lift_π, refl }
end
-- @[reducible]
def top : g.left ⟶ P₁_obj f.left := equalizer.lift (l m) (llem m)
-- @[reducible]
def h'' : g.left ⟶ Q f := pullback.lift (top m) (prod.lift (mhat m) g.hom) (limit.lift_π _ _)
-- @[reducible]
def make_arrow : g ⟶ over_pow f := over.hom_mk (h'' m) $ by { dsimp [over_pow, hk, k, h''], simp }
-- @[reducible]
def square_top (m : r ⟶ g ⨯ f) [mono m] : r ⟶ over.ni f :=
begin
  refine over.hom_mk (pullback.lift (hat_powerises (m'' m)).top _ _) _,
  { apply (m'' m) ≫ limits.prod.map (h'' m) (𝟙 _) },
  { rw (hat_powerises (m'' m)).comm, conv_rhs {rw [assoc, ← prod_map_comp_id]}, congr' 2,
    erw [h, hk, h'', limit.lift_π_assoc, prod.lift_fst, mhat] },
  { dsimp [h'], erw [limit.lift_π_assoc, assoc, limits.prod.map_snd_assoc, id_comp],
    erw [← over.w m, assoc, prod.lift_snd_assoc, over.w (limits.prod.snd : g ⨯ f ⟶ f)], refl }
end
def alt_square_commutes : square_top m ≫ over.mem f ≫ limits.prod.fst = (m ≫ limits.prod.fst) ≫ make_arrow m :=
begin
  rw [assoc, over.mem, prod.lift_fst, make_arrow],
  ext1,
  dsimp [h', m'', magic_arrow, h'', square_top],
  rw limit.lift_π_assoc,
  dsimp,
  rw [assoc, limits.prod.map_fst, assoc, prod.lift_fst_assoc], refl
end
def square_commutes : square_top m ≫ over.mem f = m ≫ limits.prod.map (make_arrow m) (𝟙 _) :=
begin
  apply prod.hom_ext,
  { rw [assoc, alt_square_commutes, assoc, assoc, limits.prod.map_fst] },
  { rw [assoc, over.mem, prod.lift_snd, assoc, limits.prod.map_snd, comp_id],
    ext1,
    dsimp [h', square_top],
    rw limit.lift_π_assoc,
    dsimp,
    rw [assoc, limits.prod.map_snd, comp_id],
    simp [m'', m'] }
end

def alt_square_pb : is_limit (pullback_cone.mk _ _ (alt_square_commutes m)) :=
begin
  apply reflects_pullback_cone over.forget,
  -- apply reflect_pullback,
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
      dsimp only [over.mem] at this,
      rw [prod.lift_fst] at this,
      dsimp [h'] at this,
      slice_lhs 1 3 {rw this},
      dsimp [h, hk, make_arrow, h''],
      rw [assoc],
      rw [pullback.lift_snd_assoc, prod.lift_fst], refl },
    { rw [assoc, assoc, assoc, limits.prod.map_snd, comp_id, prod.lift_snd] } },
  let t : s.X ⟶ r.left := (hat_powerises (m'' m)).is_pb.lift (pullback_cone.mk _ _ lem),
  have t₃ : t ≫ m'' m ≫ limits.prod.fst = pullback_cone.snd s,
    rw ← assoc,
    erw (hat_powerises (m'' m)).is_pb.fac (pullback_cone.mk _ _ lem) walking_cospan.right,
    dsimp,
    rw prod.lift_fst,
  have t₂ : t ≫ m'' m ≫ limits.prod.snd = pullback_cone.fst s ≫ pullback.fst ≫ mem f.left ≫ limits.prod.snd,
    rw ← assoc,
    erw (hat_powerises (m'' m)).is_pb.fac (pullback_cone.mk _ _ lem) walking_cospan.right,
    dsimp,
    rw prod.lift_snd,
  have t₁: t ≫ (hat_powerises (m'' m)).top = pullback_cone.fst s ≫ pullback.fst,
    erw (hat_powerises (m'' m)).is_pb.fac (pullback_cone.mk _ _ lem) walking_cospan.left,
    refl,
  refine ⟨t, _, _, _⟩,
  { change t ≫ pullback.lift (hat_powerises (m'' m)).top (m'' m ≫ limits.prod.map (h'' m) (𝟙 f.left)) _ = s.π.app walking_cospan.left,
    apply pullback.hom_ext,
    { rw ← t₁, simp },
    { rw [assoc], slice_lhs 2 3 {rw limit.lift_π},
      dsimp,
      apply prod.hom_ext,
      { rw [assoc, assoc, limits.prod.map_fst],
        slice_lhs 1 3 {rw t₃},
        rw [h''],
        erw ← pullback_cone.condition s,
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
    have m₁' : t' ≫ pullback.lift (hat_powerises (m'' m)).top (m'' m ≫ limits.prod.map (h'' m) (𝟙 f.left)) _ =
    pullback_cone.fst s := m₁,
    have m₂' : t' ≫ m.left ≫ _ = pullback_cone.snd s := m₂,
    clear m₁ m₂,
    rw ← cancel_mono (m'' m),
    change t' ≫ m' m ≫ magic_arrow f g = t ≫ m' m ≫ magic_arrow f g,
    apply prod.hom_ext,
    { rw [assoc, assoc],
      slice_lhs 3 4 {rw prod.lift_fst},
      rw m',
      rw m₂',
      rw ← t₃,
      rw assoc, refl },
    { conv_rhs {erw [assoc, t₂, ← m₁']},
      rw [assoc, assoc, assoc],
      slice_rhs 2 3 {rw limit.lift_π},
      dsimp,
      rw (hat_powerises (m'' m)).comm,
      rw [assoc, limits.prod.map_snd, comp_id],
      simp [m''] } },
  refine ⟨λ K, by apply_instance⟩,
end

end hat

def main' (f : over B) [has_power_object.{v} f.left] : is_power_object (over.mem f) :=
{ hat := λ b r m hm, by exactI make_arrow m,
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
      { rw [assoc, assoc],
        change _ ≫ k f = _ ≫ k f,
        rw [z₁, make_arrow, over.hom_mk_left, h'', k, hk, pullback.lift_snd_assoc, prod.lift_snd] },
    erw [make_arrow, limit.lift_π_assoc, prod.lift_fst],
    symmetry,
    apply unique_hat,
    change has_pullback_top _ _ _,
    rw prod_map_comp_id,
    apply left_right_hpb_to_both_hpb (h' f) _ has_pullback_top_of_pb,
    have: h' f = (over.mem f).left ≫ magic_arrow f (over_pow f),
    { apply prod.hom_ext,
      { rw [assoc, prod.lift_fst, ← over.comp_left, over.mem, prod.lift_fst], refl },
      { rw [assoc, prod.lift_snd, ← over.comp_left, over.mem, prod.lift_snd], refl } },
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
{ has_power_object := λ f, slicing.main f }

def comparison [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) (h : Π (J : Type v) [𝒥₁ : small_category J] [@fin_category J 𝒥₁], @preserves_limits_of_shape _ _ _ _ J 𝒥₁ F)
  (A : C) : F.obj (P A) ⟶ P (F.obj A) :=
begin
  let m := F.map (mem A) ≫ (prod_comparison F (P A) A),
  letI : mono (F.map (mem A)) := preserves_mono_of_preserves_pullback F _ _ _,
  exact hat m,
end

def comp_natural' [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) (h : Π (J : Type v) [𝒥₁ : small_category J] [@fin_category J 𝒥₁], @preserves_limits_of_shape _ _ _ _ J 𝒥₁ F)
  (A B : C) (f : B ⟶ A) :
  F.map (P_map f) ≫ comparison F h B = comparison F h A ≫ P_map (F.map f) :=
begin
  dsimp [comparison],
  rw [← hat_natural_left, ← hat_natural_right],
  let m₁ := F.map (mem A) ≫ (prod_comparison F (P A) A),
  let m₂ := F.map (mem B) ≫ (prod_comparison F (P B) B),
  letI : mono (F.map (mem A)) := preserves_mono_of_preserves_pullback F _ _ _,
  letI : mono (F.map (mem B)) := preserves_mono_of_preserves_pullback F _ _ _,
  letI : mono (F.map (Emap f)) := preserves_mono_of_preserves_pullback F _ _ _,
  let P₁ := pullback (F.map (mem B) ≫ (prod_comparison F (P B) B)) (limits.prod.map (F.map (P_map f)) (𝟙 (F.obj B))),
  let P₂ := pullback (F.map (mem A) ≫ (prod_comparison F (P A) A)) (limits.prod.map (𝟙 _) (F.map f)),
  let h₁ : P₁ ⟶ _ := pullback.snd,
  let h₂ : P₂ ⟶ _ := pullback.snd,
  change hat h₁ = hat h₂,
  let s₁ := (hat_powerises (Emap f)).is_pb,
  let s₂ := Epb f,
  let Fs₁ := preserves_pullback_cone F _ _ _ _ _ s₁,
  let Fs₂ := preserves_pullback_cone F _ _ _ _ _ s₂,
  have s₃comm : F.map (limits.prod.map (P_map f) (𝟙 B)) ≫ (prod_comparison F (P B) B) = (prod_comparison F (P A) B) ≫ limits.prod.map (F.map (P_map f)) (𝟙 (F.obj B)),
    rw [prod_comparison, prod_comparison],
    apply prod.hom_ext,
    { erw [assoc, prod.lift_fst, assoc, limits.prod.map_fst, ← F.map_comp, limits.prod.map_fst, prod.lift_fst_assoc, F.map_comp] },
    { erw [assoc, prod.lift_snd, assoc, limits.prod.map_snd, comp_id, ← F.map_comp, limits.prod.map_snd, comp_id, prod.lift_snd] },
  let s₃ := pullback_square_iso (F.map (limits.prod.map (P_map f) (𝟙 _))) (prod_comparison F (P A) B) (prod_comparison F (P B) B) (limits.prod.map (F.map (P_map f)) (𝟙 _)) s₃comm,
  let Fs₁s₃ := vpaste _ _ _ _ _ _ _ _ _ s₃ Fs₁,
  have eq₁: hat h₁ = hat (F.map (Emap f) ≫ (prod_comparison F (P A) B)),
  { apply lifting _ _ _ _,
    { apply Fs₁s₃.lift (limit.cone _) },
    { apply limit.lift _ (pullback_cone.mk (F.map (hat_powerises (Emap f)).top) (F.map (Emap f) ≫ (prod_comparison F (P A) B)) _),
      rw [assoc, ← s₃comm, ← assoc, ← F.map_comp, (hat_powerises (Emap f)).comm, F.map_comp, assoc], refl },
    { exact (Fs₁s₃.fac (limit.cone _) walking_cospan.right) },
    { rw limit.lift_π, refl } },
  have s₄comm : F.map (limits.prod.map (𝟙 (P A)) f) ≫ (prod_comparison F (P A) A) = (prod_comparison F (P A) B) ≫ limits.prod.map (𝟙 (F.obj (P A))) (F.map f),
    rw [prod_comparison, prod_comparison],
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, assoc, limits.prod.map_fst, ← F.map_comp, limits.prod.map_fst, comp_id, comp_id, prod.lift_fst] },
    { rw [assoc, prod.lift_snd, assoc, limits.prod.map_snd, ← F.map_comp, limits.prod.map_snd, prod.lift_snd_assoc, F.map_comp] },
  let s₄ := pullback_square_iso (F.map (limits.prod.map (𝟙 _) f)) (prod_comparison F (P A) B) (prod_comparison F (P A) A) (limits.prod.map (𝟙 _) (F.map f)) s₄comm,
  let Fs₂s₄ := vpaste _ _ _ _ _ _ _ _ _ s₄ Fs₂,
  have eq₂: hat h₂ = hat (F.map (Emap f) ≫ (prod_comparison F (P A) B)),
  { apply lifting _ _ _ _,
    { apply Fs₂s₄.lift (limit.cone _) },
    { apply limit.lift _ (pullback_cone.mk (F.map pullback.fst) (F.map (Emap f) ≫ (prod_comparison F (P A) B)) _),
      rw [assoc, ← s₄comm, ← assoc, ← F.map_comp, pullback.condition, F.map_comp, assoc], refl },
    { exact (Fs₂s₄.fac (limit.cone _) walking_cospan.right) },
    { rw limit.lift_π, refl } },
  rw [eq₁, eq₂],
end

-- Define F as a logical functor if this is an iso.
def comp_natural [has_power_objects.{v} C]
  {D : Type u₂} [category.{v} D] [has_finite_limits.{v} D] [has_power_objects.{v} D]
  (F : C ⥤ D) [h : Π (J : Type v) [𝒥₁ : small_category J] [@fin_category J 𝒥₁], @preserves_limits_of_shape _ _ _ _ J 𝒥₁ F] :
  (P_functor ⋙ F) ⟶ (F.op ⋙ P_functor) :=
{ app := λ A, comparison F h A.unop,
  naturality' := λ A B g, comp_natural' F h A.unop B.unop g.unop }

def star_power (A B : C) [has_power_object.{v} A] : (star B).obj (ni A) ⟶ (star B).obj (P A) ⨯ (star B).obj A :=
begin
  haveI := adjunction.right_adjoint_preserves_limits (forget_adj_star B),
  exact (star B).map (mem A) ≫ (prod_comparison (star B) (P A) A)
end
instance star_mono (A B : C) [has_power_object.{v} A] : mono (star_power A B) :=
begin
  haveI : mono ((star B).map (mem A)) := right_adjoint_preserves_mono (forget_adj_star B) (by apply_instance),
  haveI := adjunction.right_adjoint_preserves_limits (forget_adj_star B),
  rw star_power,
  haveI : is_iso (prod_comparison (star B) (P A) A) := by apply_instance,
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
  dsimp [star_power, the_iso, prod_comparison],
  rw [assoc, assoc, id_comp],
  apply prod.hom_ext,
  rw [assoc, assoc, assoc, prod.lift_fst, prod.lift_fst_assoc, limits.prod.map_fst, comp_id],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_fst, over.hom_mk_left, ← assoc, ← prod_map_id_comp, limits.prod.map_fst, comp_id],
  rw [assoc, assoc, assoc, prod.lift_snd, limits.prod.map_snd],
  apply prod.hom_ext,
  rw [assoc, assoc, assoc, assoc, prod.lift_fst, prod.lift_fst_assoc],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_fst, over.hom_mk_left, ← prod_map_id_comp_assoc, limits.prod.map_snd],
  rw [assoc, assoc, assoc, assoc, prod.lift_snd, prod.lift_snd],
  slice_rhs 2 3 {rw ← over.comp_left},
  rw [prod.lift_snd, over.hom_mk_left, ← prod_map_id_comp_assoc, limits.prod.map_snd],
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

  have b_pb := pullback_square_iso _ _ _ _ bottom_comm,
  have right₁_comm : 𝟙 (B ⨯ _) ≫ limits.prod.map (𝟙 _) (mem A) = (star_power A B ≫ (the_iso A ((star B).obj (P A))).hom).left ≫ (prod.associator B (P A) A).hom,
    apply seven_eleven_r_comm,
  have r₁_pb := pullback_square_iso' _ _ _ _ right₁_comm,
  have r₂_pb := pullback_prod' (mem A) B,
  have r_pb := (left_pb_to_both_pb _ _ _ _ _ _ _ _ _ r₁_pb) r₂_pb,
  have p : limits.prod.map (prod.lift g.hom k) (𝟙 A) ≫ (prod.associator B (P A) A).hom ≫ limits.prod.snd = limits.prod.map k (𝟙 A),
    rw [prod.associator_hom, prod.lift_snd],
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst, limits.prod.map_fst, prod.map_fst_assoc, prod.lift_snd] },
    { rw [assoc, prod.lift_snd, limits.prod.map_snd, limits.prod.map_snd] },
  refine ⟨_, _, subsingleton.elim _ _, subsingleton.elim _ _⟩,
  { intro q,
    refine cut_hpb_up _ _ _ _ _ _ _ _ b_pb,
    apply over_forget_reflects_hpb,
    refine right_both_hpb_to_left_hpb _ _ _ (has_pullback_top_of_is_pb r_pb),
    convert q },
  { intro q,
    have := stretch_hpb_down _ _ _ _ _ _ q _ b_pb,
    have := over_forget_preserves_hpb _ _ _ this,
    change has_pullback_top _ _ _,
    have p' := p.symm,
    convert left_hpb_right_pb_to_both_hpb _ _ _ _ _ _ this _ r_pb }
end

def seven_eleven (A B : C) [has_power_object.{v} A] : is_power_object (star_power A B) :=
{ hat := λ g r m hm, by exactI over.hom_mk (prod.lift g.hom (hat (m ≫ (the_iso A g).hom).left)) (limit.lift_π _ _),
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
  apply comp_natural' (star B) infer_instance X.unop Y.unop g.unop,
end

local attribute [instance] has_finite_products_of_has_finite_limits

def cc_of_pow [has_power_objects.{v} C] : cartesian_closed.{v} C :=
{ closed := λ B,
  begin
    haveI : is_right_adjoint (star B) := ⟨over.forget, forget_adj_star B⟩,
    haveI := monad.adjoint_lifting (logical_star B).symm (λ f g X Y r, by apply_instance),
    refine exponentiable_of_star_is_left_adj B _,
    apply left_adjoint_of_right_adjoint_op,
  end }

def lcc_of_pow [has_power_objects.{v} C] : is_locally_cartesian_closed.{v} C :=
{ overs_cc := λ B, cc_of_pow }

def subobj_hat {A B R : C} [exponentiable A] [has_subobject_classifier.{v} C] (m : R ⟶ B ⨯ A) [mono m] :
  B ⟶ A ⟹ classifier.Ω C :=
cartesian_closed.curry ((limits.prod.braiding _ _).inv ≫ classifier.classifier_of m)

def power_of_subobj (A : C) [exponentiable A] [has_subobject_classifier.{v} C] : has_power_object.{v} A :=
{ PA := A ⟹ classifier.Ω C,
  niA := pullback (classifier.truth C) ((limits.prod.braiding _ _).hom ≫ (ev A).app _),
  memA := pullback.snd,
  is_power :=
  { hat := λ B R m hm, by exactI subobj_hat m,
    powerises' := λ B R m hm,
    begin
      haveI := hm,
      apply right_both_hpb_to_left_hpb _ _ _ has_pullback_top_of_pb,
      erw [braid_natural_assoc, subobj_hat, curry_eq, prod_map_id_comp, assoc, (ev _).naturality,
           ev_coev_assoc, iso.hom_inv_id_assoc],
      apply classifier.classifies m,
    end,
    uniquely' := λ B R m hm hat' p,
    begin
      rw [subobj_hat, curry_eq_iff, iso.inv_comp_eq],
      apply classifier.uniquely,
      change has_pullback_top _ _ _,
      rw [uncurry_eq, ← braid_natural_assoc],
      apply left_right_hpb_to_both_hpb pullback.snd p has_pullback_top_of_pb,
    end } }

instance topos_has_power [has_subobject_classifier.{v} C] [cartesian_closed.{v} C] : has_power_objects.{v} C :=
⟨λ A, power_of_subobj A⟩

instance topos_has_some_colims (J : Type v) [small_category J] [has_subobject_classifier.{v} C] [cartesian_closed.{v} C] [has_limits_of_shape Jᵒᵖ C] :
  has_colimits_of_shape J C :=
some_colims J

instance topos_has_finite_colimits [has_subobject_classifier.{v} C] [cartesian_closed.{v} C] : has_finite_colimits.{v} C :=
λ _ _ _, by {resetI, apply_instance}

instance topos_is_lcc [has_subobject_classifier.{v} C] [cartesian_closed.{v} C] : is_locally_cartesian_closed.{v} C :=
lcc_of_pow

end category_theory