/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.opposites
import category_theory.limits.lattice
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.full_subcategory
import pullbacks
import comma
import cartesian_closed

universes u v

namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C] {X Y : C}
include 𝒞

def sub' (X : C) := {f : over X // mono f.hom}

instance : preorder (sub' X) :=
{ le := λ f g, ∃ (h : f.1.left ⟶ g.1.left), f.1.hom = h ≫ g.1.hom,
  le_refl := λ f, ⟨𝟙 _, (id_comp _).symm⟩,
  le_trans :=
  begin
    rintros f g h ⟨k, r⟩ ⟨l, s⟩,
    refine ⟨k ≫ l, r.trans _⟩,
    rw s, simp
  end }

@[simps]
def pullback_sub' [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub' Y) : sub' X :=
⟨over.mk (pullback.snd : pullback g.1.hom f ⟶ X), @pullback.snd_of_mono _ _ _ _ _ _ _ _ g.2⟩

lemma pullback_preserves_le' [has_pullbacks.{v} C] (f : X ⟶ Y) {g₁ g₂ : sub' Y} (h : g₁ ≤ g₂) :
  (pullback_sub' f g₁) ≤ (pullback_sub' f g₂) :=
begin
  cases h,
  refine ⟨_, _⟩,
  refine pullback.lift (pullback.fst ≫ h_w) pullback.snd _,
  slice_lhs 2 3 {rw ← h_h},
  apply pullback.condition,
  dsimp, simp,
end

attribute [instance] mono_comp

@[simps]
def postcompose_sub' (f : X ⟶ Y) [mono f] (g : sub' X) : sub' Y :=
⟨over.mk (g.1.hom ≫ f), begin haveI := g.2, apply mono_comp end⟩

lemma postcompose_preserves_le' (f : X ⟶ Y) [mono f] {g₁ g₂ : sub' X} (h : g₁ ≤ g₂) :
  postcompose_sub' f g₁ ≤ postcompose_sub' f g₂ :=
begin
  cases h with h k,
  use h,
  dsimp, simp [k]
end

def equiv (X : C) : sub' X → sub' X → Prop := λ f g, f ≤ g ∧ g ≤ f
lemma equiv_is_equivalence : _root_.equivalence (@equiv _ _ X) :=
begin
  refine ⟨λ f, ⟨le_refl _, le_refl _⟩, λ f g ⟨k, l⟩, ⟨l, k⟩, λ f g h, _⟩,
  rintro ⟨a, b⟩ ⟨c, d⟩,
  refine ⟨le_trans a c, le_trans d b⟩,
end

instance : setoid (sub' X) := ⟨equiv X, equiv_is_equivalence⟩
def sub (X : C) := quotient ⟨equiv X, equiv_is_equivalence⟩

instance : has_le (sub X) :=
begin
  split,
  refine quotient.lift₂ _ _,
  exact (≤),
  rintros _ _ _ _ ⟨a₁b₁, b₁a₁⟩ ⟨a₂b₂, b₂a₂⟩,
  rw eq_iff_iff,
  split,
    intro a₁a₂, apply le_trans b₁a₁ (le_trans a₁a₂ a₂b₂),
    intro b₁b₂, apply le_trans a₁b₁ (le_trans b₁b₂ b₂a₂)
end

def preorder_sub : preorder (sub X) :=
{ le := has_le.le,
  le_refl := λ Y, quotient.ind le_refl Y,
  le_trans := λ A B C, begin apply quotient.induction_on₃ A B C, intros a b c, apply le_trans end }

instance sub_partial : partial_order (sub X) :=
{ le := has_le.le, le_refl := preorder_sub.le_refl, le_trans := preorder_sub.le_trans,
  le_antisymm :=
  begin
    intros A B,
    apply quotient.induction_on₂ A B,
    rintros a b k l,
    apply quotient.sound,
    split, exact k, exact l
  end }

def sub_map [has_pullbacks.{v} C] {Y : C} (f : X ⟶ Y) : sub Y → sub X :=
begin
  refine quotient.lift (λ g, quotient.mk (pullback_sub' f g)) _,
  rintros a b ⟨k, l⟩,
  apply quotient.sound,
  split,
  apply pullback_preserves_le' _ k,
  apply pullback_preserves_le' _ l
end

lemma sub_map_id [has_pullbacks.{v} C] (x : sub X) : sub_map (𝟙 X) x = x :=
begin
  apply quotient.induction_on x,
  intro a,
  dsimp [sub_map], apply quotient.sound, split,
  { dsimp [pullback_sub'],
    refine ⟨pullback.fst, _⟩, dsimp, rw pullback.condition, simp },
  { dsimp [pullback_sub'],
    refine ⟨pullback.lift (𝟙 _) a.val.hom _, _⟩, dsimp,
    simp, simp }
end
lemma sub_map_comp [has_pullbacks.{v} C] {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : sub Z) : sub_map (f ≫ g) x = sub_map f (sub_map g x) :=
begin
  apply quotient.induction_on x,
  intro a,
  dsimp [sub_map], apply quotient.sound,
  split,
  { dsimp [pullback_sub'],
  refine ⟨pullback.lift (pullback.lift pullback.fst (pullback.snd ≫ f) _) pullback.snd _, _⟩,
  rw pullback.condition, simp,
  simp, simp },
  { dsimp [pullback_sub'],
  refine ⟨pullback.lift (pullback.fst ≫ pullback.fst) pullback.snd _, _⟩,
  slice_lhs 2 3 {rw pullback.condition},
  slice_lhs 1 2 {rw pullback.condition},
  simp,
  simp },
end

variable (C)

def sub.functor [has_pullbacks.{v} C] : Cᵒᵖ ⥤ Type (max u v) :=
{ obj := λ X, sub (X.unop),
  map := λ X Y f, sub_map f.unop,
  map_id' := λ X,
  begin
    ext, apply sub_map_id
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext, apply sub_map_comp
  end
}

variable {C}

def postcompose {X Y : C} (f : X ⟶ Y) [mono f] : sub X → sub Y :=
begin
  refine quotient.lift (λ g, quotient.mk (postcompose_sub' f g)) _,
  intros a b k,
  apply quotient.sound,
  exact ⟨postcompose_preserves_le' f k.1, postcompose_preserves_le' f k.2⟩,
end

lemma postcompose_map_id (g : sub X) : postcompose (𝟙 X) g = g :=
begin
  apply quotient.induction_on g,
  intro a,
  dsimp [postcompose],
  apply quotient.sound,
  split,
  use 𝟙 _,
  dsimp [postcompose_sub'], simp,
  use (𝟙 _),
  dsimp [postcompose_sub'], simp,
end

lemma postcompose_map_comp {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (h : sub X) : postcompose (f ≫ g) h = postcompose g (postcompose f h) :=
begin
  apply quotient.induction_on h,
  intro a,
  dsimp [postcompose],
  apply quotient.sound,
  split,
  refine ⟨𝟙 _, _⟩,
  dsimp, simp,
  refine ⟨𝟙 _, _⟩, dsimp, simp
end

def sub_iso_compose (e : X ≅ Y) : sub X ≃ sub Y :=
{ to_fun := postcompose e.hom,
  inv_fun := postcompose e.inv,
  left_inv :=
  begin
    intro g,
    rw ← postcompose_map_comp,
    simp only [iso.hom_inv_id],
    rw postcompose_map_id
  end,
  right_inv :=
  begin
    intro g,
    rw ← postcompose_map_comp,
    simp only [iso.inv_hom_id],
    rw postcompose_map_id
  end
}

def postcompose_sub_comm [has_pullbacks.{v} C] {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W) [mono h] [mono g] (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) (p : sub Y) :
  postcompose g (sub_map f p) = sub_map k (postcompose h p) :=
begin
  apply quotient.induction_on p,
  intro a,
  dsimp [postcompose, sub_map],
  apply quotient.sound,
  split;
  refine ⟨_, _⟩,
  apply pullback.lift pullback.fst (pullback.snd ≫ g) _,
  slice_rhs 2 3 {rw ← comm},
  dsimp [postcompose_sub'],
  slice_lhs 1 2 {rw pullback.condition}, rw category.assoc,
  dsimp, rw limit.lift_π,
  refl,
  apply pullback.lift pullback.fst _ _,
  apply t.lift (pullback_cone.mk (pullback.fst ≫ a.val.hom) pullback.snd _),
  rw ← pullback.condition,
  rw category.assoc, refl,
  erw t.fac (pullback_cone.mk (pullback.fst ≫ a.val.hom) pullback.snd _) walking_cospan.left, refl,
  dsimp,
  rw ← category.assoc,
  rw limit.lift_π, dsimp,
  erw t.fac _ walking_cospan.right, refl,
end

instance over_mono {B : C} {f g : over B} (m : f ⟶ g) [mono m] : mono m.left :=
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

omit 𝒞
@[simps]
def preorder_functor {α β : Type*} [preorder α] [preorder β] (f : α → β) (hf : monotone f) : α ⥤ β :=
{ obj := f,
  map := λ X Y ⟨⟨h⟩⟩, ⟨⟨hf h⟩⟩ }

@[simps]
def preorder_equivalence {α β : Type*} [preorder α] [preorder β] (f : α ≃ β)
  (hf : ∀ {x y}, x ≤ y ↔ f.to_fun x ≤ f.to_fun y) : α ≌ β :=
{ functor := preorder_functor f.to_fun (λ x y, hf.1),
  inverse := preorder_functor f.inv_fun (λ a b h, by rwa [hf, f.right_inv, f.right_inv]),
  unit_iso := nat_iso.of_components (λ X, eq_to_iso (f.left_inv _).symm) (λ X Y f, rfl),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso (f.right_inv _)) (λ X Y f, rfl) }

include 𝒞

def forward (A : C) : sub A ⥤ sub (⊤_ (over A)) :=
begin
  refine preorder_functor _ _,
  { refine quotient.map (λ f, _) _,
    { haveI := f.2,
      refine ⟨over.mk (default (f.1 ⟶ _)), @category_theory.over_mono' _ _ _ _ _ _ (id _)⟩,
      refine ⟨λ Z g h eq, _⟩,
      apply f.2.right_cancellation,
      exact eq },
    { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
      refine ⟨⟨over.hom_mk e₁ he₁.symm, _⟩, over.hom_mk e₂ he₂.symm, _⟩,
      change (_ : _ ⟶ ⊤_ (over A)) = _,
      apply subsingleton.elim,
      change (_ : _ ⟶ ⊤_ (over A)) = _,
      apply subsingleton.elim } },
  { rintros a b,
    apply quotient.induction_on₂ a b,
    rintros ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ ⟨t, ht⟩,
    refine ⟨over.hom_mk t ht.symm, _⟩,
    change (_ : _ ⟶ ⊤_ (over A)) = _,
    apply subsingleton.elim }
end

-- /!\ might be unstable
instance mono_term (A : C) : mono.{v} (⊤_ over A).hom :=
begin
  change mono (𝟙 _),
  apply_instance
end

def backward (A : C) : sub (⊤_ over A) ⥤ sub A :=
begin
  refine preorder_functor _ _,
  { refine quotient.map (λ f, _) _,
    { haveI := f.2,
      refine ⟨f.1.left, _⟩,
      rw ← (show f.1.hom.left ≫ _ = f.1.left.hom, from over.w f.1.hom),
      apply mono_comp _ _,
      apply category_theory.over_mono,
      dsimp,
      apply category_theory.mono_term },
    { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
      exact ⟨⟨e₁.left, (over.w e₁).symm⟩, ⟨e₂.left, (over.w e₂).symm⟩⟩ } },
  { rintros a b,
    apply quotient.induction_on₂ a b,
    rintros ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ ⟨t, ht⟩,
    refine ⟨t.left, (over.w t).symm⟩ },
end

def sub_one_over [has_terminal.{v} C] (A : C) : sub A ≌ sub (⊤_ (over A)) :=
begin
  refine preorder_equivalence _ _,
  { refine ⟨_, _, _, _⟩,
    { refine quotient.map _ _,
      { intro f,
        haveI := f.2,
        refine ⟨over.mk (default (f.1 ⟶ _)), @category_theory.over_mono' _ _ _ _ _ _ (id _)⟩,
        refine ⟨λ Z g h eq, _⟩,
        apply f.2.right_cancellation,
        exact eq },
      { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
        refine ⟨⟨over.hom_mk e₁ he₁.symm, _⟩, over.hom_mk e₂ he₂.symm, _⟩,
        change (_ : _ ⟶ ⊤_ (over A)) = _,
        apply subsingleton.elim,
        change (_ : _ ⟶ ⊤_ (over A)) = _,
        apply subsingleton.elim } },
    { refine quotient.map _ _,
      { intro f,
        haveI := f.2,
        refine ⟨f.1.left, _⟩,
        rw ← (show f.1.hom.left ≫ _ = f.1.left.hom, from over.w f.1.hom),
        apply mono_comp _ _,
        apply category_theory.over_mono,
        dsimp,
        apply category_theory.mono_term },
      { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
        exact ⟨⟨e₁.left, (over.w e₁).symm⟩, ⟨e₂.left, (over.w e₂).symm⟩⟩ } },
    { intro f,
      apply quotient.induction_on f,
      intro f',
      apply quotient.sound,
      refine ⟨⟨𝟙 _, (id_comp _).symm⟩, ⟨𝟙 _, (id_comp _).symm⟩⟩ },
    { intro f,
      apply quotient.induction_on f,
      intro f',
      apply quotient.sound,
      refine ⟨⟨𝟙 _, _⟩, ⟨𝟙 _, _⟩⟩,
      dsimp,
      apply subsingleton.elim,
      dsimp,
      apply subsingleton.elim } },
  { apply quotient.ind₂,
    intros a b,
    dsimp,
    refine ⟨_, _⟩,
    { rintro ⟨f, hf⟩,
      refine ⟨over.hom_mk f hf.symm, _⟩,
      dsimp,
      apply subsingleton.elim },
    { rintro ⟨f, hf⟩,
      dsimp at f hf,
      refine ⟨f.left, (over.w f).symm⟩ } },
end

def intersection [has_pullbacks.{v} C] {A : C} : sub A → sub A → sub A :=
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

def is_le_left [has_pullbacks.{v} C] {A : C} : ∀ (m n : sub A), intersection m n ≤ m :=
begin
  apply quotient.ind₂,
  intros m n,
  exact ⟨pullback.snd, rfl⟩,
end

def is_le_right [has_pullbacks.{v} C] {A : C} : ∀ (m n : sub A), intersection m n ≤ n :=
begin
  apply quotient.ind₂,
  intros m n,
  exact ⟨pullback.fst, pullback.condition.symm⟩,
end

def universal [has_pullbacks.{v} C] {A : C} : ∀ {k m n : sub A}, k ≤ m → k ≤ n → k ≤ intersection m n :=
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

def sub_top (B : C) : sub B := ⟦⟨over.mk (𝟙 B), by { dsimp, apply_instance }⟩⟧

instance sub_order_top {B : C} : order_top (sub B) :=
{ top := sub_top B,
  le_top :=
  begin
    apply quotient.ind, intro a,
    refine ⟨a.1.hom, (comp_id _).symm⟩,
  end,
  ..category_theory.sub_partial }

instance [has_pullbacks.{v} C] {B : C} : semilattice_inf_top (sub B) :=
{ inf := intersection,
  inf_le_left := is_le_left,
  inf_le_right := is_le_right,
  le_inf := by apply universal,
  top := sub_top B,
  le_top := quotient.ind
  begin
    intro a,
    refine ⟨a.1.hom, (comp_id _).symm⟩,
  end,
  ..category_theory.sub_partial }

lemma top_eq_top {B : C} : ⊤ = sub_top B := rfl

lemma pullback_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : sub_map f ⊤ = ⊤ :=
begin
  rw eq_top_iff,
  refine ⟨pullback.lift f (𝟙 _) (by { dsimp, simp }), (pullback.lift_snd _ _ _).symm⟩,
end

lemma inf_eq_intersection {B : C} (m m' : sub B) [has_pullbacks.{v} C] : m ⊓ m' = intersection m m' := rfl

local attribute [instance] has_pullbacks_of_has_finite_limits

def exponentiate' [has_finite_limits.{v} C] (B : C) [exponentiable B] (A : sub' (⊤_ C)) : sub' (⊤_ C) :=
begin
  refine ⟨over.mk (default (exp B A.1.left ⟶ ⊤_ C)), _⟩,
  dsimp,
  refine ⟨λ Z f g eq, _⟩,
  apply uncurry_injective,
  haveI := A.2,
  rw ← cancel_mono (A.1.hom : _ ⟶ ⊤_ C),
  change (_ : B ⨯ Z ⟶ ⊤_ C) = _,
  apply subsingleton.elim,
end

def exponentiate'_le [has_finite_limits.{v} C] (B : C) [exponentiable B] {A₁ A₂ : sub' (⊤_ C)} (h : A₁ ≤ A₂) : exponentiate' B A₁ ≤ exponentiate' B A₂ :=
begin
  cases h,
  refine ⟨post B h_w, _⟩,
  change (_ : _ ⟶ ⊤_ C) = _,
  apply subsingleton.elim,
end

def exponentiate₂' [has_finite_limits.{v} C] [is_cartesian_closed C] (B : sub' (⊤_ C)) (A : sub' (⊤_ C)) : sub' (⊤_ C) :=
exponentiate' B.1.left A

def exponentiate₂'_ge [has_finite_limits.{v} C] [is_cartesian_closed C] {B₁ B₂ : sub' (⊤_ C)} (A : sub' (⊤_ C)) (h : B₁ ≤ B₂) :
  exponentiate₂' B₂ A ≤ exponentiate₂' B₁ A :=
begin
  cases h,
  refine ⟨pre _ h_w, _⟩,
  change (_ : _ ⟶ ⊤_ C) = _,
  apply subsingleton.elim,
end

def exponential [has_finite_limits.{v} C] [is_cartesian_closed C] : sub (⊤_ C) → sub (⊤_ C) → sub (⊤_ C) :=
begin
  apply quotient.map₂ exponentiate₂' (λ B₁ B₂ hB A₁ A₂ hA, _),
  apply_instance,
  exact ⟨le_trans (exponentiate'_le _ hA.1) (exponentiate₂'_ge _ hB.2), le_trans (exponentiate'_le _ hA.2) (exponentiate₂'_ge _ hB.1)⟩,
end

def exp_e [has_finite_limits.{v} C] [is_cartesian_closed C] (B X Y : sub (⊤_ C)) : ((prod_functor.obj B).obj X ⟶ Y) ≃ (X ⟶ exponential B Y) :=
{ to_fun :=
  begin
    refine quotient.rec_on B _ _,
    refine quotient.rec_on X _ _,
    refine quotient.rec_on Y _ _,
    intros b x y h,
    refine ⟨⟨_⟩⟩,
    rcases h with ⟨⟨_, _⟩⟩,
    dsimp at h_w,
    dsimp at h_h,
    refine ⟨_, _⟩,
    apply cart_closed.curry,
    apply pullback.lift (pullback.lift (default _) limits.prod.snd (subsingleton.elim _ _)) limits.prod.fst (subsingleton.elim _ _) ≫ h_w,
    change (_ : _ ⟶ ⊤_ C) = _,
    apply subsingleton.elim,
    intros y₁ y₂ p,
    apply subsingleton.elim,
    intros _ _ _,
    apply subsingleton.elim,
    intros _ _ _,
    apply subsingleton.elim,
  end,
  inv_fun :=
  begin
    refine quotient.rec_on B _ _,
    refine quotient.rec_on X _ _,
    refine quotient.rec_on Y _ _,
    intros b x y h,
    refine ⟨⟨_⟩⟩,
    rcases h with ⟨⟨_, _⟩⟩,
    dsimp [exponentiate₂', exponentiate'] at h_w,
    refine ⟨prod.lift pullback.snd (pullback.fst ≫ pullback.snd) ≫ cart_closed.uncurry h_w, _⟩,
    change (_ : _ ⟶ ⊤_ C) = _,
    apply subsingleton.elim,
    intros _ _ _,
    apply subsingleton.elim,
    intros _ _ _,
    apply subsingleton.elim,
    intros _ _ _,
    apply subsingleton.elim,
  end,
  left_inv := λ f, by ext,
  right_inv := λ f, by ext }

def exp_e_nat [has_finite_limits.{v} C] [is_cartesian_closed C] (B : sub (⊤_ C)) (X' X Y : sub (⊤_ C)) (f : X' ⟶ X) (g : (prod_functor.obj B).obj X ⟶ Y) :
    (exp_e B X' Y).to_fun ((prod_functor.obj B).map f ≫ g) = f ≫ (exp_e B X Y).to_fun g :=
begin
  intros,
  ext
end

def exponentiable_sub [has_finite_limits.{v} C] [is_cartesian_closed C] (B : sub (⊤_ C)) : exponentiable B :=
{ is_adj :=
  { right := adjunction.right_adjoint_of_equiv (exp_e B) (λ _ _ _ _ _, subsingleton.elim _ _),
    adj := adjunction.adjunction_of_equiv_right _ _ } }

instance cart_closed_one [has_finite_limits.{v} C] [is_cartesian_closed C] : is_cartesian_closed (sub (⊤_ C)) :=
{ cart_closed := exponentiable_sub }

end category_theory
