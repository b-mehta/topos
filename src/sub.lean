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
import category_theory.limits.shapes.regular_mono
import category_theory.closed.cartesian
import category_theory.limits.shapes.pullbacks
import category_theory.limits.over
import pullbacks

universes v u

namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C] {X Y Z : C}

structure sub' (X : C) :=
(arrow : over X)
[is_mono : mono arrow.hom]

@[simps]
def sub'.mk' {X A : C} (f : A ⟶ X) [hf : mono f] : sub'.{v} X := { arrow := over.mk f, is_mono := hf }

@[simp] lemma sub'_mk'_arrow {X A : C} (f : A ⟶ X) [hf : mono f] : (sub'.mk' f).arrow.hom = f := rfl

attribute [instance] sub'.is_mono

def factors_through {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop := ∃ k, k ≫ g = f

instance preorder_sub' : preorder (sub'.{v} X) :=
{ le := λ f g, factors_through f.1.hom g.1.hom,
  le_refl := λ f, ⟨𝟙 _, id_comp _⟩,
  le_trans :=
  begin
    rintros f g h ⟨k, r⟩ ⟨l, s⟩,
    refine ⟨k ≫ l, by simp [s, r]⟩,
  end }

def pullback_sub' [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub'.{v} Y) : sub'.{v} X :=
sub'.mk' (pullback.snd : pullback g.1.hom f ⟶ X)

@[simp] lemma pullback_sub'_arrow_hom [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub'.{v} Y) :
(pullback_sub' f g).arrow.hom = pullback.snd := rfl

@[mono] lemma pullback_preserves_le' [has_pullbacks.{v} C] (f : X ⟶ Y) {g₁ g₂ : sub'.{v} Y} (h : g₁ ≤ g₂) :
  pullback_sub' f g₁ ≤ pullback_sub' f g₂ :=
begin
  rcases h with ⟨h₁, h₂⟩,
  refine ⟨pullback.lift (pullback.fst ≫ h₁) pullback.snd (by simp [h₂, pullback.condition]), pullback.lift_snd _ _ _⟩,
end

lemma pullback_sub'_monotone [has_pullbacks.{v} C] (f : X ⟶ Y) : monotone (pullback_sub' f) := λ _ _, pullback_preserves_le' f

attribute [instance] mono_comp

def postcompose_sub' (f : X ⟶ Y) [mono.{v} f] (g : sub'.{v} X) : sub'.{v} Y :=
sub'.mk' (g.arrow.hom ≫ f)

@[simp] lemma postcompose_sub'_arrow_hom (f : X ⟶ Y) [mono.{v} f] (g : sub'.{v} X) :
(postcompose_sub' f g).arrow.hom = g.arrow.hom ≫ f := rfl

@[mono] lemma postcompose_preserves_le' (f : X ⟶ Y) [mono f] {g₁ g₂ : sub'.{v} X} (h : g₁ ≤ g₂) :
  postcompose_sub' f g₁ ≤ postcompose_sub' f g₂ :=
begin
  rcases h with ⟨h₁, h₂⟩,
  refine ⟨h₁, _⟩,
  apply reassoc_of h₂,
end

lemma pullback_is_le' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} Y} : postcompose_sub' f (pullback_sub' f g₁) ≤ g₁ :=
⟨pullback.fst, pullback.condition⟩

lemma pullback_is_le'' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} X} : pullback_sub' f (postcompose_sub' f g₁) ≤ g₁ :=
begin
  refine ⟨pullback.fst, _⟩,
  change pullback.fst ≫ g₁.arrow.hom = (pullback.snd : pullback (g₁.arrow.hom ≫ f) f ⟶ X),
  rw [← cancel_mono f, assoc, pullback.condition],
end
lemma pullback_is_le''' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} X} : g₁ ≤ pullback_sub' f (postcompose_sub' f g₁) :=
begin
  refine ⟨pullback.lift (𝟙 _) g₁.arrow.hom _, pullback.lift_snd _ _ _⟩,
  rw [id_comp], refl,
end

def equiv (X : C) : sub'.{v} X → sub'.{v} X → Prop := λ f g, f ≤ g ∧ g ≤ f

lemma equiv_is_equivalence : _root_.equivalence (@equiv _ _ X) :=
⟨λ f, ⟨le_refl _, le_refl _⟩, λ f g, and.symm, λ f g h a b, ⟨le_trans a.1 b.1, le_trans b.2 a.2⟩⟩

instance : setoid (sub' X) := ⟨equiv X, equiv_is_equivalence⟩

lemma pullback_sub'_id [has_pullbacks.{v} C] (x) : pullback_sub' (𝟙 X) x ≈ x :=
⟨⟨pullback.fst, by simp [pullback.condition]⟩, ⟨pullback.lift (𝟙 _) x.arrow.hom (by simp), pullback.lift_snd _ _ _⟩⟩

lemma pullback_sub'_comp [has_pullbacks.{v} C] {Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (a) :
  pullback_sub' (f ≫ g) a ≈ pullback_sub' f (pullback_sub' g a) :=
begin
  split,
  { refine ⟨pullback.lift (pullback.lift pullback.fst (pullback.snd ≫ _) _) _ (pullback.lift_snd _ _ _), pullback.lift_snd _ _ _⟩,
    rw [pullback.condition, assoc] },
  { refine ⟨pullback.lift (pullback.fst ≫ pullback.fst) _ _, pullback.lift_snd _ _ _⟩,
    dsimp, rw [assoc, pullback.condition], apply pullback.condition_assoc, },
end

lemma postcompose_sub'_id (x) : postcompose_sub' (𝟙 X) x ≈ x :=
by split; exact ⟨𝟙 _, by {dsimp, simp}⟩

local attribute [instance] mono_comp

lemma postcompose_sub'_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (a) : postcompose_sub' (f ≫ g) a ≈ postcompose_sub' g (postcompose_sub' f a) :=
by split; exact ⟨𝟙 _, by {dsimp, simp}⟩

def sub (X : C) := quotient ⟨equiv X, equiv_is_equivalence⟩
def sub.mk {X A : C} (f : A ⟶ X) [hf : mono f] : sub X := ⟦sub'.mk' f⟧

instance : has_le (sub X) :=
⟨ quotient.lift₂ (≤)
begin
  intros a₁ a₂ b₁ b₂ h₁ h₂,
  apply propext,
  refine ⟨λ a₁a₂, le_trans h₁.2 (le_trans a₁a₂ h₂.1), λ b₁b₂, le_trans h₁.1 (le_trans b₁b₂ h₂.2)⟩,
end ⟩

def preorder_sub : preorder (sub X) :=
{ le := has_le.le,
  le_refl := λ Y, quotient.ind le_refl Y,
  le_trans := λ A B C, quotient.induction_on₃ A B C (λ a b c, le_trans) }

instance sub_partial : partial_order (sub X) :=
{ le_antisymm := λ a b, quotient.induction_on₂ a b (λ _ _ h k, quotient.sound ⟨h, k⟩),
  ..preorder_sub }

def pullback_sub [has_pullbacks.{v} C] {Y : C} (f : X ⟶ Y) : sub Y → sub X :=
quotient.map (pullback_sub' f) $ λ a b ⟨_, _⟩, by split; mono

lemma pullback_sub_id [has_pullbacks.{v} C] (x : sub X) : pullback_sub (𝟙 X) x = x :=
quotient.induction_on x (λ a, quotient.sound (pullback_sub'_id a))

lemma pullback_sub_comp [has_pullbacks.{v} C] {Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x) : pullback_sub (f ≫ g) x = pullback_sub f (pullback_sub g x) :=
quotient.induction_on x (λ a, quotient.sound (pullback_sub'_comp f g a))

variable (C)

def sub.functor [has_pullbacks.{v} C] : Cᵒᵖ ⥤ Type (max u v) :=
{ obj := λ X, sub X.unop,
  map := λ X Y f, pullback_sub f.unop,
  map_id' := λ X, funext pullback_sub_id,
  map_comp' := λ X Y Z f g, funext (pullback_sub_comp g.unop f.unop) }

variable {C}

def postcompose {X Y : C} (f : X ⟶ Y) [mono f] : sub X → sub Y :=
quotient.map (postcompose_sub' f) $ λ a b ⟨_, _⟩, by split; mono

lemma postcompose_map_id : ∀ g, postcompose (𝟙 X) g = g :=
begin
  apply quotient.ind,
  intro a,
  apply quotient.sound (postcompose_sub'_id a),
end

lemma postcompose_map_comp {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] : ∀ h, postcompose (f ≫ g) h = postcompose g (postcompose f h) :=
begin
  apply quotient.ind,
  intro a,
  apply quotient.sound (postcompose_sub'_comp _ _ _),
end

@[simps]
def postcompose_sub_equiv_of_iso (e : X ≅ Y) : sub X ≃ sub Y :=
{ to_fun := postcompose e.hom,
  inv_fun := postcompose e.inv,
  left_inv := λ g, by simp_rw [← postcompose_map_comp, e.hom_inv_id, postcompose_map_id],
  right_inv := λ g, by simp_rw [← postcompose_map_comp, e.inv_hom_id, postcompose_map_id] }

lemma postcompose_pullback_comm' [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk f g comm)) (a) :
  postcompose_sub' g (pullback_sub' f a) ≈ pullback_sub' k (postcompose_sub' h a) :=
begin
  split,
  refine ⟨pullback.lift pullback.fst _ _, pullback.lift_snd _ _ _⟩,
  dsimp,
  rw [assoc, ← comm, pullback.condition_assoc],
  refine ⟨pullback.lift
            pullback.fst
            (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow.hom) pullback.snd _).1
            (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm, _⟩,
  { rw [← pullback.condition, assoc], refl },
  { erw [pullback.lift_snd_assoc], apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 },
end

def postcompose_pullback_comm [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) :
  ∀ p, postcompose g (pullback_sub f p) = pullback_sub k (postcompose h p) :=
begin
  apply quotient.ind,
  intro a,
  apply quotient.sound (postcompose_pullback_comm' t a),
end

lemma pullback_post [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] : ∀ g₁, pullback_sub f (postcompose f g₁) = g₁ :=
begin
  apply quotient.ind,
  intro a,
  apply quotient.sound,
  refine ⟨_, _⟩,
  exact pullback_is_le'' f,
  exact pullback_is_le''' f,

end

instance over_mono {B : C} {f g : over B} (m : f ⟶ g) [mono m] : mono m.left :=
⟨λ A h k e,
begin
  let A' : over B := over.mk (k ≫ f.hom),
  have: h ≫ f.hom = k ≫ f.hom,
    rw ← over.w m, rw reassoc_of e,
  let h' : A' ⟶ f := over.hom_mk h,
  let k' : A' ⟶ f := over.hom_mk k,
  have : h' ≫ m = k' ≫ m := over.over_morphism.ext e,
  rw cancel_mono m at this,
  injection this
end⟩

def over_mono' {B : C} {f g : over B} (m : f ⟶ g) [mono m.left] : mono m :=
{right_cancellation := λ A h k e, over.over_morphism.ext ((cancel_mono m.left).1 (congr_arg comma_morphism.left e))}

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

-- /!\ might be unstable
instance mono_term (A : C) : mono.{v} (⊤_ over A).hom :=
begin
  change mono (𝟙 _),
  apply_instance
end

def sub_one_over [has_terminal.{v} C] (A : C) : sub A ≌ sub (⊤_ (over A)) :=
begin
  refine preorder_equivalence _ _,
  { refine ⟨_, _, _, _⟩,
    { refine quotient.map _ _,
      { intro f,
        refine { arrow := over.mk (default (f.1 ⟶ _)), is_mono := @category_theory.over_mono' _ _ _ _ _ _ (id _) },
        refine ⟨λ Z g h eq, _⟩,
        apply f.is_mono.right_cancellation,
        exact eq },
      { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
        refine ⟨⟨over.hom_mk e₁ he₁, _⟩, ⟨over.hom_mk e₂ he₂, _⟩⟩,
        change (_ : _ ⟶ ⊤_ (over A)) = _,
        apply subsingleton.elim,
        change (_ : _ ⟶ ⊤_ (over A)) = _,
        apply subsingleton.elim } },
    { refine quotient.map _ _,
      { intro f,
        haveI := f.is_mono,
        refine { arrow := f.arrow.left, is_mono := _ },
        rw ← (show f.arrow.hom.left ≫ _ = f.arrow.left.hom, from over.w f.arrow.hom),
        apply mono_comp _ _,
        apply category_theory.over_mono,
        dsimp,
        apply category_theory.mono_term },
      { rintros f₁ f₂ ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩⟩,
        exact ⟨⟨e₁.left, over.w e₁⟩, ⟨e₂.left, over.w e₂⟩⟩ } },
    { intro f,
      apply quotient.induction_on f,
      intro f',
      apply quotient.sound,
      refine ⟨⟨𝟙 _, id_comp _⟩, ⟨𝟙 _, id_comp _⟩⟩ },
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
      refine ⟨over.hom_mk f hf, _⟩,
      dsimp,
      apply subsingleton.elim },
    { rintro ⟨f, hf⟩,
      dsimp at f hf,
      refine ⟨f.left, (over.w f)⟩ } },
end

def intersection' [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub'.{v} A) : sub'.{v} A :=
postcompose_sub' f₂.arrow.hom (pullback_sub' f₂.arrow.hom f₁)

lemma intersection'_le_left [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub'.{v} A) : intersection' f₁ f₂ ≤ f₁ :=
pullback_is_le' f₂.arrow.hom

lemma intersection'_le_right [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub'.{v} A) : intersection' f₁ f₂ ≤ f₂ :=
⟨pullback.snd, rfl⟩

lemma le_intersection' [has_pullbacks.{v} C] {A : C} {f₁ f₂ f₃ : sub'.{v} A} (h₁ : f₃ ≤ f₁) (h₂ : f₃ ≤ f₂) : f₃ ≤ intersection' f₁ f₂ :=
begin
  cases h₁, cases h₂,
  refine ⟨pullback.lift h₁_w h₂_w (by simp [h₁_h, h₂_h]), _⟩,
  erw [pullback.lift_snd_assoc, h₂_h],
end

def intersection [has_pullbacks.{v} C] {A : C} : sub A → sub A → sub A :=
begin
  refine quotient.map₂ intersection' _,
  rintros a₁ a₂ ⟨a₁₂, a₂₁⟩ b₁ b₂ ⟨b₁₂, b₂₁⟩,
  split;
  refine le_intersection' (le_trans (intersection'_le_left _ _) ‹_›) (le_trans (intersection'_le_right _ _) ‹_›),
end

def intersection_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ : sub A) (f₂ : sub'.{v} A) :
  intersection f₁ ⟦f₂⟧ = postcompose f₂.arrow.hom (pullback_sub f₂.arrow.hom f₁) :=
begin
  apply quotient.induction_on f₁,
  intro a,
  refl,
end

def sub'_top (A : C) : sub'.{v} A := sub'.mk' (𝟙 _)

@[simp]
lemma sub'_top_arrow_hom (A : C) : (sub'_top A).arrow.hom = 𝟙 _ := rfl

lemma sub'_le_top {A : C} (f : sub'.{v} A) : f ≤ sub'_top A :=
⟨f.arrow.hom, comp_id _⟩

def sub_top (A : C) : sub A := ⟦sub'_top A⟧

instance sub_order_top {A : C} : order_top (sub A) :=
{ top := sub_top A,
  le_top := λ f, quotient.induction_on f sub'_le_top,
  ..category_theory.sub_partial }

instance [has_pullbacks.{v} C] {B : C} : semilattice_inf_top (sub B) :=
{ inf := intersection,
  inf_le_left := λ m n, quotient.induction_on₂ m n intersection'_le_left,
  inf_le_right := λ m n, quotient.induction_on₂ m n intersection'_le_right,
  le_inf := λ k m n, quotient.induction_on₃ k m n (λ _ _ _, le_intersection'),
  ..category_theory.sub_order_top }

lemma prod_eq_inter {A : C} {f₁ f₂ : sub A} [has_pullbacks.{v} C] : (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
begin
  change f₁ ⊓ (f₂ ⊓ ⊤) = f₁ ⊓ f₂,
  rw inf_top_eq,
end

lemma inf_eq_intersection {B : C} (m m' : sub B) [has_pullbacks.{v} C] : m ⊓ m' = intersection m m' := rfl

lemma top_eq_top {B : C} : ⊤ = sub_top B := rfl

  -- (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) :
  -- ∀ p, postcompose g (pullback_sub f p) = pullback_sub k (postcompose h p)

def intersect_pullback [has_pullbacks.{v} C] {X Y : C} (g : X ⟶ Y) (f1 : sub Y) :
  ∀ f₂, pullback_sub g (f1 ⊓ f₂) = pullback_sub g f1 ⊓ pullback_sub g f₂ :=
quotient.ind $
begin
  intro f₂,
  erw [inf_eq_intersection, inf_eq_intersection, intersection_eq_post_pull,
       intersection_eq_post_pull, ←pullback_sub_comp,
       ←postcompose_pullback_comm pullback.condition (cone_is_pullback f₂.arrow.hom g),
       ←pullback_sub_comp, pullback.condition],
  refl
end

lemma top_le_pullback_self' {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] : sub'_top A ≤ pullback_sub' f (sub'.mk' f) :=
⟨_, pullback.lift_snd _ _ rfl⟩

lemma pullback_self'_eq_top {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] : pullback_sub' f (sub'.mk' f) ≈ sub'_top A :=
⟨sub'_le_top _, top_le_pullback_self' f⟩

lemma pullback_self_eq_top {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] : pullback_sub f (sub.mk f) = ⊤ :=
quotient.sound (pullback_self'_eq_top f)

lemma top_le_pullback'_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : sub'_top _ ≤ pullback_sub' f (sub'_top _) :=
⟨pullback.lift _ _ (by { dsimp, simp }), pullback.lift_snd _ _ _⟩

lemma pullback'_top_eq_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : pullback_sub' f (sub'_top _) ≈ sub'_top _ :=
⟨sub'_le_top _, top_le_pullback'_top f⟩

lemma pullback_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : pullback_sub f ⊤ = ⊤ :=
quotient.sound (pullback'_top_eq_top f)

local attribute [instance] has_pullbacks_of_has_finite_limits

variable [has_finite_limits.{v} C]

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

def exponentiate' (B : C) [exponentiable B] (A : sub'.{v} (⊤_ C)) : sub'.{v} (⊤_ C) :=
{ arrow := over.mk (default (B ⟹ A.1.left ⟶ ⊤_ C)),
  is_mono :=
  ⟨begin
    intros Z f g eq,
    apply uncurry_injective,
    haveI := A.is_mono,
    rw ← cancel_mono (A.1.hom),
    change (_ : B ⨯ Z ⟶ ⊤_ C) = _,
    apply subsingleton.elim,
  end⟩ }

@[mono] def exponentiate'_le (B : C) [exponentiable B] {A₁ A₂ : sub'.{v} (⊤_ C)} (h : A₁ ≤ A₂) : exponentiate' B A₁ ≤ exponentiate' B A₂ :=
begin
  cases h,
  refine ⟨(exp B).map h_w, _⟩,
  change (_ : _ ⟶ ⊤_ C) = _,
  apply subsingleton.elim,
end

def exponentiate₂' [cartesian_closed C] (B A : sub'.{v} (⊤_ C)) : sub' (⊤_ C) :=
exponentiate' B.1.left A

lemma universal [cartesian_closed C] {A₁ A₂ A₃ : sub'.{v} (⊤_ C)} : intersection' A₁ A₂ ≤ A₃ ↔ A₂ ≤ exponentiate₂' A₁ A₃ :=
begin
  refine ⟨λ k, _, λ k, _⟩,
  { cases k,
    dsimp [intersection'] at k_w k_h,
    refine ⟨cartesian_closed.curry (pullback.lift limits.prod.fst limits.prod.snd _ ≫ k_w), _⟩,
    change (_ : _ ⟶ ⊤_ C) = _,
    apply subsingleton.elim,
    change (_ : _ ⟶ ⊤_ C) = _,
    apply subsingleton.elim },
  { cases k,
    refine ⟨prod.lift pullback.fst pullback.snd ≫ cartesian_closed.uncurry k_w, _⟩,
    change (_ : _ ⟶ ⊤_ C) = _,
    apply subsingleton.elim }
end

@[mono] def exponentiate₂'_ge [cartesian_closed C] {B₁ B₂ A : sub'.{v} (⊤_ C)} (h : B₁ ≤ B₂) :
  exponentiate₂' B₂ A ≤ exponentiate₂' B₁ A :=
begin
  cases h,
  refine ⟨pre _ h_w, _⟩,
  change (_ : _ ⟶ ⊤_ C) = _,
  apply subsingleton.elim,
end

def exponential [cartesian_closed C] : sub (⊤_ C) → sub (⊤_ C) → sub (⊤_ C) :=
begin
  refine quotient.map₂ exponentiate₂' _,
  rintros a₁ a₂ ⟨a₁₂, a₂₁⟩ b₁ b₂ ⟨b₁₂, b₂₁⟩,
  split;
  refine (le_trans (exponentiate'_le _ ‹_›) (exponentiate₂'_ge ‹_›)),
end

def exp_e [cartesian_closed C] (B X Y : sub (⊤_ C)) : ((prod_functor.obj B).obj X ⟶ Y) ≃ (X ⟶ exponential B Y) :=
{ to_fun := λ k,
  ⟨⟨begin
    rcases k with ⟨⟨_⟩⟩,
    revert k,
    dsimp [prod_functor],
    rw [prod_eq_inter],
    apply quotient.induction_on₃ B X Y,
    introv,
    apply universal.1,
  end⟩⟩,
  inv_fun := λ k,
  ⟨⟨begin
      rcases k with ⟨⟨_⟩⟩,
      dsimp [prod_functor],
      rw [prod_eq_inter],
      revert k,
      apply quotient.induction_on₃ B X Y,
      introv,
      apply universal.2,
  end⟩⟩,
  left_inv := λ f, by ext,
  right_inv := λ f, by ext }

def exp_e_nat [cartesian_closed C] (B : sub (⊤_ C)) (X' X Y : sub (⊤_ C)) (f : X' ⟶ X) (g : (prod_functor.obj B).obj X ⟶ Y) :
    (exp_e B X' Y).to_fun ((prod_functor.obj B).map f ≫ g) = f ≫ (exp_e B X Y).to_fun g :=
by ext

def exponentiable_sub [cartesian_closed C] (B : sub (⊤_ C)) : exponentiable B :=
{ is_adj :=
  { right := adjunction.right_adjoint_of_equiv (exp_e B) (λ _ _ _ _ _, subsingleton.elim _ _),
    adj := adjunction.adjunction_of_equiv_right _ _ } }

instance cart_closed_one [cartesian_closed C] : cartesian_closed (sub (⊤_ C)) :=
{ closed := exponentiable_sub }

end category_theory
