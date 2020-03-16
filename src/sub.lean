/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import pullbacks
import comma
import category_theory.opposites

universes u v

namespace category_theory

open category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C] {X Y : C}
include 𝒞

def sub' (X : C) := {f : over X // mono f.hom}
def le : sub' X → sub' X → Prop := λ f g, ∃ (h : f.1.left ⟶ g.1.left), f.1.hom = h ≫ g.1.hom
lemma le_refl : reflexive (@le _ _ X) := λ f, ⟨𝟙 _, (category.id_comp _ _).symm⟩
lemma le_trans : transitive (@le _ _ X) :=
begin
  rintros f g h ⟨k, r⟩ ⟨l, s⟩,
  refine ⟨k ≫ l, r.trans _⟩,
  rw s, simp
end

@[simps]
def pullback_sub' [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub' Y) : sub' X :=
⟨over.mk (pullback.snd : pullback g.1.hom f ⟶ X), @pullback.snd_of_mono _ _ _ _ _ _ _ _ g.2⟩

lemma pullback_preserves_le' [has_pullbacks.{v} C] (f : X ⟶ Y) {g₁ g₂ : sub' Y} (h : le g₁ g₂) :
  le (pullback_sub' f g₁) (pullback_sub' f g₂) :=
begin
  cases h,
  refine ⟨_, _⟩,
  refine pullback.lift (pullback.fst ≫ h_w) pullback.snd _,
  slice_lhs 2 3 {rw ← h_h},
  apply pullback.condition,
  dsimp, simp,
end

@[simps]
def postcompose_sub' (f : X ⟶ Y) [mono f] (g : sub' X) : sub' Y :=
⟨over.mk (g.1.hom ≫ f), begin haveI := g.2, dsimp, apply_instance end⟩

lemma postcompose_preserves_le' (f : X ⟶ Y) [mono f] {g₁ g₂ : sub' X} (h : le g₁ g₂) :
  le (postcompose_sub' f g₁) (postcompose_sub' f g₂) :=
begin
  cases h with h k,
  use h,
  dsimp, simp [k]
end

def equiv (X : C) : sub' X → sub' X → Prop := λ f g, le f g ∧ le g f
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
  exact le,
  rintros _ _ _ _ ⟨a₁b₁, b₁a₁⟩ ⟨a₂b₂, b₂a₂⟩,
  rw eq_iff_iff,
  split,
    intro a₁a₂, apply le_trans b₁a₁ (le_trans a₁a₂ a₂b₂),
    intro b₁b₂, apply le_trans a₁b₁ (le_trans b₁b₂ b₂a₂)
end

instance : preorder (sub X) :=
{ le := has_le.le,
  le_refl := λ Y, quotient.ind le_refl Y,
  le_trans := λ A B C, begin apply quotient.induction_on₃ A B C, intros a b c, apply le_trans end }

instance : partial_order (sub X) :=
{ le := has_le.le, le_refl := preorder.le_refl, le_trans := preorder.le_trans,
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
-- quotient.map (postcompose_sub' f) (λ a b k, ⟨postcompose_preserves_le' f k.1, postcompose_preserves_le' f k.2⟩)

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
end category_theory
