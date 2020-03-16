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

-- TODO: should be pretty easy to make this work without the pullbacks: use the map as just composition with the iso
def preserves_iso [has_pullbacks.{v} C] {X Y : C} (e : X ≅ Y) : sub X ≃ sub Y :=
{ to_fun := sub_map e.inv,
  inv_fun := sub_map e.hom,
  left_inv :=
  begin
    intro g, rw ← sub_map_comp,
    rw e.hom_inv_id, rw sub_map_id
  end,
  right_inv :=
  begin
    intro f, rw ← sub_map_comp,
    rw e.inv_hom_id, rw sub_map_id
  end
}
end category_theory
