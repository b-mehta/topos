/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.over
import category_theory.limits.shapes.finite_limits
import category_theory.yoneda
import order.complete_lattice
import data.set.lattice

universes v u
namespace category_theory

/-- A sieve on X is a set of morphisms to X that is closed under left composition. -/
structure sieve {C : Type u} [category.{v} C] (X : C) :=
(arrows : set (over X))
(subs : ∀ {Y Z : C} {f : Y ⟶ X} (g : Z ⟶ Y), over.mk f ∈ arrows → over.mk (g ≫ f) ∈ arrows)

namespace sieve

variables {C : Type u} [category.{v} C]

variables {X Y Z : C} {S R : sieve X}

@[simp, priority 100]
lemma downward_closed (S : sieve X) {f : Y ⟶ X} (Hf : over.mk f ∈ S.arrows) (g : Z ⟶ Y) :
  over.mk (g ≫ f) ∈ S.arrows :=
S.subs g Hf

lemma arrow_ext : Π {R S : sieve X}, R.arrows = S.arrows → R = S
| ⟨Ra, _⟩ ⟨Sa, _⟩ rfl := rfl

@[ext] lemma ext_iff {R S : sieve X} : (∀ {Y} (f : Y ⟶ X), over.mk f ∈ R.arrows ↔ over.mk f ∈ S.arrows) → R = S :=
begin
  intros a,
  apply arrow_ext,
  ext ⟨_, _, _⟩,
  convert a x_hom;
  apply subsingleton.elim,
end

open lattice

/-- The supremum of a collection of sieves: just the union of them all. -/
protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := ⋃ (S : {i // i ∈ 𝒮}), S.1.arrows,
  subs :=
  begin
    rintros Y Z f g ⟨R, ⟨⟨S, hS⟩, rfl⟩, w⟩,
    refine ⟨_, ⟨⟨S, hS⟩, rfl⟩, _⟩,
    simp [w],
  end }

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def Inf (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := ⋂ (S : {S // S ∈ 𝒮}), S.1.arrows,
  subs :=
  begin
    rintros Y Z f g R _ ⟨⟨S, hS⟩, rfl⟩,
    simp [R _ ⟨⟨S, hS⟩, rfl⟩],
  end }

/-- The union of two sieves is a sieve. -/
protected def union (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∪ R.arrows,
  subs :=
  begin
    rintros Y Z f g (a | a);
    { simp [a] },
  end }

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∩ R.arrows,
  subs :=
  begin
    rintros Y Z f g ⟨h₁, h₂⟩,
    simp [h₁, h₂],
  end
}

/--
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional
properties.
-/
instance : complete_lattice (sieve X) :=
{ le           := λ S R, ∀ Y (f : Y ⟶ X), over.mk f ∈ S.arrows → over.mk f ∈ R.arrows,
  le_refl      := λ S f q, id,
  le_trans     := λ S₁ S₂ S₃ S₁₂ S₂₃ Y f h, S₂₃ _ _ (S₁₂ _ _ h),
  le_antisymm  := begin intros S R p q, ext, refine ⟨p _ _, q _ _⟩ end,
  top          := { arrows := set.univ, subs := λ Y Z f g h, ⟨⟩ },
  bot          := { arrows := ∅, subs := λ a aa Z g, false.elim },
  sup          := sieve.union,
  inf          := sieve.inter,
  Sup          := sieve.Sup,
  Inf          := sieve.Inf,
  le_Sup       := λ _ S hS _ _ h, ⟨_, ⟨⟨S, hS⟩, rfl⟩, h⟩,
  Sup_le       := begin rintros 𝒮 S hS Y f ⟨_, ⟨⟨T, hT⟩, rfl⟩, q⟩, apply hS _ hT _ _ q end,
  Inf_le       := λ _ S hS _ _ h, h _ ⟨⟨_, hS⟩, rfl⟩,
  le_Inf       := begin rintros 𝒮 S hS Y f h q ⟨⟨T, hT⟩, rfl⟩, apply hS _ hT _ _ h end,
  le_sup_left  := λ _ _ _ _, or.inl,
  le_sup_right := λ _ _ _ _, or.inr,
  sup_le       := begin rintros _ _ _ a b _ _ (q | q), apply a _ _ q, apply b _ _ q end,
  inf_le_left  := λ _ _ _ _, and.left,
  inf_le_right := λ _ _ _ _, and.right,
  le_inf       := begin intros _ _ _ p q _ _ z, exact ⟨p _ _ z, q _ _ z⟩,  end,
  le_top       := λ _ _ _ _, trivial,
  bot_le       := by { rintros _ _ _ ⟨⟩ } }

@[simp]
lemma mem_inter {R S : sieve X} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (R ⊓ S).arrows ↔ over.mk f ∈ R.arrows ∧ over.mk f ∈ S.arrows :=
iff.rfl

@[simp]
lemma mem_union {R S : sieve X} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (R ⊔ S).arrows ↔ over.mk f ∈ R.arrows ∨ over.mk f ∈ S.arrows :=
iff.rfl

@[simp]
lemma mem_top (f : Y ⟶ X) : over.mk f ∈ (⊤ : sieve X).arrows := trivial

instance : preorder      (sieve X) := by apply_instance
instance : partial_order (sieve X) := by apply_instance

inductive generate_sets (𝒢 : set (over X)) : over X → Prop
| basic : Π {f : over X}, f ∈ 𝒢 → generate_sets f
| subs  : Π {Y Z} {f : Y ⟶ X} (g : Z ⟶ Y), generate_sets (over.mk f) → generate_sets (over.mk (g ≫ f))

/-- Generate the smallest sieve containing the given set of arrows. -/
def generate (𝒢 : set (over X)) : sieve X :=
{ arrows := generate_sets 𝒢,
  subs   := λ Y Z f g t, generate_sets.subs _ t }

open order lattice

lemma sets_iff_generate {𝒢 : set (over X)} : generate 𝒢 ≤ S ↔ 𝒢 ⊆ S.arrows :=
iff.intro
  (λ H g hg,
    begin
      have : over.mk g.hom = g,
        cases g, dsimp [over.mk],
        congr' 1, apply subsingleton.elim,
      rw ← this at *,
      apply H,
      apply generate_sets.basic hg,
    end )
  (λ ss Y f hf, begin induction hf with hf_f hf_a hf_Y hf_Z hf_f hf_g hf_a hf_ih, apply ss hf_a, apply downward_closed, apply hf_ih end)

/-- Show that there is a galois insertion (generate, .arrows). -/
def gi_generate :
  @galois_insertion (set (over X)) (sieve X) (by apply_instance) _ generate sieve.arrows :=
  { gc        := λ s f, sets_iff_generate,
    choice    := λ 𝒢 f, generate 𝒢,
    choice_eq := λ 𝒢 h, rfl,
    le_l_u    := λ _ _ _, generate_sets.basic }

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
def pullback (S : sieve X) (h : Y ⟶ X) : sieve Y :=
{ arrows := {sl | over.mk (sl.hom ≫ h) ∈ S.arrows },
  subs := λ f hf Z g k, by { dsimp at k, simp [k] } }

@[simp] lemma mem_pullback (h : Y ⟶ X) {f : Z ⟶ Y} :
  over.mk f ∈ (pullback S h).arrows ↔ over.mk (f ≫ h) ∈ S.arrows := iff.rfl

/--
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X`
is in the sieve if `gf` factors through some `g : Z ⟶ Y` which is in `R`.
-/
def comp (R : sieve Y) (f : Y ⟶ X) : sieve X :=
{ arrows := λ gf, ∃ (g : gf.left ⟶ Y), over.mk g ∈ R.arrows ∧ g ≫ f = gf.hom,
  subs :=
  begin
    rintros Z₁ Z₂ g h ⟨j, k, z⟩,
    refine ⟨h ≫ j, _, _⟩,
    simp [k],
    simp [z],
  end }

-- def comps (R : Π (f : over X), sieve f.left) (S : sieve X) : sieve X :=
--   ⨆ (f ∈ S.arrows), comp (R f) f.hom

/-- Pullback is monotonic -/
lemma pullback_le_map {S R : sieve X} (Hss : S ≤ R) (f : Y ⟶ X) : pullback S f ≤ pullback R f :=
begin rintros Z H, apply Hss end

lemma pullback_top {f : Y ⟶ X} : pullback ⊤ f = ⊤ :=
top_unique (λ _ g, id)

lemma pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g :=
begin
  ext W h,
  simp,
end
lemma pullback_inter {f : Y ⟶ X} (S R : sieve X) : (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f :=
begin
  ext Z g,
  simp,
end

lemma le_pullback_comp {R : sieve Y} {f : Y ⟶ X} :
  R ≤ pullback (comp R f) f :=
begin rintros Z g b, refine ⟨_, _, rfl⟩, simpa end

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
lemma id_mem_iff_eq_top : over.mk (𝟙 X) ∈ S.arrows ↔ S = ⊤ :=
⟨begin
  intro h,
  rw eq_top_iff,
  rintros Y f ⟨⟩,
  suffices : over.mk (f ≫ (𝟙 _)) ∈ S.arrows,
    simpa using this,
  apply downward_closed _ h,
end,
by { rintro rfl, trivial } ⟩

lemma pullback_eq_top_iff_mem (f : Y ⟶ X) : over.mk f ∈ S.arrows ↔ S.pullback f = ⊤ :=
by rw [← id_mem_iff_eq_top, mem_pullback, category.id_comp]
-- lemma comp_le_comps
--   (R : Π (f : over X), sieve f.1)
--   (S : sieve X)
--   (f : over X)
--   (H : f ∈ S.arrows) :
--   comp (R f) f.hom ≤ comps R S  :=
-- calc comp (R f) f.hom ≤  ⨆ (_ : f ∈ S.arrows), comp (R f) f.hom : le_supr _ H
--                   ... ≤  comps R S                       : le_supr _ f

-- lemma comps_le
--   (R : Π (f : over X), sieve f.left)
--   (S : sieve X) :
--   comps R S ≤ S :=
-- begin
--   apply supr_le _,
--   rintros f,
--   apply supr_le _,
--   rintros H Y g,

--   rintros ⟨a,b,e⟩,

--   -- suffices : over.mk (g.hom) ∈ S.arrows, simp at this, apply this,
--   -- rw ← e,
--   -- apply downward_closed,
--   -- apply H,
-- end

/-- A sieve induces a presheaf. -/
@[simps]
def as_functor (S : sieve X) : Cᵒᵖ ⥤ Type v :=
{ obj := λ Y, {g : Y.unop ⟶ X // over.mk g ∈ S.arrows},
  map := λ Y Z f g, ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩ }

@[simps]
def le_as_functor {S T : sieve X} (h : S ≤ T) : S.as_functor ⟶ T.as_functor :=
{ app := λ Y f, ⟨f.1, h _ _ f.2⟩ }.

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functor_inclusion (S : sieve X) : S.as_functor ⟶ yoneda.obj X :=
{ app := λ Y f, f.1 }.

lemma le_as_functor_comm {S T : sieve X} (h : S ≤ T) :
  le_as_functor h ≫ functor_inclusion _ = functor_inclusion _ :=
begin
  ext c t,
  refl,
end

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functor_inclusion_is_mono : mono (functor_inclusion S) :=
⟨λ Z f g h, begin
  ext Y y,
  have : (f ≫ functor_inclusion S).app Y y = (g ≫ functor_inclusion S).app Y y,
    rw h,
  exact this
end⟩

end sieve
end category_theory
