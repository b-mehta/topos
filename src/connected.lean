/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.equalizers
import category_theory.limits.preserves
import category_theory.limits.over
import category_theory.comma
import to_mathlib
import binary_products
import creates

/-!
# Connected category

Define a connected category
-/

universes v₁ v₂ u₁ u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

/--
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits,
that forget: over B ⥤ C creates connected limits, and further that a category
has finite connected limits iff it has pullbacks and equalizers (the latter
is not yet done).
-/
class connected (J : Type v₂) [𝒥 : category.{v₁} J] extends inhabited J :=
(iso_constant : Π {α : Type v₂} (F : J ⥤ discrete α), F ≅ (functor.const J).obj (F.obj default))

section J
variables {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥

def any_functor_eq_constant [conn : connected J] {α : Type*} (F : J ⥤ discrete α) :
  F = (functor.const J).obj (F.obj (default J)) :=
begin
  apply functor.ext _ _,
    intro X,
    have z := conn.iso_constant,
    exact ((z F).hom.app X).down.1,
  intros, apply subsingleton.elim
end

def connected.of_any_functor_const_on_obj [inhabited J]
  (h : ∀ {α : Type v₂} (F : J ⥤ discrete α), ∀ (j : J), F.obj j = F.obj (default J)) :
  connected J :=
begin
  split,
  intros α F,
  specialize h F,
  apply nat_iso.of_components _ _,
  intro B, apply eq_to_iso (h B),
  intros, apply subsingleton.elim
end

@[simps]
def functor_to_discrete_of_preserves_morphisms {α : Type v₂} (F : J → α) (h : ∀ (j₁ j₂ : J) (f : j₁ ⟶ j₂), F j₁ = F j₂) : J ⥤ discrete α :=
{ obj := F,
  map := λ _ _ f, eq_to_hom (h _ _ f),
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, (eq_to_hom_trans _ _).symm }

/--
If J is connected, then for any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `connected.of_constant_of_preserves_morphisms`
-/
def constant_function_of_preserves_morphisms [connected J] {α : Type v₂} (F : J → α) (h : ∀ (j₁ j₂ : J) (f : j₁ ⟶ j₂), F j₁ = F j₂) (j : J) :
  F j = F (default J) :=
begin
  have := congr_arg (λ (t : J ⥤ discrete α), t.obj j) (any_functor_eq_constant (functor_to_discrete_of_preserves_morphisms F h)),
  exact this
end

/--
J is connected if: given any function F : J → α which is constant for any
j₁ j₂ for which there is a morphism j₁ ⟶ j₂, then F is constant.
This can be thought of as a local-to-global property.

The converse of `constant_function_of_preserves_morphisms`.
-/
def connected.of_constant_of_preserves_morphisms [inhabited J] (h : ∀ {α : Type v₂} (F : J → α), (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), F j₁ = F j₂) → (∀ j : J, F j = F (default J))) :
  connected J :=
connected.of_any_functor_const_on_obj (λ _ F, h F.obj (λ _ _ f, (F.map f).down.1))

def rec [connected J] (p : set J) (h0 : default J ∈ p) (h1 : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) (j : J) : j ∈ p :=
begin
  have := constant_function_of_preserves_morphisms (λ k, ulift.up (k ∈ p)) (λ j₁ j₂ f, _) j,
    swap,
    dsimp, exact congr_arg ulift.up (propext (h1 f)),
  injection this with i, rwa i,
end

/--
In other words, this says that any maximal connected component of J containing the default must be all of J.
-/
def connected.of_rec [inhabited J] (h : ∀ (p : set J), default J ∈ p → (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ (j : J), j ∈ p) :
  connected J :=
connected.of_constant_of_preserves_morphisms (λ α F a, h {j | F j = F (default J)} rfl (λ _ _ f, by simp [a f] ))

@[reducible]
def zag (j₁ j₂ : J) : Prop := nonempty (j₁ ⟶ j₂) ∨ nonempty (j₂ ⟶ j₁)
@[reducible]
def zigzag : J → J → Prop := relation.refl_trans_gen zag

/-- Any equivalence relation containing (⟶) holds for all pairs. -/
lemma equiv_relation [connected J] (r : J → J → Prop) (hr : _root_.equivalence r)
  (h : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), r j₁ j₂) :
  ∀ (j₁ j₂ : J), r j₁ j₂ :=
begin
  have z: ∀ (j : J), r (default J) j :=
    rec (λ k, r (default J) k)
        (hr.1 (default J)) (λ j₁ j₂ f, ⟨λ t, hr.2.2 t (h f), λ t, hr.2.2 t (hr.2.1 (h f))⟩),
  intros, apply hr.2.2 (hr.2.1 (z _)) (z _)
end

lemma connected_zigzag [connected J] (j₁ j₂ : J) : zigzag j₁ j₂ :=
equiv_relation _
  (mk_equivalence _
    relation.reflexive_refl_trans_gen
    (relation.refl_trans_gen.symmetric (λ _ _ _, by rwa [zag, or_comm]))
    relation.transitive_refl_trans_gen)
  (λ _ _ f, relation.refl_trans_gen.single (or.inl (nonempty.intro f))) _ _

omit 𝒥

def head' {α : Type v₂} : Π l : list α, l ≠ list.nil → α
| [] t := absurd rfl t
| (a :: l) _ := a

lemma exists_zigzag {α : Type v₂} {r : α → α → Prop} {a b : α} (h : relation.refl_trans_gen r a b) :
  ∃ (l : list α), list.chain' r l ∧ ∃ (hl : l ≠ list.nil), head' l hl = a ∧ list.last l hl = b :=
begin
  apply relation.refl_trans_gen.head_induction_on h,
  refine ⟨[b], list.chain.nil, list.cons_ne_nil _ _, rfl, rfl⟩,
  clear h a,
  intros c d e t ih,
  obtain ⟨l, hl₁, hl₂, hl₃, hl₄⟩ := ih,
  refine ⟨c :: l, _, _, _, _⟩,
  cases l,
    apply list.chain'_singleton,
    rw list.chain'_cons, split,
      rw head' at hl₃, rwa hl₃,
      assumption,
  apply list.cons_ne_nil,
  refl,
  rwa list.last_cons _ hl₂,
end

lemma prop_up_chain' {α : Type v₂} {r : α → α → Prop} (p : α → Prop) {a b : α}
  (l : list α) (hl : l ≠ []) (h : list.chain' r l)
  (ha : head' l hl = a) (hb : list.last l hl = b)
  (carries : ∀ {x y : α}, r x y → (p x ↔ p y)) (final : p b) : p a :=
begin
  induction l generalizing a,
    exfalso, apply hl, refl,
  rw head' at ha, cases ha,
  cases l_tl,
  rw list.last_singleton at hb, rw hb, assumption,
  rw list.chain'_cons at h,
  rw carries h.1,
  apply l_ih _ h.2, rwa list.last_cons at hb, apply list.cons_ne_nil,
  refl
end

include 𝒥
lemma exists_zigzag' [connected J] (j₁ j₂ : J) : ∃ (l : list J), list.chain' zag l ∧ ∃ (hl : l ≠ []), head' l hl = j₁ ∧ list.last l hl = j₂ :=
exists_zigzag (connected_zigzag _ _)

def connected_of_zigzag [inhabited J] (h : ∀ (j₁ j₂ : J), ∃ (l : list J), list.chain' zag l ∧ ∃ (hl : l ≠ []), head' l hl = j₁ ∧ list.last l hl = j₂) :
  connected J :=
begin
  apply connected.of_rec,
  intros p d k j,
  obtain ⟨l, zags, nemp, hd, tl⟩ := h j (default J),
  apply prop_up_chain' p l nemp zags hd tl _ d,
  rintros _ _ (⟨⟨_⟩⟩ | ⟨⟨_⟩⟩),
  apply k a, symmetry, apply k a
end

end J

section examples
instance cospan_inhabited : inhabited walking_cospan := ⟨walking_cospan.one⟩

def cospan_connected : connected (walking_cospan) :=
begin
  apply connected.of_rec,
  introv _ t, cases j,
  { rwa t walking_cospan.hom.inl },
  { rwa t walking_cospan.hom.inr },
  { assumption }
end

instance parallel_pair_inhabited : inhabited walking_parallel_pair := ⟨walking_parallel_pair.one⟩

def parallel_pair_connected : connected (walking_parallel_pair) :=
begin
  apply connected.of_rec,
  introv _ t, cases j,
  { rwa t walking_parallel_pair_hom.left },
  { assumption }
end
end examples

section C
variables {J : Type v₂} [𝒥 : category.{v₁} J]
include 𝒥

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

@[simps]
def functor_from_nat_trans {X Y : C} (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) : J ⥤ discrete (X ⟶ Y) :=
{ obj := α.app,
  map := λ A B f, eq_to_hom (by { have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm }),
  map_id' := λ A, rfl,
  map_comp' := λ A₁ A₂ A₃ f g, (eq_to_hom_trans _ _).symm
}

def nat_trans_from_connected [conn : connected J] {X Y : C} (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  ∀ (j : J), α.app j = (α.app (default J) : X ⟶ Y) :=
@constant_function_of_preserves_morphisms _ _ _
  (X ⟶ Y)
  (λ j, α.app j)
  (λ _ _ f, (by { have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm }))

end C

local attribute [tidy] tactic.case_bash

variables {C : Type u₂} [𝒞 : category.{v₂} C]
include 𝒞

section products

variables [has_binary_products.{v₂} C]

variables {J : Type v₂} [small_category J]

@[simps]
def γ₂ {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ K :=
{ app := λ Y, limits.prod.snd }

@[simps]
def γ₁ {K : J ⥤ C} (X : C) : K ⋙ prod_functor.obj X ⟶ (functor.const J).obj X :=
{ app := λ Y, limits.prod.fst }

@[simps]
def forget_cone {X : C} {K : J ⥤ C} (s : cone (K ⋙ prod_functor.obj X)) : cone K :=
{ X := s.X,
  π := s.π ≫ γ₂ X }

def prod_preserves_connected_limits [connected J] (X : C) :
  preserves_limits_of_shape J (prod_functor.obj X) :=
{ preserves_limit := λ K,
  { preserves := λ c l,
    { lift := λ s, limits.prod.lift (s.π.app (default _) ≫ limits.prod.fst) (l.lift (forget_cone s)),
      fac' := λ s j,
      begin
        apply prod.hom_ext,
        { rw assoc,
          erw limit.map_π,
          erw comp_id,
          rw limit.lift_π,
          exact (nat_trans_from_connected (s.π ≫ γ₁ X) j).symm },
        { have: l.lift (forget_cone s) ≫ c.π.app j = s.π.app j ≫ limits.prod.snd := l.fac (forget_cone s) j,
          rw ← this,
          simp }
      end,
      uniq' := λ s m L,
      begin
        apply prod.hom_ext,
        { rw limit.lift_π,
          rw ← L (default J),
          dsimp,
          rw assoc,
          rw limit.map_π,
          erw comp_id },
        { rw limit.lift_π,
          apply l.uniq (forget_cone s),
          intro j,
          dsimp,
          rw ← L j,
          simp }
      end } } }

end products

variables {J : Type v₂} [𝒥 : small_category J]
include 𝒥

namespace over

namespace creates

@[simps]
def nat_trans_in_over {B : C} (F : J ⥤ over B) :
  F ⋙ forget ⟶ (functor.const J).obj B :=
{ app := λ j, (F.obj j).hom }

@[simps]
def raise_cone [conn : connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) :
  cone F :=
{ X := @over.mk _ _ B c.X (c.π.app (default J) ≫ (F.obj (default J)).hom),
  π :=
  { app := λ j, over.hom_mk (c.π.app j) (nat_trans_from_connected (c.π ≫ nat_trans_in_over F) j) } }

lemma raised_cone_lowers_to_original [conn : connected J] {B : C} {F : J ⥤ over B} (c : cone (F ⋙ forget)) (t : is_limit c) :
  forget.map_cone (raise_cone c) = c :=
by tidy

omit 𝒥
instance forget_reflects_iso {B : C} : reflects_isomorphisms (forget : over B ⥤ C) :=
{reflects := λ X Y f t, { inv := over.hom_mk t.inv (by { exact (@as_iso _ _ _ _ (forget.map f) t).inv_comp_eq.2 (over.w f).symm }) } }
include 𝒥

def raised_cone_is_limit [conn : connected J] {B : C} {F : J ⥤ over B} {c : cone (F ⋙ forget)} (t : is_limit c) :
  is_limit (raise_cone c) :=
{ lift := λ s, over.hom_mk (t.lift (forget.map_cone s))
               (by { dsimp, slice_lhs 1 2 {rw t.fac}, exact over.w (s.π.app (default J)) }),
  uniq' :=
  begin
    intros s m K,
    ext1,
    dsimp at K ⊢,
    apply t.hom_ext,
    intro j,
    rw t.fac,
    dsimp,
    rw ← K j,
    refl,
  end }

end creates

def forget_creates_connected_limits [conn : connected J] {B : C} : creates_limits_of_shape J (forget : over B ⥤ C) :=
{ creates_limit := λ K,
    creates_limit_of_reflects_iso (λ c t,
      { lifted :=
        { above_cone := creates.raise_cone c,
          above_hits_original := eq_to_iso (creates.raised_cone_lowers_to_original c t) },
        makes_limit := creates.raised_cone_is_limit t } ) }

end over

end category_theory