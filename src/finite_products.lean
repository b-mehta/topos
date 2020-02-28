/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal
import tactic.rcases
import pfin

/-! # Stuff that should be in the catthy library. -/
namespace category_theory

universe w
def discrete.equiv_of_iso {J K : Type w} (h : J ≃ K) : (discrete J ≌ discrete K) :=
equivalence.mk
  (functor.of_function h.to_fun) -- C ⥤ D
  (functor.of_function h.inv_fun) -- D ⥤ C
  { hom := {
      app := λ X, begin
        apply eq_to_hom,
        simp only [functor.id_obj, functor.of_function_obj, functor.comp_obj],
        exact (h.left_inv X).symm,
      end,
      naturality' := λ X Y f, dec_trivial },
    inv := {
      app := λ X, begin
        apply eq_to_hom,
        simp only [functor.id_obj, functor.of_function_obj, functor.comp_obj],
        exact h.left_inv X,
      end,
      naturality' := λ X Y f, dec_trivial },
    hom_inv_id' := by ext1; exact dec_trivial,
    inv_hom_id' := by ext1; exact dec_trivial }
  { hom := {
      app := λ X, begin
        apply eq_to_hom,
        simp only [functor.id_obj, functor.of_function_obj, functor.comp_obj],
        exact h.right_inv X
      end,
      naturality' := λ X Y f, dec_trivial },
    inv := {
      app := λ X, begin
        apply eq_to_hom,
        simp only [functor.id_obj, functor.of_function_obj, functor.comp_obj],
        exact (h.right_inv X).symm,
      end,
      naturality' := λ X Y f, dec_trivial },
    hom_inv_id' := by ext1; exact dec_trivial,
    inv_hom_id' := by ext1; exact dec_trivial }

namespace limits

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

lemma prod.lift_fst {X Y Z : C} [has_limit (pair X Y)] (f : Z ⟶ X) (g : Z ⟶ Y) : prod.lift f g ≫ prod.fst = f :=
by simp only [binary_fan.mk_π_app_left, limit.lift_π]

lemma prod.lift_snd {X Y Z : C} [has_limit (pair X Y)] (f : Z ⟶ X) (g : Z ⟶ Y) : prod.lift f g ≫ prod.snd = g :=
by simp only [binary_fan.mk_π_app_right, limit.lift_π]

lemma prod.lift_uniq {X Y Z : C} [has_limit (pair X Y)] (f : Z ⟶ X) (g : Z ⟶ Y) (m : Z ⟶ X ⨯ Y)
  (hLeft : m ≫ prod.fst = f) (hRight : m ≫ prod.snd = g)
  : m = prod.lift f g :=
begin
  apply limit.hom_ext,
  intro j,
  cases hLeft, cases hRight, cases j,
    simp only [limit.lift_π, binary_fan.mk_π_app_left],
  simp only [limit.lift_π, binary_fan.mk_π_app_right],
end

end limits
end category_theory

/-!
# Constructing finite products from binary products and a terminal object

If a category has all binary products, and a terminal object, then it has all finite products.
-/

namespace category_theory.limits
open category_theory

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- We hide the "implementation details" inside a namespace
namespace has_finite_products_of_binary_products_and_terminal_object

@[reducible]
def match_statement_lol [has_binary_products.{v} C]
  {n : ℕ} (F: discrete (pfin (nat.succ n)) ⥤ C) (limF': has_limit (discrete.lift pfin.succ ⋙ F))
  : Π (j: pfin (nat.succ n)), F.obj ⟨0, nat.succ_pos n⟩ ⨯ limF'.cone.X ⟶ F.obj j
| ⟨0, _⟩ := prod.fst
| w@⟨nat.succ j, _⟩ := prod.snd ≫
  limF'.cone.π.app (w.pred (λ h, nat.succ_ne_zero j (pfin.veq_of_eq h)))

set_option eqn_compiler.zeta true
def has_limit_for_pfin_diagram [has_binary_products.{v} C] [has_terminal.{v} C]
: Π {n: ℕ} (F: (discrete (pfin n)) ⥤ C)
, has_limit F
| 0 F :=
  -- In the base case, the category of cones over a diagram of shape ∅ is simply 𝒞, so
  -- the limit cone is 𝒞's terminal object.
  let absurdJ (x : pfin 0) : false := x.elim0 in
  let myCone : cone F :=
    { X := terminal C,
      π := nat_trans.of_homs (λ j, (absurdJ j).elim) } in
  { cone := myCone,
    is_limit :=
      { lift := λ s, terminal.from s.X
      , fac' := λ s j, (absurdJ j).elim
      , uniq' := λ s m h, dec_trivial } }

| (nat.succ n) F :=
  -- In the inductive case, we construct a limit cone with apex (F 0) ⨯ (apex of smaller limit cone)
  -- where the smaller cone is obtained from the below functor.
  let F' : discrete (pfin n) ⥤ C := discrete.lift pfin.succ ⋙ F in
  let limF' : has_limit F' := has_limit_for_pfin_diagram F' in
  let myCone : cone F :=
    { X := (F.obj ⟨0, nat.succ_pos n⟩) ⨯ limF'.cone.X
    , π := nat_trans.of_homs (match_statement_lol F limF') } in -- TODO(WN): using an actual match statement here
                                                                -- is hard to unfold later, but would obv be nicer.
  { cone := myCone,
    is_limit :=
      { lift := λ s,
          -- Show that s.X is also the apex of a cone over F' ..
          let s' : cone F' :=
            { X := s.X
            , π := nat_trans.of_homs (λ j, s.π.app j.succ) } in
          -- .. in order to get from s.X to limF'.cone.X in the right morphism
          -- using the fact that limF' is a limit cone over F'.
          prod.lift
            (s.π.app $ ⟨0, nat.succ_pos n⟩)
            (eq_to_hom rfl ≫ limF'.is_limit.lift s')
      -- Show that lift is in fact a morphism of cones from s into myCone.
      , fac' := λ s j, begin
        rcases j with ⟨j, hj⟩, cases j;
        simp only [category.id_comp, nat_trans.of_homs_app, eq_to_hom_refl, match_statement_lol,
          prod.lift_fst, limit.lift_π_assoc, is_limit.fac, nat_trans.of_homs_app,
          binary_fan.mk_π_app_right], congr
      end
      -- Show that lift is the unique morphism into myCone.
      , uniq' := λ s m h, begin
        have h0 := h ⟨0, nat.succ_pos n⟩,
        simp [match_statement_lol] at h0,
        let s' : cone F' :=
          { X := s.X
          , π := nat_trans.of_homs (λ j, s.π.app j.succ) },
        have hS : m ≫ prod.snd = eq_to_hom rfl ≫ limF'.is_limit.lift s',
        { -- m ≫ prod.snd is a morphism of cones over F' into limF'.X ..
          have hN : ∀ (j: discrete (pfin n)), (m ≫ prod.snd) ≫ limF'.cone.π.app j = s'.π.app j,
          { intro j,
            unfold_projs, simp [(h j.succ).symm],
            rcases j with ⟨j, hj⟩, refl },
          -- .. and therefore unique.
          have hUniq' : m ≫ prod.snd = limF'.is_limit.lift s',
          from limF'.is_limit.uniq' s' (m ≫ prod.snd) hN,
          simp only [hUniq', category.id_comp, eq_to_hom_refl] },
        exact prod.lift_uniq _ _ _ h0 hS
      end } }
set_option eqn_compiler.zeta false

end has_finite_products_of_binary_products_and_terminal_object

open has_finite_products_of_binary_products_and_terminal_object

-- TODO(WN): instance or def? Is there another way one might want to construct limits of shape pfin?
instance has_limits_of_shape_pfin [has_binary_products.{v} C] [has_terminal.{v} C] (n : ℕ)
  : @has_limits_of_shape (discrete $ pfin n) _ C 𝒞 :=
⟨λ F, has_limit_for_pfin_diagram F⟩

-- TODO(WN): trunc? #22
def has_trunc_finite_products [has_binary_products.{v} C] [has_terminal.{v} C]
  {J : Type v} [fintype J] [decidable_eq J]
  : trunc (has_limits_of_shape (discrete J) C) :=
trunc.lift_on (fintype.equiv_pfin J)
  (λ h,
    let hIso : discrete (pfin $ fintype.card J) ≌ discrete J :=
      discrete.equiv_of_iso h.symm in
    let limsPfin : @has_limits_of_shape (discrete (pfin $ fintype.card J)) _ C 𝒞 :=
      by apply_instance in
    trunc.mk $ has_limits_of_shape_of_equivalence hIso)
  (λ a b, trunc.eq _ _)

end category_theory.limits
