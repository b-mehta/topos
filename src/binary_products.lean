/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.constructions.preserve_binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.comma
import pullbacks
import category_theory.adjunction.limits
import category_theory.pempty
import category_theory.limits.preserves

universes v u u' u₂

open category_theory category_theory.category category_theory.limits
namespace category_theory

section

variables {J K : Type v} [small_category J] [small_category K]
variables {C : Type u} [category.{v} C]

instance mono_prod_map {X Y Z W : C} (f : X ⟶ Y) (g : W ⟶ Z) [has_binary_products.{v} C] [mono f] [mono g] : mono (limits.prod.map f g) :=
⟨λ A h k l, begin
  apply prod.hom_ext,
  { rw [← cancel_mono f, assoc, assoc, ← limits.prod.map_fst f g, reassoc_of l] },
  { rw [← cancel_mono g, assoc, assoc, ← limits.prod.map_snd f g, reassoc_of l] },
end⟩

variables {F : J ⥤ C}

open category_theory.equivalence

def cone_equivalence_comp (e : K ≌ J) (c : cone F) : cone (e.functor ⋙ F) := cone.whisker e.functor c
def is_limit_equivalence_comp (e : K ≌ J) {c : cone F} (t : is_limit c) : is_limit (cone_equivalence_comp e c) :=
let e' := cones.postcompose (e.inv_fun_id_assoc F).hom in
{ lift := λ s, t.lift (e'.obj (cone.whisker e.inverse s)),
  fac' := λ s j,
  begin
    erw t.fac (e'.obj (cone.whisker e.inverse s)) (e.functor.obj j),
    dsimp [cones.postcompose, inv_fun_id_assoc],
    erw [id_comp, comp_id, counit_functor e j, s.w (e.unit_inv.app j)], refl,
  end,
  uniq' := λ s m w,
  begin
    apply t.hom_ext,
    intro j,
    erw [t.fac, ← c.w (e.counit_iso.hom.app j)],
    dsimp [cone_equivalence_comp, inv_fun_id_assoc],
    rw [id_comp, comp_id, ← w (e.inverse.obj j), assoc],
    refl,
  end }

end

-- def discrete_equiv_of_iso {J : Type u} {K : Type u₂} (h : J ≃ K) : discrete J ≌ discrete K :=
-- { functor := discrete.functor h.to_fun,
--   inverse := functor.of_function h.inv_fun,
--   unit_iso := nat_iso.of_components (λ X, eq_to_iso (h.left_inv X).symm) (λ X Y f, dec_trivial),
--   counit_iso := nat_iso.of_components (λ X, eq_to_iso (h.right_inv X)) (λ X Y f, dec_trivial) }

-- def pempty_equiv_discrete0 : pempty ≌ discrete (ulift (fin 0)) :=
-- begin
--   apply (functor.empty (discrete pempty)).as_equivalence.trans (discrete.equivalence _),
--   refine ⟨λ x, x.elim, λ ⟨t⟩, t.elim0, λ t, t.elim, λ ⟨t⟩, t.elim0⟩,
-- end

variables {C : Type u} [category.{v} C]

section
variables {D : Type u₂} [category.{v} D]

section

variables [has_finite_products.{v} C] [has_finite_products.{v} D] (F : C ⥤ D)

@[reassoc]
lemma thingy (A B : C) [is_iso (prod_comparison F A B)] :
  inv (prod_comparison F A B) ≫ F.map limits.prod.fst = limits.prod.fst :=
begin
  erw (as_iso (prod_comparison F A B)).inv_comp_eq,
  dsimp [as_iso_hom, prod_comparison],
  rw prod.lift_fst,
end

@[reassoc]
lemma thingy2 (A B : C) [is_iso (prod_comparison F A B)] :
  inv (prod_comparison F A B) ≫ F.map limits.prod.snd = limits.prod.snd :=
begin
  erw (as_iso (prod_comparison F A B)).inv_comp_eq,
  dsimp [as_iso_hom, prod_comparison],
  rw prod.lift_snd,
end

@[reassoc] lemma prod_comparison_inv_natural {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') [is_iso (prod_comparison F A B)] [is_iso (prod_comparison F A' B')] :
  inv (prod_comparison F A B) ≫ F.map (limits.prod.map f g) = limits.prod.map (F.map f) (F.map g) ≫ inv (prod_comparison F A' B') :=
begin
  erw [(as_iso (prod_comparison F A' B')).eq_comp_inv, assoc, (as_iso (prod_comparison F A B)).inv_comp_eq],
  apply prod_comparison_natural,
end

variables [preserves_limits_of_shape (discrete walking_pair) F]

end

/-- Transfer preservation of limits along a equivalence in the shape. -/
def preserves_limit_of_equiv {J₁ J₂ : Type v} [small_category J₁] [small_category J₂] (e : J₁ ≌ J₂) (F : C ⥤ D) [preserves_limits_of_shape J₁ F] :
  preserves_limits_of_shape J₂ F :=
{ preserves_limit := λ K,
  begin
    refine ⟨λ c t, _⟩,
    have : is_limit (F.map_cone (cone_equivalence_comp e c)),
      apply preserves_limit.preserves (is_limit_equivalence_comp e t),
      apply_instance,
    let l := is_limit_equivalence_comp e.symm this,
    let equ := e.inv_fun_id_assoc (K ⋙ F),
    apply (is_limit.of_cone_equiv (cones.postcompose_equivalence equ.symm).inverse l).of_iso_limit,
    apply cones.ext _ _,
    { apply iso.refl _ },
    { intro j,
      dsimp [cone_equivalence_comp, cones.postcompose, equivalence.inv_fun_id_assoc_hom_app],
      erw [id_comp, ← c.w (e.counit_iso.inv.app j)],
      change _ ≫ (e.inv_fun_id_assoc (K ⋙ F)).hom.app j = _,
      dsimp [equivalence.inv_fun_id_assoc],
      rw [id_comp, comp_id, ← F.map_comp, assoc, ← K.map_comp, cone.w] }
  end }

variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F] [preserves_limits_of_shape (discrete pempty) F]
variables [has_finite_products.{v} C] [has_finite_products.{v} D]

example : pempty.{u} ≃ ulift (fin 0) :=
begin
  apply (equiv.equiv_pempty _).symm,
  intro,
  apply a.1.elim0,
end

def preserves_fin_of_preserves_binary_and_terminal  :
  Π (n : ℕ), preserves_limits_of_shape (discrete (ulift (fin n))) F
| 0 := preserves_limit_of_equiv (begin apply discrete.equivalence (equiv.equiv_pempty _).symm, intro a, apply a.1.elim0, end : discrete pempty ≌ _) F
| (n+1) :=
  begin
    haveI p := preserves_fin_of_preserves_binary_and_terminal n,
    refine ⟨λ K, _⟩,

    let K' : discrete (ulift (fin n)) ⥤ C := discrete.functor (λ (i : ulift _), K.obj ⟨i.down.succ⟩),
    have p' : preserves_limit K' F,
      apply_instance,
    let c : cone K,
      refine ⟨K.obj ⟨0⟩ ⨯ limit K', _⟩,
      apply discrete.nat_trans _,
      rintro ⟨i⟩,
      revert i,
      refine fin.cases _ _,
      { apply limits.prod.fst },
      { intro i,
        apply limits.prod.snd ≫ limit.π K' ⟨i⟩ },
    have : is_limit c,
    { refine ⟨λ s, prod.lift (s.π.app ⟨0⟩) _, λ s, _, _⟩,
      { refine limit.lift K' ⟨s.X, _⟩,
        apply discrete.nat_trans (λ i, _),
        apply s.π.app ⟨i.down.succ⟩ },
      { rintro ⟨j⟩,
        revert j,
        refine fin.cases _ _,
        apply prod.lift_fst,
        intro i,
        dsimp, rw fin.cases_succ,
        rw prod.lift_snd_assoc,
        apply limit.lift_π },
      { intros s m w,
        apply prod.hom_ext,
        rw prod.lift_fst,
        apply w ⟨0⟩,
        rw prod.lift_snd,
        apply limit.hom_ext,
        rintro ⟨j⟩,
        simpa using w ⟨j.succ⟩ } },
    apply preserves_limit_of_preserves_limit_cone this,
    have q : is_limit (F.map_cone (limit.cone K')),
      apply p'.preserves, apply limit.is_limit,
    haveI := category_theory.limits.prod_comparison_iso_of_preserves_binary_prods F (K.obj ⟨0⟩) (limit K'),
    refine ⟨λ s, _, _, _⟩,
    { apply _ ≫ inv (prod_comparison F (K.obj ⟨0⟩) (limit K')),
      apply prod.lift (s.π.app ⟨0⟩) (q.lift ⟨_, discrete.nat_trans (λ i, _)⟩),
      exact s.π.app ⟨i.down.succ⟩ },
    { rintro s ⟨j⟩,
      revert j,
      refine fin.cases _ _,
      { dsimp,
        rw [assoc, thingy, prod.lift_fst] },
      { intro i,
        dsimp,
        rw [fin.cases_succ, F.map_comp, assoc, thingy2_assoc, prod.lift_snd_assoc],
        apply q.fac } },
    { intros s m w,
      dsimp at m,
      erw [(as_iso (prod_comparison F _ _)).eq_comp_inv, as_iso_hom, prod_comparison],
      apply prod.hom_ext,
      { rw [assoc, prod.lift_fst, prod.lift_fst], refine w ⟨0⟩ },
      { rw [assoc, prod.lift_snd, prod.lift_snd], apply q.hom_ext, intro j,
        rw [q.fac, assoc], dsimp,
        rw [← F.map_comp],
        have z : m ≫ F.map _ = _ := w ⟨j.down.succ⟩,
        dsimp at z,
        rw [fin.cases_succ] at z,
        convert z,
        ext1,
        refl } }
  end


def preserves_finite_limits_of_preserves_binary_and_terminal (J : Type v) [fintype J] [decidable_eq J] :
  preserves_limits_of_shape.{v} (discrete J) F :=
begin
  refine trunc.rec_on_subsingleton (fintype.equiv_fin J) _,
  intro e,
  replace e := e.trans equiv.ulift.symm,
  haveI := preserves_fin_of_preserves_binary_and_terminal F (fintype.card J),
  apply preserves_limit_of_equiv (discrete.equivalence e).symm,
end

end

variables [has_binary_products.{v} C] {B : C} [has_binary_products.{v} (over B)]
variables (f g : over B)

@[reducible]
def magic_arrow (f g : over B) :
  (g ⨯ f).left ⟶ g.left ⨯ f.left :=
prod.lift ((limits.prod.fst : g ⨯ f ⟶ g).left) ((limits.prod.snd : g ⨯ f ⟶ f).left)

-- This is an equalizer but we don't really need that
instance magic_mono : mono (magic_arrow f g) :=
begin
  refine ⟨λ Z p q h, _⟩,
  have h₁ := h =≫ limits.prod.fst,
  rw [assoc, assoc, prod.lift_fst] at h₁,
  have h₂ := h =≫ limits.prod.snd,
  rw [assoc, assoc, prod.lift_snd] at h₂,
  have: p ≫ (g ⨯ f).hom = q ≫ (g ⨯ f).hom,
    have: (g ⨯ f).hom = (limits.prod.fst : g ⨯ f ⟶ g).left ≫ g.hom := (over.w (limits.prod.fst : g ⨯ f ⟶ g)).symm,
    rw this,
    apply reassoc_of h₁,
  let Z' : over B := over.mk (q ≫ (g ⨯ f).hom),
  let p' : Z' ⟶ g ⨯ f := over.hom_mk p,
  let q' : Z' ⟶ g ⨯ f := over.hom_mk q,
  suffices: p' = q',
    show p'.left = q'.left,
    rw this,
  apply prod.hom_ext,
  ext1,
  exact h₁,
  ext1,
  exact h₂,
end

def magic_comm (f g h : over B) (k : f ⟶ g) :
  (limits.prod.map k (𝟙 h)).left ≫ magic_arrow h g = magic_arrow h f ≫ limits.prod.map k.left (𝟙 h.left) :=
begin
  apply prod.hom_ext,
  { rw [assoc, prod.lift_fst, ← over.comp_left, limits.prod.map_fst, assoc, limits.prod.map_fst, prod.lift_fst_assoc], refl },
  { rw [assoc, assoc, limits.prod.map_snd, comp_id, prod.lift_snd, ← over.comp_left, limits.prod.map_snd, comp_id, prod.lift_snd] }
end
def magic_pb (f g h : over B) (k : f ⟶ g) :
  is_limit (pullback_cone.mk (limits.prod.map k (𝟙 h)).left (magic_arrow h f) (magic_comm f g h k)) :=
begin
  refine is_limit.mk' _ _,
  intro s,
  have s₁ := pullback_cone.condition s =≫ limits.prod.fst,
    rw [assoc, assoc, prod.lift_fst, limits.prod.map_fst] at s₁,
  have s₂ := pullback_cone.condition s =≫ limits.prod.snd,
    rw [assoc, assoc, prod.lift_snd, limits.prod.map_snd, comp_id] at s₂,
  let sX' : over B := over.mk (pullback_cone.fst s ≫ (g ⨯ h).hom),
  have z : (pullback_cone.snd s ≫ limits.prod.snd) ≫ h.hom = sX'.hom,
    rw ← s₂,
    change (pullback_cone.fst s ≫ _) ≫ h.hom = pullback_cone.fst s ≫ (g ⨯ h).hom,
    rw ← over.w (limits.prod.snd : g ⨯ h ⟶ _),
    rw assoc,
  have z₂ : (pullback_cone.snd s ≫ limits.prod.fst) ≫ f.hom = pullback_cone.fst s ≫ (g ⨯ h).hom,
    rw ← over.w k,
    slice_lhs 1 3 {rw ← s₁},
    rw assoc,
    rw over.w (limits.prod.fst : g ⨯ h ⟶ _),
  let l : sX' ⟶ f := over.hom_mk (pullback_cone.snd s ≫ limits.prod.fst) z₂,
  let t : sX' ⟶ f ⨯ h := prod.lift l (over.hom_mk (pullback_cone.snd s ≫ limits.prod.snd) z),
  have t₁: t.left ≫ (limits.prod.fst : f ⨯ h ⟶ f).left = l.left,
    rw [← over.comp_left, prod.lift_fst],
  have t₂: t.left ≫ (limits.prod.snd : f ⨯ h ⟶ h).left = pullback_cone.snd s ≫ limits.prod.snd,
    rw [← over.comp_left, prod.lift_snd], refl,
  have fac: t.left ≫ magic_arrow h f = pullback_cone.snd s,
    apply prod.hom_ext,
    rw [assoc],
    change t.left ≫ magic_arrow h f ≫ limits.prod.fst = pullback_cone.snd s ≫ limits.prod.fst,
    rw [prod.lift_fst], exact t₁,
    rw ← t₂,
    rw assoc,
    change t.left ≫ magic_arrow h f ≫ limits.prod.snd = _,
    rw prod.lift_snd,
  refine ⟨t.left, _, fac, _⟩,
  rw [← cancel_mono (magic_arrow h g), pullback_cone.condition s, assoc],
  change t.left ≫ (limits.prod.map k (𝟙 h)).left ≫ magic_arrow h g =
    pullback_cone.snd s ≫ limits.prod.map k.left (𝟙 h.left),
  rw [magic_comm, ← fac, assoc],
  intros m m₁ m₂,
  rw ← cancel_mono (magic_arrow h f),
  erw m₂,
  exact fac.symm,
end

end category_theory