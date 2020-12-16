/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.shapes.pullbacks
import category_theory.comma
import category_theory.adjunction.limits
import category_theory.pempty
import category_theory.limits.preserves.basic
import category_theory.limits.preserves.shapes.products
import category.pullbacks

universes v u u' u₂

noncomputable theory
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
def is_limit_equivalence_comp (e : K ≌ J) {c : cone F} (t : is_limit c) : is_limit (cone.whisker e.functor c) :=
is_limit.whisker_equivalence t _

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
def preserves_limit_of_equiv {J₁ J₂ : Type v} [small_category J₁] [small_category J₂] (e : J₁ ≌ J₂)
  (F : C ⥤ D) [preserves_limits_of_shape J₁ F] :
  preserves_limits_of_shape J₂ F :=
{ preserves_limit := λ K,
  begin
    refine ⟨λ c t, _⟩,
    have : is_limit (F.map_cone (cone.whisker e.functor c)),
      apply is_limit_of_preserves F (is_limit.whisker_equivalence t e),
    have := is_limit.whisker_equivalence this e.symm,
    let equ := e.inv_fun_id_assoc (K ⋙ F),
    apply ((is_limit.postcompose_hom_equiv equ _).symm this).of_iso_limit,
    apply cones.ext _ _,
    { apply iso.refl _ },
    { intro j,
      dsimp,
      simp [←functor.map_comp] },
  end }

@[simps {rhs_md := semireducible}]
def build_prod {n : ℕ} {f : ulift (fin (n+1)) → C}
  (c₁ : fan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩))
  (c₂ : binary_fan (f ⟨0⟩) c₁.X) :
fan f :=
fan.mk c₂.X
begin
  rintro ⟨i⟩,
  revert i,
  refine fin.cases _ _,
  { apply c₂.fst },
  { intro i,
    apply c₂.snd ≫ c₁.π.app (ulift.up i) },
end

def build_limit {n : ℕ} (f : ulift (fin (n+1)) → C)
  {c₁ : fan (λ (i : ulift (fin n)), f ⟨i.down.succ⟩)} {c₂ : binary_fan (f ⟨0⟩) c₁.X}
  (t₁ : is_limit c₁) (t₂ : is_limit c₂) :
  is_limit (build_prod c₁ c₂) :=
{ lift := λ s,
  begin
    apply (binary_fan.is_limit.lift' t₂ _ _).1,
    { apply s.π.app ⟨0⟩ },
    { apply t₁.lift ⟨_, discrete.nat_trans (λ i, s.π.app ⟨i.down.succ⟩)⟩ }
  end,
  fac' := λ s,
  begin
    rintro ⟨j⟩,
    revert j,
    rw fin.forall_fin_succ,
    split,
    { apply (binary_fan.is_limit.lift' t₂ _ _).2.1 },
    { intro i,
      dsimp only [build_prod_π_app],
      rw [fin.cases_succ, ← assoc, (binary_fan.is_limit.lift' t₂ _ _).2.2, t₁.fac],
      refl }
  end,
  uniq' := λ s m w,
  begin
    apply binary_fan.is_limit.hom_ext t₂,
    { rw (binary_fan.is_limit.lift' t₂ _ _).2.1,
      apply w ⟨0⟩ },
    { rw (binary_fan.is_limit.lift' t₂ _ _).2.2,
      apply t₁.uniq ⟨_, _⟩,
      rintro ⟨j⟩,
      rw assoc,
      dsimp only [discrete.nat_trans_app],
      rw ← w ⟨j.succ⟩,
      dsimp only [build_prod_π_app],
      rw fin.cases_succ }
  end }

variables (F : C ⥤ D) [preserves_limits_of_shape (discrete walking_pair) F] [preserves_limits_of_shape (discrete pempty) F]
variables [has_finite_products.{v} C] [has_finite_products.{v} D]

def fin0_equiv_pempty : fin 0 ≃ pempty :=
equiv.equiv_pempty (λ a, a.elim0)

lemma has_scalar.ext {R M : Type*} : ∀ (a b : has_scalar R M), a.smul = b.smul → a = b
| ⟨_⟩ ⟨_⟩ rfl := rfl

noncomputable def preserves_fin_of_preserves_binary_and_terminal  :
  Π (n : ℕ) (f : ulift (fin n) → C), preserves_limit (discrete.functor f) F
| 0 := λ f,
  begin
    letI : preserves_limits_of_shape (discrete (ulift (fin 0))) F :=
      preserves_limit_of_equiv (discrete.equivalence (equiv.ulift.trans fin0_equiv_pempty).symm) _,
    apply_instance,
  end
| (n+1) :=
  begin
    haveI := preserves_fin_of_preserves_binary_and_terminal n,
    intro f,
    refine preserves_limit_of_preserves_limit_cone
      (build_limit f (limit.is_limit _) (limit.is_limit _)) _,
    apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _,
    let := build_limit (λ i, F.obj (f i))
              (is_limit_of_has_product_of_preserves_limit F _)
              (is_limit_of_has_binary_product_of_preserves_limit F _ _),
    refine is_limit.of_iso_limit this _,
    apply cones.ext _ _,
    apply iso.refl _,
    rintro ⟨j⟩,
    revert j,
    refine fin.cases _ _,
    { symmetry,
      apply category.id_comp _ },
    { intro i,
      symmetry,
      dsimp,
      rw [fin.cases_succ, fin.cases_succ],
      change 𝟙 _ ≫ F.map _ = F.map _ ≫ F.map _,
      rw [id_comp, ← F.map_comp],
      refl }
  end

def preserves_ulift_fin_of_preserves_binary_and_terminal (n : ℕ) :
  preserves_limits_of_shape (discrete (ulift (fin n))) F :=
{ preserves_limit := λ K,
  begin
    let : discrete.functor K.obj ≅ K := discrete.nat_iso (λ i, iso.refl _),
    haveI := preserves_fin_of_preserves_binary_and_terminal F n K.obj,
    apply preserves_limit_of_iso_diagram F this,
  end }

def preserves_finite_products_of_preserves_binary_and_terminal (J : Type v) [fintype J] :
  preserves_limits_of_shape.{v} (discrete J) F :=
begin
  classical,
  refine trunc.rec_on_subsingleton (fintype.equiv_fin J) _,
  intro e,
  haveI := preserves_ulift_fin_of_preserves_binary_and_terminal F (fintype.card J),
  apply preserves_limit_of_equiv (discrete.equivalence (e.trans equiv.ulift.symm)).symm,
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