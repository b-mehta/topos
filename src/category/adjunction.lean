/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.equivalence
import category_theory.adjunction
import category_theory.yoneda
import category_theory.natural_isomorphism
import category_theory.fully_faithful
import category_theory.conj
import tactic

namespace category_theory
open category

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ -- declare the `v`'s first; see `category_theory.category` for an explanation

-- local attribute [elab_simple] whisker_left whisker_right

section one

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]


@[simps]
def op_equiv' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

@[simp]
lemma op_equiv'_apply (A : Cᵒᵖ) (B : C) (f : A ⟶ opposite.op B) : op_equiv' _ _ f = f.unop :=
rfl
@[simp]
lemma op_equiv'_symm_apply (A : Cᵒᵖ) (B : C) (f : B ⟶ A.unop) : (op_equiv' _ _).symm f = f.op :=
rfl

section two
variables {E : Type u₃} [category.{v₃} E]

def faithful_functor_right_cancel {F G : C ⥤ D} (H : D ⥤ E)
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) : F ≅ G :=
nat_iso.of_components
  (λ X, preimage_iso (comp_iso.app X))
  (λ X Y f, H.map_injective (by simpa using comp_iso.hom.naturality f))

end two

def left_adjoints_coyoneda_equiv {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G):
  F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
nat_iso.of_components
  (λ X, nat_iso.of_components
    (λ Y, ((adj1.hom_equiv X.unop Y).trans (adj2.hom_equiv X.unop Y).symm).to_iso)
    (by tidy))
  (by tidy)

def left_adjoint_uniq {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
nat_iso.unop
  (faithful_functor_right_cancel _
    (left_adjoints_coyoneda_equiv adj2 adj1))

def adjunction_op {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : G.op ⊣ F.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
    { to_fun := λ f, ((adj.hom_equiv _ _).inv_fun f.unop).op,
      inv_fun := λ g, ((adj.hom_equiv _ _).to_fun g.unop).op,
      left_inv := λ f, by simp,
      right_inv := λ f, by simp },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by simp [has_hom.hom.unop_inj.eq_iff],
  hom_equiv_naturality_right' := λ Y' Y X f g, by simp [has_hom.hom.unop_inj.eq_iff] }

def right_adjoint_uniq {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
nat_iso.unop (left_adjoint_uniq (adjunction_op adj2) (adjunction_op adj1))

variables {C' : Type u₃} [category.{v₃} C']
variables {D' : Type u₄} [category.{v₄} D']

@[simp]
lemma hom_congr_symm_apply {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X₁ ⟶ Y₁) :
  (α.hom_congr β).symm f = α.hom ≫ f ≫ β.inv :=
rfl

@[simp]
lemma hom_congr_apply {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) :
  (α.hom_congr β) f = α.inv ≫ f ≫ β.hom :=
rfl

def restrict_adjunction (iC : C ⥤ C') (iD : D ⥤ D') {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
  {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
  [full iC] [faithful iC] [full iD] [faithful iD] :
  L ⊣ R :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  calc (L.obj X ⟶ Y) ≃ (iD.obj (L.obj X) ⟶ iD.obj Y) : equiv_of_fully_faithful iD
       ... ≃ (L'.obj (iC.obj X) ⟶ iD.obj Y) : iso.hom_congr (comm1.symm.app X) (iso.refl _)
       ... ≃ (iC.obj X ⟶ R'.obj (iD.obj Y)) : adj.hom_equiv _ _
       ... ≃ (iC.obj X ⟶ iC.obj (R.obj Y)) : iso.hom_congr (iso.refl _) (comm2.app Y)
       ... ≃ (X ⟶ R.obj Y) : (equiv_of_fully_faithful iC).symm,
  hom_equiv_naturality_left_symm' := λ X' X Y f g,
  begin
    apply iD.map_injective,
    dsimp [equiv.trans, equiv.symm],
    simp only [functor.image_preimage, adjunction.hom_equiv_counit, assoc, id_comp, comp_id,
               functor.map_comp],
    erw [comm1.inv.naturality_assoc f],
    refl,
  end,
  hom_equiv_naturality_right' := λ X Y' Y f g,
  begin
    apply iC.map_injective,
    dsimp [equiv.trans],
    simp only [adjunction.hom_equiv_unit, functor.image_preimage, assoc, id_comp, comp_id,
               functor.map_comp],
    erw comm2.hom.naturality g,
    refl,
  end }

end one

end category_theory
