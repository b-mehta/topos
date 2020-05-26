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

namespace category_theory
open category

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

-- local attribute [elab_simple] whisker_left whisker_right

section

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞

@[simps]
def op_equiv (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

@[simps]
def op_equiv' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

include 𝒟

-- Some basic adjunction properties
@[reducible]
def equiv_homset_left_of_nat_iso
  {F G : C ⥤ D} (iso : F ≅ G) {X : C} {Y : D} :
  (F.obj X ⟶ Y) ≃ (G.obj X ⟶ Y) :=
{ to_fun := λ f, (iso.app _).inv ≫ f,
  inv_fun := λ g, (iso.app _).hom ≫ g,
  left_inv := λ f, begin dsimp, rw ← assoc, simp end,
  right_inv := λ g, begin dsimp, rw ← assoc, simp end }

@[reducible]
def equiv_homset_right_of_nat_iso
  {G H : D ⥤ C} (iso : G ≅ H) {X : C} {Y : D} :
  (X ⟶ G.obj Y) ≃ (X ⟶ H.obj Y) :=
⟨λ f, f ≫ (iso.app _).hom, λ g, g ≫ (iso.app _).inv, λ f, by simp, λ g, by simp⟩

def adjunction_of_nat_iso_left
  {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) :
  G ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, (equiv_homset_left_of_nat_iso iso.symm).trans (adj.hom_equiv X Y) }

def adjunction_of_nat_iso_right
  {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) :
  F ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, (adj.hom_equiv X Y).trans (equiv_homset_right_of_nat_iso iso) }

def right_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_right_adjoint F] : is_right_adjoint G :=
{ left := r.left,
  adj := adjunction_of_nat_iso_right r.adj h }

def right_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E} [Fr : is_right_adjoint F] [Gr : is_right_adjoint G] :
  is_right_adjoint (F ⋙ G) :=
{ left := Gr.left ⋙ Fr.left,
  adj := adjunction.comp _ _ Gr.adj Fr.adj }

def left_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_left_adjoint F] : is_left_adjoint G :=
{ right := r.right,
  adj := adjunction_of_nat_iso_left r.adj h }

def left_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) [Fr : is_left_adjoint F] [Gr : is_left_adjoint G] :
  is_left_adjoint (F ⋙ G) :=
{ right := Gr.right ⋙ Fr.right,
  adj := adjunction.comp _ _ Fr.adj Gr.adj }

def left_adjoint_of_equiv {F : C ⥤ D} [is_equivalence F] : is_left_adjoint F :=
{ right := _,
  adj := functor.adjunction F }

def right_adjoint_of_equiv {F : C ⥤ D} [is_equivalence F] : is_right_adjoint F :=
{ left := _,
  adj := functor.adjunction F.inv }

def adjoint_op {F : C ⥤ D} {G : Dᵒᵖ ⥤ Cᵒᵖ} (h : G ⊣ F.op) : F ⊣ G.unop :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, (equiv.trans (h.hom_equiv (opposite.op Y) (opposite.op X)) (op_equiv _ _)).symm.trans (op_equiv' _ _),
  hom_equiv_naturality_left_symm' := λ X X' Y f g,
  begin
    dsimp [equiv.symm, op_equiv],
    apply has_hom.hom.op_inj,
    simp,
  end,
  hom_equiv_naturality_right' := λ X Y Y' f g,
  begin
    dsimp [equiv.symm, op_equiv'],
    apply has_hom.hom.op_inj,
    simp,
  end }

def left_adjoint_of_right_adjoint_op {F : C ⥤ D} [h : is_right_adjoint F.op] : is_left_adjoint F :=
{ right := (left_adjoint F.op).unop,
  adj := adjoint_op h.adj }

end

section

variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
          {E : Type u₃} [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

def faithful_functor_right_cancel {F G : C ⥤ D} {H : D ⥤ E}
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) : F ≅ G :=
begin
  refine nat_iso.of_components (λ X, preimage_iso (comp_iso.app X)) (λ X Y f, _),
  apply functor.injectivity H,
  simp only [preimage_iso_hom, H.map_comp, H.image_preimage],
  exact comp_iso.hom.naturality f,
end

end

section

variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

def left_adjoints_coyoneda_equiv {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G):
  F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
begin
  refine nat_iso.of_components _ _,
  { intro X,
    refine nat_iso.of_components _ _,
    { intro Y,
      exact ((adj1.hom_equiv X.unop Y).trans (adj2.hom_equiv X.unop Y).symm).to_iso },
    tidy },
  tidy
end

def left_adjoint_uniq {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  nat_iso.unop
    (faithful_functor_right_cancel
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

end

end category_theory
