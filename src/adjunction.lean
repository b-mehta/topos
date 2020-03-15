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

local attribute [elab_simple] whisker_left whisker_right

section

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

-- Some basic adjunction properties
@[reducible]
def equiv_homset_left_of_nat_iso {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F G : C ⥤ D} (iso : F ≅ G) {X : C} {Y : D} :
  (F.obj X ⟶ Y) ≃ (G.obj X ⟶ Y) :=
⟨λ f, (iso.app _).inv ≫ f, λ g, (iso.app _).hom ≫ g, λ f, begin dsimp, rw ← assoc, simp end, λ g, begin dsimp, rw ← assoc, simp end⟩

@[reducible]
def equiv_homset_right_of_nat_iso {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {G H : D ⥤ C} (iso : G ≅ H) {X : C} {Y : D} :
  (X ⟶ G.obj Y) ≃ (X ⟶ H.obj Y) :=
⟨λ f, f ≫ (iso.app _).hom, λ g, g ≫ (iso.app _).inv, λ f, by simp, λ g, by simp⟩

def adjunction_of_nat_iso_left {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) :
  G ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.trans (equiv_homset_left_of_nat_iso iso.symm) (adj.hom_equiv X Y),
  hom_equiv_naturality_left_symm' := begin intros, simp, rw ← assoc, rw ← assoc, rw ← assoc, rw ← assoc, congr' 2, simp end,
  hom_equiv_naturality_right' := λ X Y Y' f g, by simp}

def adjunction_of_nat_iso_right {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
  {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) :
  F ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.trans (adj.hom_equiv X Y) (equiv_homset_right_of_nat_iso iso),
  hom_equiv_naturality_left_symm' := λ X X' Y f g, by simp,
  hom_equiv_naturality_right' := λ X Y Y' f g, begin simp, congr' 1, rw ← assoc, rw ← assoc, congr' 1, rw [nat_trans.naturality] end}

end

section

variables {C : Type u₁} [𝒞 : category.{v₁} C]
          {D : Type u₂} [𝒟 : category.{v₂} D]
          {E : Type u₃} [ℰ : category.{v₃} E]
include 𝒞 𝒟 ℰ

def faithful_functor_right_cancel {F G : C ⥤ D} {H : D ⥤ E}
  [full H] [faithful H] (comp_iso: F ⋙ H ≅ G ⋙ H) : F ≅ G :=
begin
  refine nat_iso.of_components (λX, preimage_iso (comp_iso.app X)) _,
  intros X Y f,
  apply functor.injectivity H,
  simp only [preimage_iso_hom, iso.app, functor.image_preimage, functor.map_comp],
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
      exact equiv.to_iso ((adj1.hom_equiv X.unop Y).trans ((adj2.hom_equiv X.unop Y).symm)) },
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
    { to_fun := λ f, ((adj.hom_equiv (Y.unop) (X.unop)).inv_fun f.unop).op,
      inv_fun := λ g, ((adj.hom_equiv (Y.unop) (X.unop)).to_fun g.unop).op,
      left_inv := λ f, by { dsimp, rw (adj.hom_equiv _ _).right_inv, refl },
      right_inv := λ f, by { dsimp, rw (adj.hom_equiv _ _).left_inv, refl } },
  hom_equiv_naturality_left_symm' := λ X' X Y f g,
  begin
    dsimp,
    apply has_hom.hom.unop_inj,
    rw [unop_comp, has_hom.hom.unop_op],
    apply adj.hom_equiv_naturality_right
  end,
  hom_equiv_naturality_right' := λ Y' Y X f g,
  begin
    dsimp,
    apply has_hom.hom.unop_inj,
    rw [unop_comp, has_hom.hom.unop_op],
    apply adj.hom_equiv_naturality_left_symm
  end
}

def right_adjoint_uniq {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
nat_iso.unop (left_adjoint_uniq (adjunction_op adj2) (adjunction_op adj1))

end

end category_theory