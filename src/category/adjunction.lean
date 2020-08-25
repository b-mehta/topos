/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.equivalence
import category_theory.adjunction.opposites
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

def left_adjoint_of_right_adjoint_op {F : C ⥤ D} [h : is_right_adjoint F.op] : is_left_adjoint F :=
{ right := (left_adjoint F.op).unop,
  adj := adjunction.adjoint_unop_of_adjoint_op _ _ (adjunction.of_right_adjoint _) }

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
nat_iso.unop (fully_faithful_cancel_right _ (left_adjoints_coyoneda_equiv adj2 adj1))

-- def adjunction_op {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : G.op ⊣ F.op :=
-- adjunction.mk_of_hom_equiv
-- { hom_equiv := λ X Y,
--     { to_fun := λ f, ((adj.hom_equiv _ _).inv_fun f.unop).op,
--       inv_fun := λ g, ((adj.hom_equiv _ _).to_fun g.unop).op,
--       left_inv := λ f, by simp,
--       right_inv := λ f, by simp },
--   hom_equiv_naturality_left_symm' := λ X' X Y f g, by simp [has_hom.hom.unop_inj.eq_iff],
--   hom_equiv_naturality_right' := λ Y' Y X f g, by simp [has_hom.hom.unop_inj.eq_iff] }

def right_adjoint_uniq {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
nat_iso.unop
  (left_adjoint_uniq
    (adjunction.op_adjoint_op_of_adjoint _ F adj2)
    (adjunction.op_adjoint_op_of_adjoint _ _ adj1))

end one

end category_theory
