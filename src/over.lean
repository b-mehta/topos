import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import cartesian_closed
import pullbacks
import comma

/-!
# Properties of the over category.

We can interpret the forgetful functor `forget : over B ⥤ C` as dependent sum,
(written `Σ_B`)
and when C has binary products, it has a right adjoint `B*` given by
`A ↦ (π₂ : A × B → B)`, denoted `star` in Lean.

TODO: prove everything below this line.
Furthermore, if the original category C has pullbacks and terminal object (i.e.
all finite limits), `B*` has a right adjoint iff `B` is exponentiable in `C`.
This right adjoint is written `Π_B` and is interpreted as dependent product.

Under the same conditions, if `A` is exponentiable in `C`, then `B* A` is
exponentiable in `C/B` for any `B`, and `B*` preserves exponentials.

We say `C` is locally cartesian closed if it has all finite limits, and each
`C/B` is cartesian closed.

Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`, and so `f* : C/B ⥤ (C/B)/f` is 'the same thing' as pulling back
morphisms along `f`. In particular, `C` is locally cartesian closed iff
it has finite limits and `f* : C/B ⥤ C/A` has a right adjoint (for each
`f : A ⟶ B`).

From here, we can show that if `C` is locally cartesian closed and has
reflexive coequalizers, then every morphism factors into a regular epic
and monic.
-/
namespace category_theory
open category limits

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variable (B : C)
variable [has_binary_products.{v} C]

section -- this section is just to add this attribute
local attribute [tidy] tactic.case_bash

@[reducible]
def star : C ⥤ over B :=
{ obj := λ A, @over.mk _ _ _ (B ⨯ A) limits.prod.fst,
  map := λ X Y f, begin apply over.hom_mk _ _, apply limits.prod.map (𝟙 _) f, simp end}

def forget_adj_star : over.forget ⊣ star B :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g A,
  { to_fun := λ f, over.hom_mk (prod.lift g.hom f),
    inv_fun := λ k, k.left ≫ limits.prod.snd,
    left_inv := by tidy,
    right_inv := by tidy } }
end

variables [has_terminal.{v} C] [has_pullbacks.{v} C]

def Pi_obj [exponentiable B] (f : over B) : C := pullback (exp_lift B f.hom) (point_at_hom (𝟙 B))

private def pi_obj.equiv [exponentiable B] (X : C) (Y : over B) : ((star B).obj X ⟶ Y) ≃ (X ⟶ Pi_obj B Y) :=
{ to_fun := λ f, pullback.lift (exp_transpose.to_fun f.left) (terminal.from _)
                    (begin rw ← exp_transpose_natural_right, erw ← exp_transpose_natural_left, tidy end),
  inv_fun := λ g, begin
                    apply over.hom_mk _ _, apply (exp_transpose.inv_fun (g ≫ pullback.fst)),
                    dsimp, apply function.injective_of_left_inverse exp_transpose.left_inv,
                    rw exp_transpose_natural_right, rw exp_transpose.right_inv, rw assoc,
                    rw pullback.condition, have : g ≫ pullback.snd = terminal.from X,
                    apply subsingleton.elim, rw ← assoc, rw this, erw ← exp_transpose_natural_left,
                    apply function.injective_of_left_inverse exp_transpose.right_inv,
                    rw exp_transpose.left_inv, rw exp_transpose.left_inv, simp
                  end,
  left_inv := λ f, begin apply over.over_morphism.ext, simp, rw exp_transpose.left_inv end,
  right_inv := λ g, begin simp, apply pullback.hom_ext, simp, rw exp_transpose.right_inv, apply subsingleton.elim end
  }

private lemma pi_obj.natural_equiv [exponentiable B] (X' X : C) (Y : over B) (f : X' ⟶ X) (g : (star B).obj X ⟶ Y) :
  (pi_obj.equiv B X' Y).to_fun ((star B).map f ≫ g) = f ≫ (pi_obj.equiv B X Y).to_fun g :=
begin
  apply pullback.hom_ext, simp [pi_obj.equiv], rw ← exp_transpose_natural_left, refl,
  apply subsingleton.elim
end

def Pi_functor [exponentiable B] : over B ⥤ C := @adjunction.right_adjoint_of_equiv _ _ _ _ (star B) (Pi_obj B) (pi_obj.equiv B) (pi_obj.natural_equiv B)
def star_adj_pi_of_exponentiable [exponentiable B] : star B ⊣ Pi_functor B := adjunction.adjunction_of_equiv_right _ _
def star_is_left_adj_of_exponentiable [exponentiable B] : is_left_adjoint (star B) := ⟨Pi_functor B, star_adj_pi_of_exponentiable B⟩

def exponentiable_of_star_is_left_adj (h : is_left_adjoint (star B)) : exponentiable B :=
⟨⟨star B ⋙ h.right, adjunction.comp _ _ h.adj (forget_adj_star B)⟩⟩

end category_theory