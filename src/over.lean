import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.epi_mono
import category_theory.limits.over
import cartesian_closed

/-!
# Properties of the over category.

We can interpret the forgetful functor `forget : over B ⥤ C` as dependent sum,
(written `Σ_B`)
and when C has binary products, it has a right adjoint `B*` given by
`A ↦ (π₁ : B × A → B)`, denoted `star` in Lean.

Furthermore, if the original category C has pullbacks and terminal object (i.e.
all finite limits), `B*` has a right adjoint iff `B` is exponentiable in `C`.
This right adjoint is written `Π_B` and is interpreted as dependent product.

Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`.
-/
namespace category_theory
open category limits

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section adjunction

variable (B : C)

section

variable [has_pullbacks.{v} C]

@[simps]
def real_pullback {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ A),
  map := λ g h k, over.hom_mk (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition])) (by tidy) }

end

section
variable [has_binary_products.{v} C]

@[simps]
def star : C ⥤ over B :=
{ obj := λ A, @over.mk _ _ _ (B ⨯ A) limits.prod.fst,
  map := λ X Y f, over.hom_mk (limits.prod.map (𝟙 _) f) }

local attribute [tidy] tactic.case_bash

def forget_adj_star : over.forget ⊣ star B :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g A,
  { to_fun := λ f, over.hom_mk (prod.lift g.hom f),
    inv_fun := λ k, k.left ≫ limits.prod.snd,
    left_inv := by tidy,
    right_inv := by tidy } }
end

variables [has_finite_limits.{v} C]

def Pi_obj [exponentiable B] (f : over B) : C := pullback (post B f.hom) (point_at_hom (𝟙 B))

@[simps]
private def pi_obj.equiv [exponentiable B] (X : C) (Y : over B) :
  ((star B).obj X ⟶ Y) ≃ (X ⟶ Pi_obj B Y) :=
{ to_fun := λ f, pullback.lift (cart_closed.curry f.left) (terminal.from _)
    (by { rw [point_at_hom, comp_id, ← curry_natural_left, ← curry_natural_right,
              limits.prod.map_fst, comp_id, over.w f], refl }),
  inv_fun := λ g,
    begin
      apply over.hom_mk _ _,
      { apply (cart_closed.uncurry (g ≫ pullback.fst)) },
      { dsimp,
        rw [← uncurry_natural_right, assoc, pullback.condition, ← assoc, ← curry_natural_left,
            uncurry_curry, comp_id, limits.prod.map_fst, comp_id] }
    end,
  left_inv := λ f, by { ext1, simp },
  right_inv := λ g,
  by { ext1, { simp }, { apply subsingleton.elim } } }

private lemma pi_obj.natural_equiv [exponentiable B] (X' X : C) (Y : over B) (f : X' ⟶ X) (g : (star B).obj X ⟶ Y) :
  (pi_obj.equiv B X' Y).to_fun ((star B).map f ≫ g) = f ≫ (pi_obj.equiv B X Y).to_fun g :=
begin
  apply pullback.hom_ext,
  { simp [curry_natural_left] },
  { apply subsingleton.elim }
end

def Pi_functor [exponentiable B] : over B ⥤ C :=
  adjunction.right_adjoint_of_equiv (pi_obj.equiv B) (pi_obj.natural_equiv B)
def star_adj_pi_of_exponentiable [exponentiable B] : star B ⊣ Pi_functor B :=
  adjunction.adjunction_of_equiv_right _ _
instance star_is_left_adj_of_exponentiable [exponentiable B] : is_left_adjoint (star B) :=
  ⟨Pi_functor B, star_adj_pi_of_exponentiable B⟩

def exponentiable_of_star_is_left_adj (h : is_left_adjoint (star B)) : exponentiable B :=
⟨⟨star B ⋙ h.right, adjunction.comp _ _ h.adj (forget_adj_star B)⟩⟩

end adjunction

end category_theory
