import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import cartesian_closed
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

section
local attribute [tidy] tactic.case_bash

@[reducible]
def star : C ⥤ over B :=
{ obj := λ A, @over.mk _ _ _ (limits.prod A B) limits.prod.snd,
  map := λ X Y f, begin apply over.hom_mk _ _, apply limits.prod.map f (𝟙 _), simp end}

end

def forget_adj_star : over.forget ⊣ star B :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g A, { to_fun := λ f, begin apply over.hom_mk _ _, apply prod.lift f g.hom, simp end,
                        inv_fun := λ k, k.left ≫ limits.prod.fst,
                        left_inv := λ f, begin dsimp, simp end,
                        right_inv := λ k, begin apply over.over_morphism.ext, dsimp, apply prod.hom_ext, simp, simp, rw ← over.w k, refl end},
  hom_equiv_naturality_left_symm' := λ X X' Y f g, begin dsimp, simp end,
  hom_equiv_naturality_right' := λ X Y Y' f g, begin simp, apply over.over_morphism.ext, simp, dsimp, apply prod.hom_ext, simp, simp, dsimp, simp end}
end category_theory
