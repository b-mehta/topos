import category_theory.monad.algebra
import category_theory.limits.creates
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.equalizers
-- import category_theory.comma
-- import category_theory.limits.over
-- import category_theory.limits.shapes.constructions.equalizers
import category_theory.limits.shapes.regular_mono

namespace category_theory

open category limits comonad

universes v u v₂ u₂

variables {C : Type u} [category.{v} C] [has_finite_limits.{v} C]
variables {G : C ⥤ C} [comonad.{v} G]

variable (a : coalgebra G)

section

@[simps]
def raise_to_hom : a ⟶ (cofree G).obj a.A :=
{ f := a.a,
  h' := a.coassoc.symm }

instance : regular_mono (raise_to_hom a) :=
{ Z := (cofree G).obj (G.obj a.A),
  left :=
  { f := (δ_ G).app a.A,
    h' := comonad.coassoc a.A },
  right :=
  { f := G.map a.a,
    h' := ((δ_ G).naturality a.a).symm },
  w := coalgebra.hom.ext _ _ (coalgebra.coassoc a),
  is_limit :=
  begin
  end
}

end

end category_theory