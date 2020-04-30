import category_theory.full_subcategory
import category_theory.limits.preserves

open category_theory category_theory.category category_theory.limits

universes v u u₂

variables {C : Type u}

variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒟
variables (F : C → D)

-- Should also work for fully faithful functors
instance forget_reflects_limits : reflects_limits (induced_functor F) :=
{ reflects_limits_of_shape := λ J 𝒥₁, by exactI
  { reflects_limit := λ K,
    { reflects := λ c t,
      { lift := λ s, t.lift ((induced_functor F).map_cone s),
        fac' := λ s, t.fac ((induced_functor F).map_cone s),
        uniq' := λ s, t.uniq ((induced_functor F).map_cone s) } } } }