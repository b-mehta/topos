-- import category_theory.monad
-- import category_theory.limits.shapes.wide_pullbacks
-- import category_theory.comma
-- import over

-- universes v₁ v₂ v₃ u₁ u₂ u₃

-- namespace category_theory
-- open category limits comonad

-- @[simps]
-- def upgrade_functor {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] (F : C ⥤ D) (A : C) :
--   over A ⥤ over (F.obj A) :=
-- { obj := λ f, over.mk (F.map f.hom),
--   map := λ f g k, over.hom_mk (F.map k.left) (by simp [←F.map_comp, over.w]) }

-- section
-- parameters {E : Type u₁} [category.{v₁} E] {G : E ⥤ E} [comonad G] [has_finite_limits.{v₁} E]
-- parameter [Π (J : Type v₁) [decidable_eq J] [fintype J], preserves_limits_of_shape (wide_pullback_shape J) G]
-- variable (a : coalgebra G)

-- local attribute [instance] has_pullbacks_of_has_finite_limits

-- def G' : over a.A ⥤ over a.A := upgrade_functor G a.A ⋙ real_pullback a.a

-- def G'δ : G' a ⟶ G' a ⋙ G' a :=
-- { app := λ f,
--   begin
--     apply over.hom_mk,
--     dsimp [G'],
--     have := left_pb_to_both_pb,
--   end

-- }

-- instance : comonad (G' a) :=
-- { ε :=
--   { app := λ f, over.hom_mk (pullback.snd ≫ (ε_ G).app f.left)
--     (by { dsimp, erw [assoc, ← (ε_ G).naturality, ← pullback.condition_assoc, a.counit, comp_id], refl }),
--     naturality' := λ f g k,
--     begin
--       ext1,
--       dsimp [G'],
--       rw [pullback.lift_snd_assoc, assoc, assoc, (ε_ G).naturality], refl,
--     end },
--   δ := G'δ a,
-- }

-- def forward : coalgebra (G' a) ⥤ over a := sorry
-- def backward : over a ⥤ coalgebra (G' a) := sorry

-- end

-- end category_theory