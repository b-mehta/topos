import category_theory.limits.limits
import category_theory.limits.shapes
import category_theory.types
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers

universes v u

open category_theory category_theory.category category_theory.limits

-- finite products from binary products and initial object

-- @[priority 100] -- see Note [lower instance priority]
-- def has_finite_products_of_has_binary_products_and_terminal (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_binary_products.{v} C] : 
--   has_finite_products.{v} C :=
-- {has_limits_of_shape := λ J _ _, 
--   {has_limit := λ F, 
--     {cone := _, is_limit := _}}}

-- example (C : Type u) [𝒞 : category.{v} C] [has_pullbacks.{v} C] (X Y Z : C)
--   (F : discrete walking_pair ⥤ C) (s : cone F) (f : X ⟶ Z) (g : Y ⟶ Z)
--   (m : s.X ⟶ pullback f g) : 
--   m = pullback.lift (m ≫ pullback.fst) (m ≫ pullback.snd) _ :=
-- begin
  
-- end
-- 1 goal
-- C : Type u,
-- 𝒞 : category C,
-- _inst_1 : has_terminal C,
-- _inst_2 : has_pullbacks C,
-- F : discrete walking_pair ⥤ C,
-- s : cone F,
-- m : s.X ⟶ pullback (terminal.from (F.obj walking_pair.left)) (terminal.from (F.obj walking_pair.right)),
-- j : ∀ (j : discrete walking_pair), m ≫ walking_pair.rec pullback.fst pullback.snd j = (s.π).app j
-- ⊢ m = pullback.lift (m ≫ pullback.fst) (m ≫ pullback.snd) _

example (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_pullbacks.{v} C] : 
  has_binary_products.{v} C :=
{has_limits_of_shape := 
  {has_limit := λ F, 
    {cone := 
      {X := pullback (terminal.from (F.obj walking_pair.left)) 
                     (terminal.from (F.obj walking_pair.right)), 
       π := nat_trans.of_homs (λ x, begin cases x, apply pullback.fst, apply pullback.snd end)}, 
     is_limit := 
       {lift := begin 
                  intro c, apply pullback.lift _ _ _,
                  exact c.π.app walking_pair.left, exact c.π.app walking_pair.right, 
                  apply subsingleton.elim
                end,
        fac' := begin
                  intros s c, cases c, apply limit.lift_π, apply limit.lift_π,
                end,
        uniq' := begin
        rw nat_trans.of_homs, dsimp, intros s m j, rw ← j, rw ← j, dsimp, 
        -- have := @is_limit.uniq_cone_morphism _ _ _ _ F s, 
        end
                }
     }}}

end category_theory.limits