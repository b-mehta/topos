import category_theory.monad.algebra
import category_theory.limits.creates
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.equalizers
import category_theory.closed.cartesian
import category_theory.conj
-- import category_theory.comma
-- import category_theory.limits.over
-- import category_theory.limits.shapes.constructions.equalizers
import category_theory.limits.shapes.regular_mono

namespace category_theory

open category limits comonad

universes v u v₂ u₂

variables {C : Type u} [category.{v} C] [has_finite_limits.{v} C]

def equalizer_equiv {A B : C} (X : C) (f g : A ⟶ B) : (X ⟶ equalizer f g) ≃ {h : X ⟶ A // h ≫ f = h ≫ g} :=
{ to_fun := λ k, ⟨k ≫ equalizer.ι f g, by simp [equalizer.condition]⟩,
  inv_fun := λ k, equalizer.lift k.1 k.2,
  left_inv := λ k, by { ext, simp },
  right_inv := by { rintro ⟨k, hk⟩, simp [equalizer.lift_ι] } }

variables {G : C ⥤ C} [comonad.{v} G]
variables [cartesian_closed C]


instance forget_creates_limits (J : Type v) [small_category J] [preserves_limits_of_shape J G] :
  creates_limits_of_shape J (forget G) :=
sorry

def forget_creates_limits_of_comonad_preserves (J : Type v) [small_category J]
  [preserves_limits_of_shape J G] (D : J ⥤ coalgebra G) [has_limit (D ⋙ forget G)] :
has_limit D :=
has_limit_of_created D (forget G)

def kleisli_exp_obj (A : C) (b : coalgebra G) : coalgebra G :=
(cofree G).obj (A ^^ b.A)

variables [preserves_limits_of_shape (discrete walking_pair) G]
variables [preserves_limits_of_shape walking_parallel_pair G]

instance : has_binary_products (coalgebra G) :=
{ has_limits_of_shape :=
  { has_limit := λ D, forget_creates_limits_of_comonad_preserves _ _ } }
instance : has_equalizers (coalgebra G) :=
{ has_limits_of_shape :=
  { has_limit := λ D, forget_creates_limits_of_comonad_preserves _ _ } }

def kleisli_exp_hom
  {A A' : C} (f : (cofree G).obj A ⟶ (cofree G).obj A') (b : coalgebra G)  :
  kleisli_exp_obj A b ⟶ kleisli_exp_obj A' b :=
begin
  apply (adj G).hom_equiv _ _ _,
  apply exp_comparison G _ _ ≫ pre _ b.a ≫ (exp b.A).map _,
  apply ((adj G).hom_equiv _ _).symm f,
end

def prod_iso (b c : coalgebra G) : (b ⨯ c).A ≅ b.A ⨯ c.A := sorry

def is_exp (A : C) (b c : coalgebra G) :
  (c ⟶ kleisli_exp_obj A b) ≃ (b ⨯ c ⟶ (cofree G).obj A) :=
calc (c ⟶ kleisli_exp_obj A b) ≃ (c.A ⟶ A ^^ b.A) : ((adj G).hom_equiv _ _).symm
     ... ≃ (b.A ⨯ c.A ⟶ A) : ((exp.adjunction _).hom_equiv _ _).symm
     ... ≃ ((b ⨯ c).A ⟶ A) : iso.hom_congr (prod_iso _ _).symm (iso.refl _)
     ... ≃ (b ⨯ c ⟶ (cofree G).obj A) : (adj G).hom_equiv _ _

def top_map (a : coalgebra G) : (cofree G).obj a.A ⟶ (cofree G).obj (G.obj a.A) :=
{ f := (δ_ G).app a.A,
  h' := comonad.coassoc _ }

def bot_map (a : coalgebra G) : (cofree G).obj a.A ⟶ (cofree G).obj (G.obj a.A) :=
{ f := G.map a.a,
  h' := ((δ_ G).naturality a.a).symm }

def exp_obj [has_equalizers (coalgebra G)] [preserves_limits_of_shape (discrete walking_pair) G]
  (a b : coalgebra G) :=
equalizer (kleisli_exp_hom (top_map a) b) (kleisli_exp_hom (bot_map a) b)

-- variable (a : coalgebra G)

-- section

-- @[simps]
-- def raise_to_hom : a ⟶ (cofree G).obj a.A :=
-- { f := a.a,
--   h' := a.coassoc.symm }

-- instance : regular_mono (raise_to_hom a) :=
-- { Z := (cofree G).obj (G.obj a.A),
--   left :=
--   { f := (δ_ G).app a.A,
--     h' := comonad.coassoc a.A },
--   right :=
--   { f := G.map a.a,
--     h' := ((δ_ G).naturality a.a).symm },
--   w := coalgebra.hom.ext _ _ (coalgebra.coassoc a),
--   is_limit :=
--   begin
--   end
-- }

-- end

end category_theory