import category_theory.limits.shapes.terminal
import .kleisli

meta def tactic.interactive.case_bash : tactic unit := tactic.case_bash

namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

namespace monad

variables (T : C ⥤ C)

section
variables [monad.{v₁} T]
instance forget_right : is_right_adjoint (forget T) :=
{ left := free T
, adj := monad.adj T }

instance free_left : is_left_adjoint (free T) :=
{ right := forget T
, adj := monad.adj T }

theorem free_forget_id : free T ⋙ forget T = T := by { apply functor.ext; simp }

end

/-- The monad to which `adj` gives rise. Copy-pasted instance from mathlib,
except it's not an instance here because I wanna refer to it. -/
def monad_of_adj {D : Type u₂} [𝒟 : category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
: monad.{v₁} (F ⋙ G) :=
{ η := adj.unit
, μ := whisker_right (whisker_left F adj.counit) G
, assoc' := λ X, by { dsimp, erw [←G.map_comp, adj.counit.naturality, G.map_comp], refl }
, right_unit' := λ X, by { dsimp, rw [←G.map_comp], simp } }

variables [𝕋 : monad.{v₁} T]
include 𝕋

set_option pp.universes true

/- A packaged category + adjunction on it inducing the monad 𝕋 on 𝒞. -/
structure adj_inducing :=
-- TODO(WN): use `bundled`?
(D : Type u₂) (𝒟 : category.{v₂} D)
(F : C ⥤ D) (U : D ⥤ C)
(adj : F ⊣ U) (ftors_eq : F ⋙ U = T)
(monads_eq : monad_of_adj adj == 𝕋)

instance packaged_adj_cat (X: adj_inducing T) : category.{v₂} X.D := X.𝒟

/-- A morphism of adjunctions inducing 𝕋. -/
structure adj_mor (X Y : adj_inducing.{v₁ v₂ u₁ u₂} T) :=
(K : X.D ⥤ Y.D)
(left_comm' : X.F ⋙ K = Y.F)
(right_comm' : K ⋙ Y.U = X.U)

theorem adj_mor.ext {X Y : adj_inducing T} (f g : adj_mor T X Y)
(h : f.K = g.K) : f = g := begin
  cases f, cases g, congr, exact h
end

/-- Category Adj_T of adjunctions inducing the monad 𝕋 on 𝒞. -/
instance adj.category : category.{max v₂ u₂} (adj_inducing T) :=
{ hom := λ X Y, adj_mor.{v₁ v₂ u₁ u₂} T X Y
, id := λ X,
  { K := 𝟭 X.D
  , left_comm' := functor.comp_id X.F
  , right_comm' := functor.id_comp X.U }
, comp := λ X Y Z f g,
  { K := f.K ⋙ g.K
  , left_comm' := begin
      show (X.F ⋙ f.K) ⋙ g.K = Z.F,
      rw [f.left_comm'],
      exact g.left_comm'
    end
  , right_comm' := begin
      show f.K ⋙ (g.K ⋙ Z.U) = X.U,
      rw [g.right_comm'],
      exact f.right_comm'
    end }

, id_comp' := λ X Y f, begin
    apply adj_mor.ext,
    simp [functor.id_comp]
  end
, comp_id' := λ X Y f, begin
    apply adj_mor.ext,
    simp [functor.comp_id]
  end
, assoc' := λ X Y Z W f g h, by { simp, refl } }

/-- The Eilenberg-Moore adjunction is in Adj_T. -/
def eilenberg_moore : adj_inducing.{v₁ v₁ u₁ (max u₁ v₁)} T :=
{ D := algebra T
, 𝒟 := by apply_instance
, F := free T, U := forget T
, adj := adj T
, ftors_eq := @free_forget_id _ _ T 𝕋
, monads_eq := begin
    dunfold monad_of_adj adj adjunction.mk_of_hom_equiv,
    simp,
    cases h : 𝕋 with η μ,
    congr' 1,
    { exact @free_forget_id _ _ T 𝕋 },
    { cases η, congr' 1,
      { exact @free_forget_id _ _ T 𝕋 },
      { dsimp, simp } },
    { dunfold whisker_left whisker_right,
      cases μ, congr' 1,
      { exact @free_forget_id _ _ T 𝕋 },
      { ext X, dunfold free forget algebra, dsimp, exact category.id_comp _ _ } }
  end }

open kleisli.adjunction

/-- The Kleisli adjunction is also in Adj_T. -/
def kleisli : adj_inducing T :=
{ D := kleisli T
, 𝒟 := by apply_instance
, F := F_T T, U := U_T T
, adj := kleisli.adjunction.adj T
, ftors_eq := F_T_U_T_eq_T T
, monads_eq := begin
    dunfold monad_of_adj kleisli.adjunction.adj adjunction.mk_of_hom_equiv,
    simp,
    cases h : 𝕋 with η μ,
    congr' 1;
    rw ←h,
    { exact F_T_U_T_eq_T T },
    { cases η, congr' 1,
      { exact F_T_U_T_eq_T T },
      { ext X, dunfold category_struct.id F_T, rw h } },
    { dunfold whisker_left whisker_right,
      cases μ, congr' 1,
      { show (_ ⋙ _) ⋙ (F_T T ⋙ U_T T) = T ⋙ T,
        rw [F_T_U_T_eq_T T] },
      { rw [functor.comp_id, F_T_U_T_eq_T T] },
      { ext X, rw h, dunfold equiv.refl, simp,
        erw [functor.map_id, category.id_comp],
        refl } }
  end }

open limits

set_option pp.implicit false
set_option pp.universes true

/-- The category Cᵀ of Eilenberg-Moore algebras is terminal in Adj_T. -/
theorem adj_cat_has_terminal : has_terminal.{max u₁ v₁} (adj_inducing.{v₁ v₁ u₁ (max u₁ v₁)} T) :=
  @has_terminal_of_unique _ _
    (eilenberg_moore.{v₁ u₁} T)
    -- There is a morphism of adjunctions from any adjunction `padj` inducing 𝕋
    -- to the Eilenberg-Moore adjunction for 𝕋
    (λ padj, begin
      -- First rewrite all instances of T to F ⋙ U
      rcases h₁ : padj with ⟨D, 𝒟, F, U, adj, ftors_eq, monads_eq⟩,
      unfreezeI, cases ftors_eq,
      cases monads_eq,

      exact
      let Uε : _ := whisker_right adj.counit U in
      { default :=
        -- given by a functor K from the category D to the Eilenberg-Moore category Cᵀ
        { K :=
          -- which takes an object d ∈ D to an Eilenberg-Moore algebra (Ud, Uε_d)
          { obj := λ d,
            { A := U.obj d
            , a := Uε.app d
            , unit' := adjunction.right_triangle_components adj
            , assoc' := by { dsimp, rw [←functor.map_comp U, ←functor.map_comp U,
              adjunction.counit_naturality] } }
          -- and which takes a morphism f: d ⟶ d' ∈ D to Uf : Ud ⟶ Ud'
          , map := λ d₁ d₂ f,
            { f := U.map f
            , h' := by { dsimp, rw [←functor.map_comp U, ←functor.map_comp U,
              adjunction.counit_naturality] } }

          , map_id' := λ d, by { congr' 1, erw [U.map_id] }
          , map_comp' := λ d₁ d₂ d₃ f g, by simp [algebra.hom.comp] }

        , left_comm' := functor.ext
          (λ c, rfl)
          (λ c₁ c₂ f, by { dsimp, congr' 1, simp, refl })

        , right_comm' := functor.ext
          (λ d, rfl)
          (λ d₁ d₂ f, by { simp, refl }) }

      , uniq := λ K₂, begin
        show K₂ = { K := _, left_comm' := _, right_comm' := _ },
        rcases K₂ with ⟨K₂, hK₂_left_comm, hK₂_right_comm⟩,
        congr' 1,
        apply functor.ext,
        { intros d₁ d₂ f,

          sorry },
        { intro d,

          sorry}
      end }
    end)

end monad
end category_theory
