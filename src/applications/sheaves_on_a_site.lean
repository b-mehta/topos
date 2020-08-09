import applications.topologies
import topology.sheaves.presheaf_of_functions
import opens

/-!
The category `Sheaf` of (set-valued) sheaves on a site is defined, using the sheaf condition as
defined in `grothendieck.lean`. It's defined somewhat abstractly, but an equivalent condition
(`grothendieck.sheaf_condition'`) is given there too, which is more concrete.
-/
universes v u

noncomputable theory

namespace category_theory
namespace site_sheaf

open category limits

variables (C : Type u) [small_category C] (J : sieve_set C) [grothendieck J]

structure Sheaf :=
(P : Cᵒᵖ ⥤ Type u)
(sheaf_cond : grothendieck.sheaf_condition J P)

instance : category (Sheaf C J) := induced_category.category Sheaf.P

/--
The category of sheaves (in the Grothendieck sense) is equivalent to a special case of sheaves on
a local operator. We use this equivalence to transfer properties from the abstract topos theory
to the geometric case.
-/
def equiv_lt_sheaf : Sheaf C J ≌ sheaf (j J) :=
{ functor :=
  { obj := λ P, sheaf.mk P.P (equivalent_sheaf_conditions _ _ P.sheaf_cond),
    map := λ P Q f, f },
  inverse :=
  { obj := λ P, ⟨P.A, (equivalent_sheaf_conditions _ _).symm (get_condition P)⟩,
    map := λ P Q f, f },
  unit_iso := nat_iso.of_components (λ P, {hom := 𝟙 _, inv := 𝟙 _}) (by tidy),
  counit_iso := nat_iso.of_components (λ P, {hom := 𝟙 _, inv := 𝟙 _}) (by tidy) }

/-- The forgetful functor from sheaves to presheaves. -/
def forget_Sheaf : Sheaf C J ⥤ (Cᵒᵖ ⥤ Type u) := induced_functor _

instance : full (forget_Sheaf C J) := induced_category.full _
instance : faithful (forget_Sheaf C J) := induced_category.faithful _

/-- The sheafification functor for sheaves on a site. -/
def sheafify : (Cᵒᵖ ⥤ Type u) ⥤ Sheaf C J := sheafification (j J) ⋙ (equiv_lt_sheaf _ _).inverse

/-- The equivalence between Sheaf and sheaf commutes with their respective forgetful functors. -/
lemma forget_comm : forget_Sheaf C J = (equiv_lt_sheaf _ _).functor ⋙ sheaf.forget (j J) := rfl

/-- Sheafification is left adjoint to the inclusion into presheaves. -/
def Sheafy_adjoint : sheafify C J ⊣ forget_Sheaf C J :=
adjunction.comp _ _ (sheafification_is_adjoint (j J)) (equiv_lt_sheaf _ _).symm.to_adjunction

instance : is_right_adjoint (forget_Sheaf C J) :=
{ left := _, adj := Sheafy_adjoint C J }

/-- The category of sheaves is a reflective subcategory of presheaves -/
instance : reflective (forget_Sheaf C J) := {}.

/-- The forgetful functor creates limits. -/
instance : creates_limits (forget_Sheaf C J) :=
{ creates_limits_of_shape := λ D 𝒟,
  { creates_limit := λ K,
    begin
      change creates_limit _ ((equiv_lt_sheaf _ _).functor ⋙ sheaf.forget (j J)),
      apply_instance,
    end } }

/-- Sheafification preserves finite products -/
instance preserve_fin_prod (D : Type u) [decidable_eq D] [fintype D] : preserves_limits_of_shape (discrete D) (sheafify C J) :=
{ preserves_limit := λ K,
begin
  unfold sheafify,
  haveI := sheafification_preserves_finite_products (j J) D,
  apply_instance,
end }

/-- Sheafification preserves equalizers -/
instance preserve_equalizer : preserves_limits_of_shape walking_parallel_pair (sheafify C J) :=
{ preserves_limit := λ K,
begin
  unfold sheafify,
  haveI := sheafification_preserves_equalizers (j J),
  apply_instance,
end }

end site_sheaf

open topological_space topological_space.opens

/-- Sheaves on a space. -/
abbreviation Sh (X : Type u) [topological_space X] := site_sheaf.Sheaf (opens X) (covering X)

end category_theory