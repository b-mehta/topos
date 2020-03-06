import category_theory.limits.shapes

open category_theory category_theory.category category_theory.limits

universes u v
variables {C : Type u} [𝒞 : category.{v} C]
variables {J : Type v} [small_category J]
include 𝒞

@[simp] lemma limit.lift_self_id (F : J ⥤ C) [has_limit F] :
  limit.lift F (limit.cone F) = 𝟙 (limit F) :=
begin
  symmetry, refine is_limit.uniq _ _ _ _,
  intro j, erw [id_comp _ (limit.π F j)], refl,
end