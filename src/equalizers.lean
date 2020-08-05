import category_theory.limits.preserves
import category_theory.limits.shapes.equalizers

namespace category_theory

open category_theory category_theory.category category_theory.limits

universes v u u₂

variables (C : Type u) [category.{v} C]

def of_iso_point {J : Type v} [small_category J] (K : J ⥤ C) (c : cone K) [has_limit K] [i : is_iso (limit.lift K c)] : is_limit c :=
is_limit.of_iso_limit (limit.is_limit K)
begin
  haveI : is_iso (limit.cone_morphism c).hom := i,
  haveI : is_iso (limit.cone_morphism c) := cones.cone_iso_of_hom_iso _,
  symmetry,
  apply as_iso (limit.cone_morphism c),
end

section equalizers
variables {C} {D : Type u₂} [category.{v} D] (F : C ⥤ D) {B c : C} (f g : B ⟶ c) [has_equalizers.{v} C] [has_equalizers.{v} D]

def equalizing_map : F.obj (equalizer f g) ⟶ equalizer (F.map f) (F.map g) :=
equalizer.lift (F.map (equalizer.ι _ _)) (by simp only [← F.map_comp, equalizer.condition])

def equalizer_of_iso_point (h : is_iso (equalizing_map F f g)) : preserves_limit (parallel_pair f g) F :=
preserves_limit_of_preserves_limit_cone (limit.is_limit _)
begin
  apply of_iso_point _ _ _,
  apply_instance,
  let k : F.obj (equalizer f g) ⟶ limit _ := limit.lift (parallel_pair f g ⋙ F) (F.map_cone (limit.cone (parallel_pair f g))),
  change is_iso k,
  let k₂ : equalizer (F.map f) (F.map g) ⟶ limit (parallel_pair f g ⋙ F),
    apply limit.lift _ ⟨_, _, _⟩,
    rintro ⟨j⟩,
    apply equalizer.ι (F.map f) (F.map g),
    apply equalizer.ι _ _ ≫ F.map f,
    rintros X Y k,
    cases k,
    erw [id_comp], refl,
    erw [id_comp, equalizer.condition], refl,
    erw [functor.map_id, functor.map_id, id_comp, comp_id],
  have : is_iso k₂,
    refine ⟨_, _, _⟩,
    apply equalizer.lift _ _,
    apply limit.π _ walking_parallel_pair.zero,
    erw limit.w (parallel_pair f g ⋙ F) walking_parallel_pair_hom.left,
    erw limit.w (parallel_pair f g ⋙ F) walking_parallel_pair_hom.right,
    dsimp,
    apply equalizer.hom_ext,
    rw [assoc, equalizer.lift_ι, id_comp, limit.lift_π],
    dsimp,
    apply limit.hom_ext,
    rintro ⟨j⟩,
    erw [id_comp, assoc, limit.lift_π, equalizer.lift_ι],
    dsimp,
    rw [assoc, limit.lift_π],
    dsimp,
    rw [equalizer.lift_ι_assoc, id_comp],
    apply limit.w (parallel_pair f g ⋙ F) walking_parallel_pair_hom.left,
  have : k = equalizing_map F f g ≫ k₂,
    apply limit.hom_ext,
    rintro ⟨j⟩,
    erw [assoc, limit.lift_π, limit.lift_π],
    dsimp [functor.map_cone],
    erw [equalizer.lift_ι],
    rw [limit.lift_π, assoc, limit.lift_π],
    dsimp [functor.map_cone],
    erw [equalizer.lift_ι_assoc, ← F.map_comp, limit.w (parallel_pair f g) walking_parallel_pair_hom.left],
  rw this,
  resetI,
  apply_instance,
end

end equalizers

end category_theory