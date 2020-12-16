import locally_cartesian_closed

namespace category_theory
open category limits

noncomputable theory

universes v u
variables {C : Type u} [category.{v} C]
variables {J : Type v} [small_category J]

variables {K₁ K₂ : J ⥤ C}
variables (c₁ : cocone K₁) {c₂ : cocone K₂} (t₂ : is_colimit c₂)
variables (τ : K₁ ⟶ K₂) (f : c₁.X ⟶ c₂.X)

variables (all_comm : ∀ (j : J), τ.app j ≫ c₂.ι.app j = c₁.ι.app j ≫ f)
variables (all_pb : Π (j : J), is_limit (pullback_cone.mk _ _ (all_comm j)))

variables [has_finite_limits C] [is_locally_cartesian_closed C] [has_colimits_of_shape J C]

include t₂ all_comm all_pb

def iso_diagrams : K₁ ≅ pullback_diagram f K₂ c₂ (𝟙 c₂.X) :=
begin
  apply nat_iso.of_components (λ j, _) _,
  { refine is_limit.cone_points_iso_of_nat_iso (all_pb j) (cone_is_pullback _ _) _,
    { apply nat_iso.of_components _ _,
    { intro j, refl },
    { rintros X Y ⟨f⟩,
      dsimp, simp,
      cases f_1_1,
      dsimp, simp,
      dsimp, simp } } },
  { intros X Y g,
    dsimp only [pullback_diagram_map, is_limit.cone_points_iso_of_nat_iso],
    ext1,
    { rw [assoc, assoc, pullback.lift_fst],
      change _ ≫ _ ≫ (pullback_cone.mk _ _ _).fst = _ ≫ (pullback_cone.mk _ _ _).fst ≫ _,
      rw is_limit.map_π,
      rw is_limit.map_π_assoc,
      dsimp,
      rw [comp_id, τ.naturality, id_comp] },
    { rw [assoc, assoc, pullback.lift_snd],
      change _ ≫ _ ≫ (pullback_cone.mk _ _ _).snd = _ ≫ (pullback_cone.mk _ _ _).snd,
      rw is_limit.map_π,
      rw is_limit.map_π,
      dsimp,
      rw [comp_id, comp_id],
      rw c₁.w,
      } }
end

def pullback_colimit : is_colimit c₁ :=
begin
  apply is_colimit.of_iso_colimit ((is_colimit.precompose_hom_equiv (iso_diagrams c₁ t₂ τ f all_comm all_pb) _).inv_fun (pullback_preserves f c₂ t₂ (𝟙 _))),
  apply cocones.ext _ _,
  { refine {iso . hom := pullback.snd, inv := pullback.lift f (𝟙 _) (by simp), hom_inv_id' := _},
    change _ = 𝟙 _,
    apply pullback.hom_ext,
    rw [assoc, pullback.lift_fst, ← pullback.condition, comp_id, id_comp],
    rw [assoc, pullback.lift_snd, comp_id, id_comp] },
  { intro j,
    dsimp [iso_diagrams],
    rw [assoc],
    rw pullback.lift_snd,
    change _ ≫ (pullback_cone.mk _ _ _).snd = _,
    rw is_limit.map_π,
    dsimp,
    apply comp_id }
end

end category_theory