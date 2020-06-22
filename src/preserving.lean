import preserve_binary_products
import category_theory.limits.limits
import category_theory.comma
import category_theory.limits.over
import category_theory.limits.shapes.constructions.equalizers
import pullbacks
import pempty

namespace category_theory

open category limits

universes v u v₂ u₂

variables {C : Type u} [category.{v} C] {D : Type u₂} [category.{v} D]
variables (T : C ⥤ D)

section pair_of_pb_term

variables [has_pullbacks.{v} C] [has_terminal.{v} C]

@[simps]
def pair_of_pullback_terminal (X Y : C) : cone (pair X Y) :=
{ X := pullback (default (X ⟶ ⊤_ C)) (default (Y ⟶ ⊤_ C)),
  π := { app := λ j, walking_pair.cases_on j pullback.fst pullback.snd } }

def pair_of_pullback_terminal_is_limit (X Y : C) : is_limit (pair_of_pullback_terminal X Y) :=
{ lift := λ s,
  begin
    apply pullback.lift _ _ _,
    apply s.π.app walking_pair.left,
    apply s.π.app walking_pair.right,
    apply subsingleton.elim,
  end,
  fac' := λ s j,
  begin
    cases j,
    apply pullback.lift_fst,
    apply pullback.lift_snd,
  end,
  uniq' := λ s m w,
  begin
    apply pullback.hom_ext,
    erw [w walking_pair.left, pullback.lift_fst],
    erw [w walking_pair.right, pullback.lift_snd],
  end }

variables [preserves_limits_of_shape walking_cospan T] [preserves_limits_of_shape pempty T]

def unique_to_functor_terminal {X : D} {f g : X ⟶ T.obj (⊤_ C)} : f = g :=
begin
  have : is_limit (T.map_cone _) := preserves_limit.preserves (limit.is_limit (functor.empty C)),
  apply this.hom_ext,
  simp,
end

def preserves_pair {X Y : C} : preserves_limit (pair X Y) T :=
begin
  apply preserves_limit_of_preserves_limit_cone (pair_of_pullback_terminal_is_limit X Y),
  have := preserves_pullback_cone T _ (default (X ⟶ ⊤_ C)) _ (default (Y ⟶ ⊤_ C)) pullback.condition (cone_is_pullback _ _),
  refine ⟨λ s, _, _, _⟩,
  apply (limits.pullback_cone.is_limit.lift' this (s.π.app walking_pair.left) (s.π.app walking_pair.right) _).1,
  apply unique_to_functor_terminal,
  rintros s ⟨_ | _⟩,
  apply (limits.pullback_cone.is_limit.lift' _ _ _ _).2.1,
  apply (limits.pullback_cone.is_limit.lift' _ _ _ _).2.2,
  intros s m w,
  refine pullback_cone.is_limit.hom_ext this _ _,
  rw (limits.pullback_cone.is_limit.lift' _ _ _ _).2.1,
  apply w walking_pair.left,
  rw (limits.pullback_cone.is_limit.lift' _ _ _ _).2.2,
  apply w walking_pair.right,
end

def preserves_binary_prods_of_preserves_pullbacks_and_terminal :
  preserves_limits_of_shape (discrete walking_pair) T :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (diagram_iso_pair K).symm,
    apply preserves_pair
  end }

end pair_of_pb_term

section equalizer_of_pb_prod

variables [has_pullbacks.{v} C] [has_binary_products.{v} C]
variables [preserves_limits_of_shape walking_cospan T] [preserves_limits_of_shape (discrete walking_pair) T]

open limits.walking_parallel_pair limits.walking_parallel_pair_hom
open limits.has_equalizers_of_pullbacks_and_binary_products

def prod_comparison (F : C ⥤ D) (A B : C) [has_limit (pair (F.obj A) (F.obj B))] : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
prod.lift (F.map limits.prod.fst) (F.map limits.prod.snd)

def preserves_parallel_pair {X Y : C} (f g : X ⟶ Y) : preserves_limit (parallel_pair f g) T :=
begin
  apply preserves_limit_of_preserves_limit_cone (equalizer_cone_is_limit (parallel_pair f g)),
  have l := preserves_pullback_cone T _ (prod.lift (𝟙 X) f) _ (prod.lift (𝟙 X) g) pullback.condition (cone_is_pullback _ _),
  have pl : has_limit (pair (T.obj X) (T.obj Y)),
    suffices : has_limit (pair X Y ⋙ T),
      resetI,
      apply has_limit_of_iso (diagram_iso_pair (pair X Y ⋙ T)),
    refine ⟨T.map_cone (limit.cone (pair X Y)), preserves_limit.preserves (limit.is_limit _)⟩,
  resetI,
  have p := limits.prod_comparison_iso_of_preserves_binary_prods' T X Y,
  refine ⟨λ s, _, _, _⟩,
  apply (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).1,
  have : s.π.app zero ≫ T.map f = s.π.app zero ≫ T.map g,
    erw s.w right, apply s.w left,
  rw [← cancel_mono (prod_comparison' T X Y), assoc, assoc, prod_comparison'],
  apply prod.hom_ext,
  simp only [prod.lift_fst, assoc, ← T.map_comp],
  simp only [prod.lift_snd, assoc, ← T.map_comp, this],
  intros s j,
  cases j,
  dsimp, rw comp_id,
  apply (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).2.1,
  conv_rhs {rw ← s.w left},
  dsimp,
  rw comp_id,
  simp_rw [T.map_comp],
  rw ← assoc,
  congr' 1,
  apply (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).2.1,
  intros s m w,
  apply pullback_cone.is_limit.hom_ext l,
  erw (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).2.1,
  rw ← w zero,
  congr' 1,
  dsimp, rw comp_id,
  refl,
  erw (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).2.2,
  rw ← w zero,
  congr' 1,
  dsimp,
  rw comp_id, rw pullback_fst_eq_pullback_snd, refl,
end

def preserves_equalizers_of_preserves_pullbacks_and_prods :
  preserves_limits_of_shape walking_parallel_pair T :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (diagram_iso_parallel_pair K).symm,
    apply preserves_parallel_pair
  end }

end equalizer_of_pb_prod

-- section factorisation

-- variable [has_finite_limits.{v} C]

-- @[simps]
-- def That : C ⥤ over (T.obj (⊤_ C)) :=
-- { obj := λ A, over.mk (T.map (default (A ⟶ _))),
--   map := λ A B f,
--   begin
--     refine over.hom_mk (T.map f) _,
--     dsimp,
--     rw ← T.map_comp,
--     congr' 1,
--     apply subsingleton.elim,
--   end }

-- def That_preserves_terminal : preserves_limits_of_shape pempty (That T) :=
-- { preserves_limit := λ K,
--   begin
--     apply preserves_limit_of_iso _ (K.unique_from_pempty _),
--     clear K,
--     apply preserves_limit_of_preserves_limit_cone (limit.is_limit (functor.empty C)),
--     have : default ((limit.cone (functor.empty C)).X ⟶ ⊤_ C) = 𝟙 _,
--       apply subsingleton.elim,
--     refine ⟨_, _, _⟩,
--     intro s,
--     refine over.hom_mk s.X.hom _,
--     dsimp,
--     rw [this, T.map_id, comp_id],
--     intro s,
--     simp,
--     intros s m w,
--     ext1,
--     dsimp,
--     rw ← over.w m,
--     dsimp,
--     conv_rhs {congr, skip, congr, apply_congr this},
--     simp,
--   end }

-- end factorisation


end category_theory