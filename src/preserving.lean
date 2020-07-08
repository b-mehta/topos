import preserve_binary_products
import category_theory.limits.limits
import category_theory.comma
import category_theory.limits.over
import category_theory.limits.shapes.constructions.equalizers
import pullbacks

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

variables [preserves_limits_of_shape walking_cospan T] [preserves_limits_of_shape (discrete pempty) T]

def unique_to_functor_terminal {X : D} {f g : X ⟶ T.obj (⊤_ C)} : f = g :=
begin
  have : is_limit (T.map_cone _) := preserves_limit.preserves (limit.is_limit (functor.empty C)),
  apply this.hom_ext,
  rintro ⟨⟩,
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
  erw (limits.pullback_cone.is_limit.lift' l (s.π.app zero) (s.π.app zero) _).2.2,
  rw ← w zero,
  congr' 1,
  dsimp,
  rw comp_id, rw pullback_fst_eq_pullback_snd,
end

def preserves_equalizers_of_preserves_pullbacks_and_prods :
  preserves_limits_of_shape walking_parallel_pair T :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (diagram_iso_parallel_pair K).symm,
    apply preserves_parallel_pair
  end }

end equalizer_of_pb_prod

section lim_of_prod_equalizer

variables {J : Type v} [small_category J]
variables (F : J ⥤ C)

-- variables {c₁ : cone (discrete.functor F.obj)}
-- variables {c₂ : cone (discrete.functor (λ f, F.obj f.1.2) : discrete (Σ (p : J × J), p.fst ⟶ p.snd) ⥤ C)}
-- variables (t₁ : is_limit c₁)
-- variables (t₂ : is_limit c₂)
-- -- variables [has_limit (discrete.functor F.obj)]
-- -- variables [has_limit (discrete.functor (λ f, F.obj f.1.2) : discrete (Σ (p : J × J), p.fst ⟶ p.snd) ⥤ C)]
-- variables [preserves_limit (discrete.functor F.obj) T]
-- variables [preserves_limit (discrete.functor (λ f, F.obj f.1.2) : discrete (Σ (p : J × J), p.fst ⟶ p.snd) ⥤ C) T]

-- include t₁ t₂

-- def diagram : walking_parallel_pair ⥤ C :=
-- begin
--   let s : c₁.X ⟶ c₂.X,
--     refine t₂.lift (fan.mk (λ f, _ ≫ F.map f.2)),
--     exact c₁.π.app f.1.1,
--   let t : c₁.X ⟶ c₂.X,
--     refine t₂.lift (fan.mk (λ f, _)),
--     exact c₁.π.app f.1.2,
--   exact parallel_pair s t,
-- end

-- variables {c₃ : cone (diagram F t₁ t₂)}

-- @[simps] def cones_hom : (diagram F t₁ t₂).cones ⟶ F.cones :=
-- { app := λ X c,
--   { app := λ j, c.app walking_parallel_pair.zero ≫ c₁.π.app j,
--     naturality' := λ j j' f,
--     begin
--       have L := c.naturality walking_parallel_pair_hom.left,
--       have R := c.naturality walking_parallel_pair_hom.right,
--       have := R.symm.trans L,
--       have q := this =≫ c₂.π.app ⟨⟨j, j'⟩, f⟩,
--       dsimp [diagram] at q,
--       rw [assoc, assoc, t₂.fac, t₂.fac] at q,
--       dsimp at q,
--       rw q,
--       dsimp,
--       rw [id_comp, assoc],
--     end } }.

-- local attribute [semireducible] opposite.op opposite.unop opposite

-- @[simps] def cones_inv : F.cones ⟶ (diagram F t₁ t₂).cones :=
-- { app := λ X c,
--   begin
--     let π : X.unop ⟶ (diagram F t₁ t₂).obj walking_parallel_pair.zero,
--       apply t₁.lift {X := _, π := { app := c.app }},
--     let s := (diagram F t₁ t₂).map walking_parallel_pair_hom.left,
--     let t := (diagram F t₁ t₂).map walking_parallel_pair_hom.right,
--     have : π ≫ s = π ≫ t,
--       apply t₂.hom_ext,
--       rintros ⟨⟨A, B⟩, f⟩,
--       erw [assoc, assoc, t₂.fac, t₂.fac],
--       dsimp,
--       change t₁.lift _ ≫ _ ≫ _ = t₁.lift _ ≫ _,
--       rw t₁.fac,
--       rw t₁.fac_assoc,
--       change c.app A ≫ F.map f = c.app B,
--       rw ← c.naturality f,
--       apply id_comp,
--     refine ⟨_, _⟩,
--     rintro ⟨j⟩,
--     exact π,
--     exact π ≫ s,
--     dsimp,
--     rintros _ _ ⟨_ | _⟩,
--     apply id_comp,
--     rw [id_comp, this],
--     dsimp,
--     rw [functor.map_id, id_comp, comp_id],
--   end,
--   naturality' := λ X Y f,
--   begin
--     ext c j,
--     cases j,
--     apply t₁.hom_ext,
--     intro j,
--     dsimp,
--     rw [t₁.fac, assoc, t₁.fac],
--     refl,
--     dsimp,
--     rw ← assoc,
--     congr' 1,
--     apply t₁.hom_ext,
--     intro j,
--     dsimp,
--     rw [t₁.fac, assoc, t₁.fac],
--     refl,
--   end }

-- def cones_iso : (diagram F t₁ t₂).cones ≅ F.cones :=
-- { hom := cones_hom F t₁ t₂,
--   inv := cones_inv F t₁ t₂,
--   hom_inv_id' :=
--   begin
--     ext X c j,
--     cases j,
--     dsimp,
--     apply t₁.hom_ext,
--     intro j,
--     dsimp, rw t₁.fac, refl,
--     have : 𝟙 X.unop ≫ c.app walking_parallel_pair.one = c.app walking_parallel_pair.zero ≫ _ := c.naturality walking_parallel_pair_hom.left,
--       rw [id_comp] at this,
--     dsimp,
--     rw this,
--     congr' 1,
--     apply t₁.hom_ext,
--     intro j,
--     dsimp, rw t₁.fac, refl,
--   end }.


variables [has_limit F]
variables [has_limit (discrete.functor F.obj)]
variables [has_limit (discrete.functor (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2))]
variables [preserves_limit (discrete.functor F.obj) T]
variables [preserves_limit (discrete.functor (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2)) T]

-- instance [has_equalizers C] : preserves_limit F T :=
-- begin
--   let q := has_limit.of_cones_iso (has_limit_of_has_products_of_has_equalizers.diagram F) F (has_limit_of_has_products_of_has_equalizers.cones_iso F),
--   apply preserves_limit_of_preserves_limit_cone,
--   apply q.2,

-- end

end lim_of_prod_equalizer

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