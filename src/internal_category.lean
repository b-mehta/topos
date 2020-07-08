import category_theory.limits.shapes.pullbacks
import category_theory.limits.limits
import category_theory.types
import category_theory.limits.types
import category_theory.monad.algebra
import locally_cartesian_closed

namespace category_theory

open category_theory category_theory.category category_theory.limits

universes v u

variables (A : Type u) [category.{v} A] [has_finite_limits.{v} A]

structure internal_category_struct :=
(C₀ : A)
(C₁ : A)
(src trg : C₁ ⟶ C₀)
(ident : C₀ ⟶ C₁)
(comp : pullback trg src ⟶ C₁) -- pullback.fst ≫ trg = pullback.snd ≫ src
(id_src : ident ≫ src = 𝟙 _)
(id_trg : ident ≫ trg = 𝟙 _)
(comp_src : comp ≫ src = pullback.fst ≫ src)
(comp_trg : comp ≫ trg = pullback.snd ≫ trg)

section
open limits.pullback
structure internal_category extends internal_category_struct.{v} A :=
(comp_id : lift (𝟙 C₁) (trg ≫ ident) (by rw [id_comp, assoc, id_src, comp_id]) ≫ comp = 𝟙 C₁)
(id_comp : lift (src ≫ ident) (𝟙 C₁) (by rw [id_comp, assoc, id_trg, category.comp_id]) ≫ comp = 𝟙 C₁)
(assoc : (lift (lift fst (snd ≫ fst) (by rw [condition, assoc]) ≫ comp) (snd ≫ snd) (by rw [assoc, comp_trg, lift_snd_assoc, assoc, condition, assoc]) : pullback trg (fst ≫ src : pullback trg src ⟶ C₀) ⟶ _) ≫ comp = lift fst (snd ≫ comp) (by rw [condition, assoc, comp_src]) ≫ comp)
end

section type_pullback
variables {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z)

def type_pb : Type u := {p : X × Y // f p.1 = g p.2}

def proj₁ : type_pb f g ⟶ X := λ (t : type_pb f g), t.1.1
def proj₂ : type_pb f g ⟶ Y := λ (t : type_pb f g), t.1.2
lemma cond : proj₁ f g ≫ f = proj₂ f g ≫ g :=
begin
  ext ⟨_, h⟩,
  exact h
end
def is_pb : is_limit (pullback_cone.mk _ _ (cond f g)) :=
is_limit.mk' _ $ λ s,
begin
  refine ⟨λ i, ⟨⟨s.fst i, s.snd i⟩, congr_fun s.condition i⟩, rfl, rfl, _⟩,
  intros m m₁ m₂,
  ext i,
  apply congr_fun m₁ i,
  apply congr_fun m₂ i,
end
def iso_limit : type_pb f g ≅ pullback f g := is_limit.cone_point_unique_up_to_iso (is_pb f g) (limit.is_limit _)
@[reassoc] lemma iso_limit_coh₁ : (iso_limit f g).hom ≫ pullback.fst = proj₁ f g :=
pullback.lift_fst _ _ _
@[reassoc] lemma iso_limit_coh₂ : (iso_limit f g).hom ≫ pullback.snd = proj₂ f g :=
pullback.lift_snd _ _ _
@[reassoc] lemma iso_limit_coh₃ {W : Type u} (h : W ⟶ X) (k : W ⟶ Y) (comm : h ≫ f = k ≫ g) :
  pullback.lift h k comm ≫ (iso_limit f g).inv = (λ w, ⟨⟨h w, k w⟩, congr_fun comm w⟩) :=
begin
  rw iso.comp_inv_eq,
  apply pullback.hom_ext,
  rw [pullback.lift_fst, assoc, iso_limit_coh₁], refl,
  rw [pullback.lift_snd, assoc, iso_limit_coh₂], refl,
end
-- lemma iso_limit_coh₄ (x : X) (y : Y) {h : f x = g y} :
--   (iso_limit f g).hom ⟨⟨x, y⟩, h⟩ = _ := sorry

end type_pullback

instance category_struct_of_internal_category_struct_type (c : internal_category_struct.{u} (Type u)) :
  category_struct c.C₀ :=
{ hom := λ X Y, {h : c.C₁ // c.src h = X ∧ c.trg h = Y},
  id := λ X, ⟨c.ident X, congr_fun c.id_src X, congr_fun c.id_trg X⟩,
  comp := λ X Y Z f g,
  begin
    refine ⟨c.comp _, _, _⟩,
    refine ⟨λ j, option.cases_on j Y (λ j', walking_pair.cases_on j' f.1 g.1), λ j j' k, _⟩,
    cases k with _ k,
    refl,
    cases k,
    apply f.2.2,
    apply g.2.1,
    change (c.comp ≫ c.src) _ = _,
    rw [c.comp_src],
    apply f.2.1,
    change (c.comp ≫ c.trg) _ = _,
    rw [c.comp_trg],
    apply g.2.2,
  end }

def tag (n : ℕ) (α : Type u) := α

-- trash proof
-- def category_of_internal_category_type (c : internal_category.{u} (Type u)) :
--   small_category c.C₀ :=
-- { id_comp' :=
--   begin
--     rintros X Y ⟨f, rfl, rfl⟩,
--     ext1,
--     have := congr_fun c.id_comp f,
--     dsimp,
--     dsimp at this,
--     conv_rhs {rw ← this},
--     change c.comp _ = c.comp _,
--     congr' 1,
--     apply subtype.eq _,
--     ext1,
--     cases x,
--     exact (congr_fun c.id_trg (c.src f)).symm,
--     cases x,
--     refl,
--     refl,
--   end,
--   comp_id' :=
--   begin
--     rintros X Y ⟨f, rfl, rfl⟩,
--     ext1,
--     have := congr_fun c.comp_id f,
--     dsimp,
--     dsimp at this,
--     conv_rhs {rw ← this},
--     change c.comp _ = c.comp _,
--     congr' 1,
--     apply subtype.eq _,
--     ext1,
--     cases x,
--     refl,
--     cases x,
--     refl,
--     refl,
--   end,
--   assoc' :=
--   begin
--     rintros W X Y Z ⟨f, rfl, rfl⟩ ⟨g, g₁, rfl⟩ ⟨h, h₁, rfl⟩,
--     have := congr_fun c.assoc ⟨λ j, option.cases_on j (c.trg f) (λ k, walking_pair.cases_on k f ⟨λ j', option.cases_on j' (c.trg g) (λ k', walking_pair.cases_on k' g h), _⟩), _⟩,
--       swap,
--       rintro (j₁ | j₂) j₃ (k₁ | k₂ | k₃),
--       dsimp, rw functor.map_id, refl,
--       dsimp, rw functor.map_id, refl,
--       refl,
--       apply h₁,
--       swap,
--       rintros (j₁ | j₂ | j₃) j₄ (k₁ | k₂),
--       dsimp, rw functor.map_id, refl,
--       dsimp, rw functor.map_id, refl,
--       refl,
--       dsimp, rw functor.map_id, refl,
--       apply g₁,
--     rw subtype.ext,
--     dunfold category_struct.comp,
--     dsimp only [],
--     dunfold pullback.lift has_limit.is_limit at *,
--     dsimp at this,
--     simp only [assoc, c.comp_trg, c.comp_src] at this,
--     convert this,
--     clear this,
--     ext1,
--     cases x,
--     refl,
--     dsimp,
--     cases x,
--     dsimp,
--     congr' 2,
--     ext1,
--     cases x,
--     refl,
--     cases x,
--     refl,
--     refl,
--     refl,
--     clear this,
--     ext1,
--     cases x,
--     refl,
--     cases x,
--     refl,
--     refl,
--   end
-- }

@[simps]
def internal_category_struct_type_of_category_struct (A : Type u) [small_category A] : internal_category_struct.{u} (Type u) :=
{ C₀ := A,
  C₁ := Σ (X : A) (Y : A), X ⟶ Y,
  src := λ x, x.1,
  trg := λ x, x.2.1,
  ident := λ x, ⟨x, x, 𝟙 x⟩,
  comp :=
  begin
    refine (iso_limit _ _).inv ≫ _,
    intro t,
    refine ⟨t.1.1.1, t.1.2.2.1, t.1.1.2.2 ≫ eq_to_hom t.2 ≫ t.1.2.2.2⟩,
  end,
  id_src := by {ext x, refl},
  id_trg := by {ext x, refl},
  comp_src :=
  begin
    dsimp,
    rw [assoc, iso.inv_comp_eq, iso_limit_coh₁_assoc],
    ext ⟨⟨⟨X, Y, f⟩, ⟨Y', Z, g⟩⟩, h⟩,
    dsimp at h,
    subst h,
    refl,
  end,
  comp_trg :=
  begin
    dsimp,
    rw [assoc, iso.inv_comp_eq, iso_limit_coh₂_assoc],
    ext ⟨⟨⟨X, Y, f⟩, ⟨Y', Z, g⟩⟩, h⟩,
    dsimp at h,
    subst h,
    refl,
  end }

def internal_category_type_of_category (A : Type u) [small_category A] : internal_category.{u} (Type u) :=
{ comp_id :=
  begin
    ext ⟨X, Y, f⟩,
    dsimp only [internal_category_struct_type_of_category_struct],
    rw iso_limit_coh₃_assoc,
    dsimp,
    rw [comp_id, comp_id],
  end,
  id_comp :=
  begin
    dsimp only [internal_category_struct_type_of_category_struct],
    rw [iso_limit_coh₃_assoc],
    ext ⟨X, Y, f⟩,
    dsimp,
    rw [id_comp, id_comp],
  end,
  assoc :=
  begin
    dsimp only [internal_category_struct_type_of_category_struct, id],
    elide 5,
    rw [iso_limit_coh₃_assoc],
    unelide,
    simp_rw [iso_limit_coh₃_assoc],
    rw ← cancel_epi (iso_limit _ _).hom,
    ext ⟨⟨⟨X, Y, f⟩, ⟨i, hi⟩⟩, h⟩,
    dsimp at h,
    subst h,
    refine sigma.eq rfl _,
    refine sigma.eq rfl _,
    dsimp [iso_limit, is_limit.cone_point_unique_up_to_iso, is_limit.unique_up_to_iso,
           pullback_cone.mk, is_limit.lift_cone_morphism],
    simp only [assoc, id_comp],
    refl, -- WAT.
    -- this stuff is silly but can't seem to be able to avoid it...
    have : Π {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z), is_iso (iso_limit f g).hom,
      intros,
      apply is_iso.of_iso,
    refine @is_iso.epi_of_iso _ _ _ _ _ (id _),
    apply this,
  end,
  ..internal_category_struct_type_of_category_struct A }.

variable {A}
local attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits
local attribute [instance] has_pullbacks_of_has_finite_limits

def iso_comm {X Y : A} (f : X ⟶ Y) [is_locally_cartesian_closed.{v} A] :
  star Y ⋙ real_pullback f ≅ star X :=
begin
  apply nat_iso.of_components _ _,
  intro Z,
  apply over_iso _ _,
  refine ⟨_, _, _, _⟩,
  apply limits.prod.lift pullback.snd (pullback.fst ≫ limits.prod.snd),
  apply pullback.lift (limits.prod.map f (𝟙 Z)) limits.prod.fst _,
  apply limits.prod.map_fst,
  dsimp,
  apply pullback.hom_ext,
  simp only [pullback.lift_fst, limits.prod.map_fst, assoc, id_comp, prod.lift_map, comp_id],
  apply prod.hom_ext;
  simp only [pullback.condition, prod.lift_fst, prod.lift_snd],
  simp,
  apply prod.hom_ext,
  simp,
  simp only [pullback.lift_fst_assoc, assoc, id_comp, prod.lift_snd, limits.prod.map_snd, comp_id],
  dsimp, apply prod.lift_fst,
  intros P Q k,
  ext1,
  dsimp,
  rw [prod.lift_map, comp_id],
  apply prod.hom_ext;
  simp,
end

def presheaf_comonad [is_locally_cartesian_closed.{v} A] (c : internal_category.{v} A) : A ⥤ A :=
begin
  haveI : has_pullbacks.{v} A := ⟨by apply_instance⟩,
  apply star c.C₁ ⋙ dependent_product c.trg ⋙ over.forget,
end

def source {c : internal_category.{v} A} {Q : A} (f : Q ⟶ c.C₁) : Q ⟶ c.C₀ := f ≫ c.src
def target {c : internal_category.{v} A} {Q : A} (f : Q ⟶ c.C₁) : Q ⟶ c.C₀ := f ≫ c.trg
def compose (c : internal_category.{v} A) {Q : A} (f g : Q ⟶ c.C₁) (composable : target f = source g) :
  Q ⟶ c.C₁ :=
pullback.lift f g composable ≫ c.comp
def identity (c : internal_category.{v} A) {Q : A} (x : Q ⟶ c.C₀) :
  Q ⟶ c.C₁ :=
x ≫ c.ident

def elim_pi [cartesian_closed.{v} A] {B Q : A} {F} (f : Q ⟶ (Pi_functor B).obj F) (x : Q ⟶ B) : Q ⟶ F.left :=
prod.lift x (𝟙 _) ≫ (((star_adj_pi_of_exponentiable _).hom_equiv _ _).symm f).left
lemma elim_pi_prop [cartesian_closed.{v} A] {B Q : A} {F} (f : Q ⟶ (Pi_functor B).obj F) (x : Q ⟶ B) : elim_pi f x ≫ F.hom = x :=
begin
  dsimp [elim_pi],
  rw [assoc, over.w, over.mk_hom, prod.lift_fst],
end
def intro_pi [cartesian_closed.{v} A] {B Q : A} {F : over B} (lam : B ⨯ Q ⟶ F.left) (well_typed : lam ≫ F.hom = limits.prod.fst) : Q ⟶ (Pi_functor B).obj F :=
(star_adj_pi_of_exponentiable _).hom_equiv _ _ (over.hom_mk lam)
lemma compute_pi [cartesian_closed.{v} A] {B Q : A} {F : over B} (lam : B ⨯ Q ⟶ F.left) (well_typed : lam ≫ F.hom = limits.prod.fst) (x : Q ⟶ B) :
  elim_pi (intro_pi lam well_typed) x = prod.lift x (𝟙 _) ≫ lam :=
begin
  dsimp [elim_pi, intro_pi],
  rw equiv.symm_apply_apply,
  refl,
end

-- def intro_pb [is_locally_cartesian_closed.{v} A] {X Y : A} {Q B} (f : X ⟶ Y) : Q ⟶ (real_pullback f).obj B :=
-- begin
--   apply (radj f).hom_equiv _ _ _,
--   dsimp [dependent_sum],
--   apply over.hom_mk _ _,
--   dsimp, sorry,
--   dsimp, sorry
-- end

def elim_prod [is_locally_cartesian_closed.{v} A] {X Y : A} {f : X ⟶ Y} {Q R}
  (t : Q ⟶ ((dependent_product f).obj R).left) (x : Q ⟶ X) (comm : t ≫ ((dependent_product f).obj R).hom = x ≫ f) :
  Q ⟶ R.left :=
begin
  let Q' : over Y := over.mk (x ≫ f),
  let x' : Q' ⟶ over.mk f := over.hom_mk x rfl,
  let t' : Q' ⟶ (dependent_product f).obj R := over.hom_mk t comm,
  apply (elim_pi t' x').left,
end

def elim_prod_prop [is_locally_cartesian_closed.{v} A] {X Y : A} {f : X ⟶ Y} {Q R}
  (t : Q ⟶ ((dependent_product f).obj R).left) (x : Q ⟶ X) (comm : t ≫ ((dependent_product f).obj R).hom = x ≫ f) : elim_prod t x comm ≫ R.hom = x :=
begin
  let x' : over.mk (x ≫ f) ⟶ over.mk f := over.hom_mk x rfl,
  refine congr_arg comma_morphism.left (elim_pi_prop _ x'),
end

def presheaf_counit [is_locally_cartesian_closed.{v} A] (c : internal_category.{v} A) {Q Y} (t : Q ⟶ (presheaf_comonad c).obj Y) : Q ⟶ Y :=
begin
  have := elim_prod t (identity c (t ≫ ((dependent_product c.trg).obj (over.mk limits.prod.fst)).hom)) _,
    swap,
    rw [identity, assoc, c.id_trg, comp_id], refl,
  apply this ≫ limits.prod.snd,
end

-- lemma presheaf_counit_nat [is_locally_cartesian_closed.{v} A] (c : internal_category.{v} A) {Q Q'} (f : Q ⟶ Q') :
  -- (presheaf_comonad c).map f ≫ presheaf_counit c (𝟙 ((presheaf_comonad c).obj Q')) = presheaf_counit c (𝟙 ((presheaf_comonad c).obj Q)) ≫ f :=
-- begin
  -- dsimp [presheaf_counit, presheaf_comonad],
  --
-- end

-- instance [is_locally_cartesian_closed.{v} A] (c : internal_category.{v} A) : comonad (presheaf_comonad c) :=
-- { ε :=
--   { app := λ y, presheaf_counit c (𝟙 _),
--     naturality' :=
--     begin
--       intros Q Q' f,

--       rw [functor.id_map],

--     end
--     },
--   δ :=
--   { app := λ y,
--     begin
--       dsimp,

--     end

--   }

-- }

def W (Y : Type 1) : Type 1 := Σ (x : Type), Π (T : Type), (T → x) → Y
def W_functor {Y Z : Type 1} (f : Y → Z) : W Y → W Z :=
λ ⟨U, e⟩, ⟨U, λ T g, f (e T g)⟩

def ε {Y : Type 1} : W Y → Y := λ ⟨U, e⟩, e U id

lemma ε_nat {Y Z : Type 1} (f : Y → Z) : f ∘ ε = ε ∘ W_functor f :=
begin
  ext1 ⟨U, e⟩,
  dsimp [W_functor, ε],
  refl,
end

def δ {Y : Type 1} : W Y → W (W Y) := λ ⟨U, e⟩, ⟨U, λ T f, ⟨T, λ S g, e S (f ∘ g)⟩⟩


end category_theory