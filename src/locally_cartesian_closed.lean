import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.limits.shapes.images
import category_theory.limits.shapes.regular_mono
import category_theory.epi_mono
import category_theory.limits.over
import over
import images

/-!
# Locally cartesian closed categories
We say `C` is locally cartesian closed if it has all finite limits, and each
`C/B` is cartesian closed.

Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`, and so `f* : C/B ⥤ (C/B)/f` is 'the same thing' as pulling back
morphisms along `f`. In particular, `C` is locally cartesian closed iff
it has finite limits and `f* : C/B ⥤ C/A` has a right adjoint (for each
`f : A ⟶ B`).

From here, we can show that if `C` is locally cartesian closed and has
reflexive coequalizers, then every morphism factors into a regular epic
and monic.
-/
namespace category_theory
open category limits

universes v u
variables (C : Type u) [category.{v} C]

local attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits

class is_locally_cartesian_closed [has_finite_limits.{v} C] :=
(overs_cc : Π (B : C), cartesian_closed (over B))

attribute [instance] is_locally_cartesian_closed.overs_cc

def cc_of_lcc [has_finite_limits.{v} C] [is_locally_cartesian_closed.{v} C] : cartesian_closed.{v} C :=
cartesian_closed_of_equiv over_terminal

universe u₂

variable {C}
lemma equiv_reflects_mono {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
faithful_reflects_mono e.functor hef

lemma equiv_reflects_epi {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : epi (e.functor.map f)) : epi f :=
faithful_reflects_epi e.functor hef

section

lemma equiv_preserves_mono {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) [mono f] (e : C ≌ D) :
  mono (e.functor.map f) :=
begin
  apply equiv_reflects_mono ((e.functor).map f) e.symm,
  erw equivalence.inv_fun_map,
  apply mono_comp _ _,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _),
  apply is_iso.of_iso_inverse,
  apply mono_comp _ _,
  apply_instance,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _),
  apply is_iso.of_iso,
end

lemma equiv_preserves_epi {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) [epi f] (e : C ≌ D) :
  epi (e.functor.map f) :=
begin
  apply equiv_reflects_epi ((e.functor).map f) e.symm,
  erw equivalence.inv_fun_map,
  apply epi_comp _ _,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _),
  apply is_iso.of_iso_inverse,
  apply epi_comp _ _,
  apply_instance,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _),
  apply is_iso.of_iso,
end
end

lemma over_epi {B : C} {f g : over B} (k : f ⟶ g) [epi k.left] : epi k :=
⟨λ h l m a, by { ext, rw [← cancel_epi k.left, ← over.comp_left, a], refl }⟩

lemma over_epi' [has_binary_products.{v} C] {B : C} {f g : over B} (k : f ⟶ g) [ke : epi k] : epi k.left :=
left_adjoint_preserves_epi (forget_adj_star _) ke

local attribute [instance] has_pullbacks_of_has_finite_limits
variables [has_finite_limits.{v} C] [is_locally_cartesian_closed.{v} C]

def dependent_product {A B : C} (f : A ⟶ B) : over A ⥤ over B :=
(over.iterated_slice_equiv (over.mk f)).inverse ⋙ Pi_functor (over.mk f)

def ladj' {A B : C} (f : A ⟶ B) : pullback_along f ⊣ dependent_product f :=
adjunction.comp _ _ (star_adj_pi_of_exponentiable (over.mk f)) (equivalence.to_adjunction _)

def ladj {A B : C} (f : A ⟶ B) : real_pullback f ⊣ dependent_product f :=
adjunction.of_nat_iso_left (ladj' f) (iso_pb f)

instance other_thing {A B : C} (f : A ⟶ B) : is_left_adjoint (real_pullback f) :=
⟨dependent_product f, ladj _⟩

/--
 P ⟶ D
 ↓   ↓
 A → B
If g : D ⟶ B is epi then the pullback of g along f is epi
-/

instance pullback_preserves_epi {A B D : C}
  (f : A ⟶ B) (g : D ⟶ B) [hg : epi g] :
  epi (pullback.snd : pullback g f ⟶ A) :=
begin
  let g'' : over.mk g ⟶ over.mk (𝟙 B) := over.hom_mk g,
  haveI : epi g''.left := hg,
  haveI := left_adjoint_preserves_epi (ladj f) (over_epi g''),
  have : ((real_pullback f).map g'').left ≫ pullback.snd = pullback.snd := pullback.lift_snd _ pullback.snd _,
  rw ← this,
  have : epi ((real_pullback f).map g'').left := over_epi' _,
  haveI : split_epi (pullback.snd : pullback (𝟙 B) f ⟶ A) := ⟨pullback.lift f (𝟙 A) (by simp), pullback.lift_snd _ _ _⟩,
  apply epi_comp,
end

lemma pullback_preserves_epi'' {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} [hg : epi g] {c : pullback_cone g f} (t : is_limit c) :
epi (pullback_cone.snd c) :=
begin
  have y := is_limit.unique_up_to_iso t (limit.is_limit _),
  have z : pullback_cone.snd c = y.hom.hom ≫ pullback_cone.snd (limit.cone (cospan g f)),
    rw y.hom.w,
  rw z, apply epi_comp _ _,
    apply @is_iso.epi_of_iso _ _ _ _ _ _, refine ⟨_, _, _⟩, apply y.inv.hom,
    show ((y.hom ≫ y.inv).hom = 𝟙 c.X), rw y.hom_inv_id, refl,
    show ((y.inv ≫ y.hom).hom = 𝟙 _), rw y.inv_hom_id, refl,
  exact category_theory.pullback_preserves_epi f g
end

lemma prod_map_epi {A B : C} (D : C) {q : A ⟶ B} [hq : epi q] : epi (limits.prod.map q (𝟙 D)) :=
pullback_preserves_epi'' _ (pullback_prod _ _)

lemma prod_map_epi' {A B : C} (D : C) {q : A ⟶ B} [hq : epi q] : epi (limits.prod.map (𝟙 D) q) :=
pullback_preserves_epi'' _ (pullback_prod' q D)

instance prod_maps_epi {X Y Z W : C} (f : X ⟶ Y) (g : W ⟶ Z) [epi f] [epi g] : epi (limits.prod.map f g) :=
begin
  have: limits.prod.map f g = limits.prod.map (𝟙 _) g ≫ limits.prod.map f (𝟙 _),
  { apply prod.hom_ext,
    { rw [limits.prod.map_fst, assoc, limits.prod.map_fst, limits.prod.map_fst_assoc, id_comp] },
    { rw [limits.prod.map_snd, assoc, limits.prod.map_snd, comp_id, limits.prod.map_snd] } },
  rw this,
  apply epi_comp _ _,
  apply prod_map_epi',
  apply prod_map_epi
end

section pullback_preserves_colimits

variables {J : Type v} [small_category J] [has_colimits_of_shape J C]
variables {Y Z : C} (f : Y ⟶ Z)

local attribute [-instance] adjunction.has_colimit_comp_equivalence

@[simps]
def pullback_diagram (K : J ⥤ C) (c : cocone K) (r : c.X ⟶ Z) : J ⥤ C :=
{ obj := λ j, pullback (c.ι.app j ≫ r : K.obj j ⟶ Z) f,
  map := λ j₁ j₂ k,
  begin
    apply pullback.lift (pullback.fst ≫ K.map k) pullback.snd _,
    simp [reassoc_of (c.w k), pullback.condition],
  end }.

@[simps]
def pullback_cocone (K : J ⥤ C) (c : cocone K) (r : c.X ⟶ Z) : cocone (pullback_diagram f K c r) :=
{ X := pullback r f,
  ι :=
  { app := λ j,
    begin
      apply pullback.lift _ pullback.snd _,
      apply pullback.fst ≫ c.ι.app j,
      rw [assoc, pullback.condition],
    end } }

@[simps]
def long_diagram (K : J ⥤ C) (c : cocone K) (r : c.X ⟶ Z) : J ⥤ over Z :=
{ obj := λ j, over.mk (c.ι.app j ≫ r),
  map := λ j₁ j₂ k, over.hom_mk (K.map k) (by { dsimp, rw reassoc_of (c.w k) }) }

@[simps]
def long_cone {K : J ⥤ C} (c : cocone K) (r : c.X ⟶ Z) : cocone (long_diagram K c r) :=
{ X := over.mk r,
  ι := { app := λ j, over.hom_mk (c.ι.app j) } }.

def diagram_iso {K : J ⥤ C} (c : cocone K) (r : c.X ⟶ Z) : (long_diagram K c r ⋙ over.forget) ≅ K :=
nat_iso.of_components (λ k, iso.refl _) (by tidy)

def forget_long_cocone_iso {K : J ⥤ C} (c : cocone K) (r : c.X ⟶ Z) :
  over.forget.map_cocone (long_cone c r) ≅ (cocones.precompose (diagram_iso c r).hom).obj c :=
cocones.ext (iso.refl _) (begin intro j, dsimp [diagram_iso], simp end)

def long_colimit {K : J ⥤ C} (c : cocone K) (r : c.X ⟶ Z) (t : is_colimit c) : is_colimit (long_cone c r) :=
begin
  suffices : is_colimit (over.forget.map_cocone (long_cone c r)),
    apply reflects_colimit.reflects this,
  apply limits.is_colimit.of_iso_colimit _ (forget_long_cocone_iso _ _).symm,
  apply is_colimit.of_left_adjoint (cocones.precompose_equivalence (diagram_iso _ r)).functor t,
end

def pullback_diagram_iso {K : J ⥤ C} (c : cocone K) (r : c.X ⟶ Z) :
  ((long_diagram K c r ⋙ real_pullback f) ⋙ over.forget) ≅ pullback_diagram f K c r :=
nat_iso.of_components (λ j, iso.refl _) (by tidy)

def pullback_preserves {K : J ⥤ C} (c : cocone K) (t : is_colimit c) (r : c.X ⟶ Z) : is_colimit (pullback_cocone f K c r) :=
begin
  haveI : preserves_colimits (real_pullback f) := adjunction.left_adjoint_preserves_colimits (ladj f),
  let e := cocones.precompose_equivalence (pullback_diagram_iso f c r),
  let c' := is_colimit.of_left_adjoint e.inverse (preserves_colimit.preserves (preserves_colimit.preserves (long_colimit c r t))),
  apply is_colimit.of_iso_colimit c',
  apply cocones.ext _ _,
  apply iso.refl _,
  intro j,
  dsimp [pullback_diagram_iso],
  simpa
end

@[simps]
def pullback_along_id : pullback (𝟙 Z) f ≅ Y :=
{ hom := pullback.snd,
  inv := pullback.lift f (𝟙 _) (by simp),
  hom_inv_id' :=
  begin
    apply pullback.hom_ext,
    rw [assoc, pullback.lift_fst, ← pullback.condition], simp,
    simp,
  end }

end pullback_preserves_colimits

variables [has_coequalizers.{v} C]
section factorise

instance : has_strong_epi_mono_factorisations.{v} C :=
{ has_fac := λ A B f,
  { I := coequalizer (pullback.fst : pullback f f ⟶ A) pullback.snd,
    m := coequalizer.desc f pullback.condition,
    e := coequalizer.π pullback.fst pullback.snd,
    m_mono := ⟨λ D g h gmhm,
    begin
      let q := coequalizer.π pullback.fst pullback.snd,
      let E := pullback (limits.prod.map q q) (limits.prod.lift g h),
      let n : E ⟶ D := pullback.snd,
      let k : E ⟶ A := pullback.fst ≫ limits.prod.fst,
      let l : E ⟶ A := pullback.fst ≫ limits.prod.snd,
      have kqng: k ≫ q = n ≫ g,
        have: _ = (n ≫ _) ≫ _ := pullback.condition =≫ limits.prod.fst,
        simpa using this,
      have lqnh: l ≫ q = n ≫ h,
        have: _ = (n ≫ _) ≫ _ := pullback.condition =≫ limits.prod.snd,
        simpa using this,
      have kflf: k ≫ f = l ≫ f,
        rw [← coequalizer.π_desc f pullback.condition, ← assoc, kqng, assoc, gmhm, ← assoc, ← lqnh, assoc],
      have aqbq : _ ≫ q = _ ≫ q := coequalizer.condition _ _,
      have: n ≫ g = n ≫ h,
        rw [← kqng, ← pullback.lift_fst k l kflf, assoc, aqbq, pullback.lift_snd_assoc _ _ _, lqnh],
      rwa ← cancel_epi n,
    end⟩ } }.

/-- The strong epi-mono factorisation is actually a regular epi-mono factorisation. -/
instance {A B : C} (f : A ⟶ B) : regular_epi (factor_thru_image f) :=
category_theory.coequalizer_regular _ _

end factorise

-- This is slow and horrible :(
instance pullback_regular_epi {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [gr : regular_epi g] [has_coequalizers.{v} C] :
  regular_epi (pullback.snd : pullback g f ⟶ Y) :=
{ W := pullback ((gr.left ≫ g) ≫ 𝟙 _) f,
  left :=
  begin
    apply pullback.lift (pullback.fst ≫ gr.left) pullback.snd _,
    rw [← pullback.condition, comp_id, assoc],
  end,
  right :=
  begin
    apply pullback.lift (pullback.fst ≫ gr.right) pullback.snd _,
    rw [← pullback.condition, comp_id, assoc, gr.w],
  end,
  w := by simp,
  is_colimit :=
  begin
    have := pullback_preserves f _ gr.is_colimit (𝟙 Z),
    apply is_colimit.of_iso_colimit (is_colimit.of_left_adjoint (cocones.precompose_equivalence _).inverse this),
    swap,
    { apply nat_iso.of_components _ _,
      { rintro ⟨j⟩,
        { apply iso.refl _ },
        { refine ⟨pullback.lift pullback.fst pullback.snd _, pullback.lift pullback.fst pullback.snd _, _, _⟩,
          { rw ← pullback.condition,
            dsimp,
            conv_rhs {congr, skip, erw comp_id} },
          { dsimp,
            conv_lhs {congr, skip, erw comp_id},
            rw pullback.condition },
          { apply pullback.hom_ext; simp only [assoc, id_comp, pullback.lift_fst, pullback.lift_snd] },
          { apply pullback.hom_ext; simp only [assoc, id_comp, pullback.lift_fst, pullback.lift_snd] } } },
    { rintro k₁ k₂ i,
      cases i,
      { dsimp, rw [id_comp],
        apply pullback.hom_ext; simp },
      { dsimp,
        rw [id_comp],
        apply pullback.hom_ext; simp },
      { cases k₁,
        { dsimp, rw [id_comp], simp only [functor.map_id, comp_id], apply pullback.hom_ext,
          { simp only [pullback.lift_fst], erw [id_comp, comp_id, comp_id] },
          { simp only [pullback.lift_snd], erw [id_comp] } },
        { dsimp, simp only [functor.map_id, comp_id, id_comp], conv_rhs {apply_congr comp_id},
          apply pullback.hom_ext,
          { simp only [assoc, pullback.lift_fst], apply comp_id },
          { simp only [assoc, pullback.lift_snd] } } } } },
    dsimp [cocones.precompose_equivalence, cocones.precompose],
    apply cocones.ext _ _,
    apply pullback_along_id,
    dsimp,
    rintro ⟨j⟩,
    dsimp, simp,
    dsimp, simp,
    apply_instance,
  end }.

def pullback_image {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [has_coequalizers.{v} C] :
  pullback (image.ι g) f ≅ image (pullback.snd : pullback g f ⟶ _) :=
begin
  let red : pullback g f ⟶ pullback (image.ι g) f, -- := pullback.lift (pullback.fst ≫ factor_thru_image g) pullback.snd _,
    apply pullback.lift (pullback.fst ≫ factor_thru_image g) pullback.snd _,
    simp [pullback.condition],
  let green : pullback (factor_thru_image g) (pullback.fst : pullback (image.ι g) f ⟶ _) ⟶ pullback (image.ι g) f,
    apply pullback.snd,
  have : regular_epi green := by apply_instance,
  let red_to_green : pullback (factor_thru_image g) (pullback.fst : pullback (image.ι g) f ⟶ _) ⟶ pullback g f,
    apply pullback.lift pullback.fst (pullback.snd ≫ pullback.snd) _,
    rw [assoc, ←pullback.condition, ←pullback.condition_assoc, image.fac g],
  let green_to_red : pullback g f ⟶ pullback (factor_thru_image g) (pullback.fst : pullback (image.ι g) f ⟶ _),
    apply pullback.lift pullback.fst red _,
    rw [pullback.lift_fst],
  have : split_epi green_to_red,
    refine { section_ := red_to_green, id' := _ },
    apply pullback.hom_ext,
    { simp },
    { apply pullback.hom_ext; simp [pullback.condition] },
  haveI := this,
  have : regular_epi green := by apply_instance,
  haveI : strong_epi (green_to_red ≫ green) := strong_epi_comp _ _,
  apply unique_factorise _ _ (green_to_red ≫ green) pullback.snd _,
  simp,
end

variable [has_coequalizers.{v} C]

lemma pullback_image_fac {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [has_coequalizers.{v} C] :
  (pullback_image f g).hom ≫ image.ι (pullback.snd : pullback g f ⟶ Y) = (pullback.snd : pullback (image.ι g) f ⟶ Y) :=
is_image.lift_fac _ _

lemma pullback_image_inv_fac {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [has_coequalizers.{v} C] :
  (pullback_image f g).inv ≫ (pullback.snd : pullback (image.ι g) f ⟶ Y) = image.ι (pullback.snd : pullback g f ⟶ Y) :=
image.lift_fac _

def regular_epi_of_regular_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi f] [r : regular_epi (f ≫ g)] : regular_epi g :=
{ W := r.W,
  left := r.left ≫ f,
  right := r.right ≫ f,
  w := by rw [assoc, assoc, r.w],
  is_colimit := cofork.is_colimit.mk _
  (λ s, begin apply (cofork.is_colimit.desc' r.is_colimit (f ≫ s.π) _).1, rw [← assoc, s.condition, assoc], end)
  (begin intro s, erw [← cancel_epi f, ← assoc, (cofork.is_colimit.desc' r.is_colimit (f ≫ s.π) _).2], end)
  (begin
    intros s m w,
    apply cofork.is_colimit.hom_ext r.is_colimit,
    erw [assoc, w walking_parallel_pair.one, (cofork.is_colimit.desc' r.is_colimit (f ≫ s.π) _).2]
  end) }

def regular_epi_of_is_pullback {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z)
  (comm : f ≫ h = g ≫ k) (l : is_limit (pullback_cone.mk _ _ comm)) [regular_epi h] :
  regular_epi g :=
begin
  have e : regular_epi (pullback.snd : pullback h k ⟶ Y) := category_theory.pullback_regular_epi k h,
  have : (pullback.snd : pullback h k ⟶ Y) = l.lift _ ≫ g := (l.fac _ walking_cospan.right).symm,
  rw this at e,
  have : split_epi (l.lift (limit.cone (cospan h k))),
    refine ⟨limit.lift _ (pullback_cone.mk f g comm), _⟩,
    dsimp,
    apply l.hom_ext,
    apply (pullback_cone.mk f g comm).equalizer_ext,
    erw [assoc, l.fac (limit.cone (cospan h k)) walking_cospan.left, limit.lift_π, id_comp],
    erw [assoc, l.fac (limit.cone (cospan h k)) walking_cospan.right, limit.lift_π, id_comp],
  haveI := this,
  apply regular_epi_of_regular_epi (l.lift (limit.cone (cospan h k))) g,
end

def regular_epi_of_is_pullback_alt {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z)
  (comm : f ≫ h = g ≫ k) (l : is_limit (pullback_cone.mk _ _ comm)) [regular_epi k] :
  regular_epi f := regular_epi_of_is_pullback g f k h comm.symm (pullback_flip l)

def regular_epi_of_comp_iso {X Y Z : C} (f : X ⟶ Y) [r : regular_epi f] (g : Y ⟶ Z) [is_iso g] :
  regular_epi (f ≫ g) :=
{ W := r.W,
  left := r.left,
  right := r.right,
  w := begin rw [reassoc_of r.w], end,
  is_colimit := cofork.is_colimit.mk _
  (λ s, inv g ≫ r.is_colimit.desc _)
  (λ s, begin change (_ ≫ g) ≫ inv g ≫ _ = _, erw [assoc, (as_iso g).hom_inv_id_assoc, r.is_colimit.fac _ walking_parallel_pair.one], end)
  (λ s m w, begin erw (as_iso g).eq_inv_comp, apply r.is_colimit.uniq, intro j, rw ← w j, cases j; simp end) }

def regular_epi_of_strong_epi {X Y : C} (f : X ⟶ Y) [strong_epi f] : regular_epi f :=
begin
  haveI : regular_epi (factor_thru_image f) := by apply_instance,
  have : strong_epi (factor_thru_image f ≫ image.ι f),
    rwa image.fac f,
  haveI := this,
  haveI : strong_epi (image.ι f) := strong_epi_of_strong_epi (factor_thru_image f) _,
  haveI : is_iso (image.ι f) := is_iso_of_mono_of_strong_epi _,
  rw ← image.fac f,
  apply regular_epi_of_comp_iso,
end

instance regular_epi_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [regular_epi f] [regular_epi g] : regular_epi (f ≫ g) :=
by { haveI := strong_epi_comp f g; exact regular_epi_of_strong_epi (f ≫ g) }

instance regular_prod_map {X Y Z W : C} (f : X ⟶ Y) (g : W ⟶ Z) [regular_epi f] [regular_epi g] :
  regular_epi (limits.prod.map f g) :=
begin
  have : regular_epi (limits.prod.map f (𝟙 W)) := regular_epi_of_is_pullback _ _ _ _ _ (pullback_prod f W),
  haveI : regular_epi (limits.prod.map (𝟙 Y) g) := regular_epi_of_is_pullback _ _ _ _ _ (pullback_prod' g Y),
  have : limits.prod.map f (𝟙 W) ≫ limits.prod.map (𝟙 Y) g = limits.prod.map f g,
    apply prod.hom_ext; simp only [limits.prod.map_fst, limits.prod.map_snd, assoc, comp_id, limits.prod.map_snd_assoc, id_comp],
  rw ← this,
  apply_instance,
end

def image_prod_map {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) : image (limits.prod.map f g) ≅ image f ⨯ image g :=
begin
  symmetry,
  apply unique_factorise _ _ (limits.prod.map (factor_thru_image f) (factor_thru_image g)) (limits.prod.map (image.ι f) (image.ι g)) _,
  apply prod.hom_ext; simp,
end

lemma image_prod_map_comp {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) : (image_prod_map f g).hom ≫ limits.prod.map (image.ι f) (image.ι g) = image.ι _ :=
image.lift_fac _

lemma image_prod_map_inv_comp {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) : (image_prod_map f g).inv ≫ image.ι _ = limits.prod.map (image.ι f) (image.ι g) :=
is_image.lift_fac _ _

end category_theory
