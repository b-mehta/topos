import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.epi_mono
import cartesian_closed
import category_theory.limits.over
import pullbacks
import comma
import over

-- This file is largely commented out for now.

/-!
OLD:
# Properties of the over category.
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
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

local attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits

class is_locally_cartesian_closed [has_finite_limits.{v} C] :=
(overs_cc : Π (B : C), is_cartesian_closed (over B))

attribute [instance] is_locally_cartesian_closed.overs_cc
-- attribute [instance] has_pullbacks_of_has_finite_limits

def over_terminal [has_terminal.{v} C] : over (⊤_ C) ≌ C :=
{ functor := over.forget,
  inverse :=
  { obj := λ X, over.mk (terminal.from X),
    map := λ X Y f, over.hom_mk f },
  unit_iso :=
  begin
    refine nat_iso.of_components (λ X, { hom := over.hom_mk (𝟙 _), inv := over.hom_mk (𝟙 _) } ) _,
    intros X Y f,
    ext1,
    simp,
  end,
  counit_iso := iso.refl _,
}

instance cc_of_lcc [has_finite_limits.{v} C] [is_locally_cartesian_closed.{v} C] : is_cartesian_closed.{v} C :=
cartesian_closed_of_equiv (over_terminal C)

universe u₂

variable {C}
lemma equiv_reflects_mono {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
faithful_reflects_mono e.functor hef

lemma equiv_reflects_epi {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : epi (e.functor.map f)) : epi f :=
faithful_reflects_epi e.functor hef

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

lemma over_epi {B : C} {f g : over B} {k : f ⟶ g} [epi k.left] : epi k :=
begin
  split, intros h l m a, ext, rw [← cancel_epi k.left, ← over.comp_left, a], refl
end

lemma over_epi' [has_binary_products.{v} C] (B : C) (f g : over B) (k : f ⟶ g) [ke : epi k] : epi k.left :=
left_adjoint_preserves_epi (forget_adj_star _) ke

-- lemma over_epi'' [has_binary_products.{v} C] (B : C) (f g : over B) (k : f ⟶ g) : epi k ↔ epi k.left :=
-- ⟨λ ke, by exactI (over_epi' _ _ _ _), over_epi⟩

-- section
-- local attribute [instance] over.construct_products.over_binary_product_of_pullback

-- @[reducible]
-- def pullback_along [has_pullbacks.{v} C] {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
-- star (over.mk f) ⋙ (over.iterated_slice_equiv _).functor

-- def over_iso {B : C} (f g : over B) (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) : (f ≅ g) :=
-- { hom := over.hom_mk hl.hom, inv := over.hom_mk hl.inv (by simp [iso.inv_comp_eq, hw]) }

-- def over_left_iso {B : C} {f g : over B} (hf : f ≅ g) : f.left ≅ g.left :=
-- { hom := hf.hom.left,
--   inv := hf.inv.left,
--   hom_inv_id' := begin rw [← over.comp_left, hf.hom_inv_id], refl end,
--   inv_hom_id' := begin rw [← over.comp_left, hf.inv_hom_id], refl end}

-- lemma pullback_along_obj_of_id [has_pullbacks.{v} C] {A B : C} (f : A ⟶ B) : (pullback_along f).obj (over.mk (𝟙 B)) ≅ over.mk (𝟙 A) :=
-- begin
--   apply over_iso, swap,
--   have: over.mk f⨯⊤_ over B ≅ over.mk f, apply prod.right_unitor,
--   apply over_left_iso this,
--   dunfold over_left_iso over.iterated_slice_equiv pullback_along equivalence.mk, simp, dsimp, simp,
-- end

-- -- lemma pullback_of_obj [has_pullbacks.{v} C] {A B D : C} (f : A ⟶ B) (g : D ⟶ B) :
-- --   ((pullback_along f).map (terminal.from (over.mk g))).left = (pullback.fst : pullback f g ⟶ A) ≫ (pullback.with_id_l f).inv :=
-- -- begin
-- --   dsimp [pullback_along, equivalence.mk, pullback.with_id_l, pullback.with_id_r, identify_limit_apex, iso_apex_of_iso_cone, pullback.with_id_r', pullback.flip', flip_limit_cone, cospan_cone.flip, is_limit.unique_up_to_iso, is_limit.lift_cone_morphism],
-- --   ext, simp, dsimp, erw limit.lift_π, simp, dunfold pullback_cone.snd, dsimp, simp, erw limit.lift_π, dsimp, simp,
-- --   erw limit.lift_π, dsimp, symmetry, exact pullback.condition,
-- -- end

-- #print instances has_binary_products

-- end

def over_iso {B : C} {f g : over B} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) : (f ≅ g) :=
{ hom := over.hom_mk hl.hom, inv := over.hom_mk hl.inv (by simp [iso.inv_comp_eq, hw]) }

variables [has_finite_limits.{v} C] [is_locally_cartesian_closed.{v} C]

@[simps]
def real_pullback {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
{ obj := λ g, over.mk (pullback.fst : pullback f g.hom ⟶ A),
  map := λ g h k,
  begin
    apply over.hom_mk _ _,
    apply pullback.lift pullback.fst _ _,
    apply pullback.snd ≫ k.left,
    rw pullback.condition,
    rw assoc,
    rw over.w k,
    dsimp,
    rw limit.lift_π,
    refl
  end }


def pullback_along {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
star (over.mk f) ⋙ (over.iterated_slice_equiv _).functor

def iso_pb {A B : C} (f : A ⟶ B) : pullback_along f ≅ real_pullback f :=
begin
  refine nat_iso.of_components _ _,
  { intro X,
    let p : over B := over.mk (pullback.fst ≫ f : pullback f X.hom ⟶ B),
    let q : p ⟶ over.mk f ⨯ X := prod.lift (over.hom_mk pullback.fst rfl) (over.hom_mk pullback.snd pullback.condition.symm),
    apply over_iso _ _,
    { refine ⟨pullback.lift _ _ _, q.left, _, _⟩,
      { apply (limits.prod.fst : over.mk f ⨯ X ⟶ over.mk f).left },
      { apply (limits.prod.snd : over.mk f ⨯ X ⟶ X).left },
      { rw over.w (limits.prod.snd : over.mk f ⨯ X ⟶ X),
        exact over.w (limits.prod.fst : over.mk f ⨯ X ⟶ over.mk f) },
      { rw ← cancel_mono (magic_arrow X (over.mk f)),
        rw id_comp,
        apply prod.hom_ext,
        { rw [prod.lift_fst, assoc, prod.lift_fst, assoc, ← over.comp_left, prod.lift_fst, over.hom_mk_left, limit.lift_π],
          refl },
        { rw [prod.lift_snd, assoc, prod.lift_snd, assoc, ← over.comp_left, prod.lift_snd, over.hom_mk_left, limit.lift_π],
          refl } },
      { apply pullback.hom_ext,
        { erw [id_comp, assoc, limit.lift_π, ← over.comp_left, prod.lift_fst], refl },
        { erw [id_comp, assoc, limit.lift_π, ← over.comp_left, prod.lift_snd], refl } } },
    { exact limit.lift_π _ _ } },
  { intros X Y g,
    ext1,
    apply pullback.hom_ext,
    { dsimp [pullback_along, over_iso],
      rw [assoc, assoc, limit.lift_π, limit.lift_π],
      dsimp,
      rw [limit.lift_π, ← over.comp_left, limits.prod.map_fst, comp_id],
      refl },
    { dsimp [pullback_along, over_iso],
      rw [assoc, assoc, limit.lift_π, limit.lift_π],
      dsimp,
      rw [limit.lift_π_assoc, ← over.comp_left, limits.prod.map_snd],
      refl } }
end

def ladj {A B : C} (f : A ⟶ B) : pullback_along f ⊣ _ ⋙ Pi_functor (over.mk f) :=
adjunction.comp _ _ (star_adj_pi_of_exponentiable (over.mk f)) (equivalence.to_adjunction _)

def ladj' {A B : C} (f : A ⟶ B) : real_pullback f ⊣ (over.iterated_slice_equiv (over.mk f)).inverse ⋙ Pi_functor (over.mk f) :=
adjunction_of_nat_iso_left (ladj f) (iso_pb f)

lemma other_thing {A B : C} (f : A ⟶ B) : is_left_adjoint (real_pullback f) :=
⟨(over.iterated_slice_equiv (over.mk f)).inverse ⋙ Pi_functor (over.mk f), adjunction_of_nat_iso_left (ladj f) (iso_pb f)⟩

-- end
/--
 P ⟶ A
 ↓   ↓
 D ↠ B
If g : D ⟶ B is epi then the pullback of g along f is epi
-/
theorem pullback_preserves_epi {A B D : C}
  (f : A ⟶ B) (g : D ⟶ B) [hg : epi g] :
  epi (pullback.fst : pullback f g ⟶ A) :=
begin
  let g' := over.mk g,
  let g'' : g' ⟶ over.mk (𝟙 B) := over.hom_mk g,
  resetI,
  haveI hg'' : epi g'' := @over_epi _ _ _ _ _ g'' hg,
  let g''' := (real_pullback f).map g'',
  haveI : epi g''' := left_adjoint_preserves_epi (ladj' f) hg'',
  have: g'''.left = pullback.lift pullback.fst (pullback.snd ≫ g) _,
    refl,
  let h : pullback f g ⟶ pullback f (𝟙 B) := g'''.left,
  let k : pullback f (𝟙 B) ⟶ A := pullback.fst,
  have: h ≫ k = pullback.fst := limit.lift_π _ _,
  rw ← this,
  haveI : epi h := over_epi' _ _ _ _,
  have: split_epi k := ⟨pullback.lift (𝟙 A) f (by simp), limit.lift_π _ _⟩,
  apply epi_comp,
end

lemma pullback_preserves_epi' {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} (hg : epi g) :
epi (pullback.snd : pullback g f ⟶ A) :=
begin
  let t : pullback g f ⟶ pullback f g := pullback.lift pullback.snd pullback.fst pullback.condition.symm,
  have: pullback.lift pullback.snd pullback.fst pullback.condition.symm ≫ t = 𝟙 _,
    apply pullback.hom_ext,
    { simp },
    { simp },
  have : split_epi t := ⟨_, this⟩,
  have : t ≫ pullback.fst = (pullback.snd : pullback g f ⟶ A) := limit.lift_π _ _,
  rw ← this,
  haveI := pullback_preserves_epi f g,
  apply epi_comp,
end
--   have: (pullback.snd : pullback g f ⟶ A) = (pullback.flip' _ _).hom ≫ (pullback.fst : pullback f g ⟶ A), -- TODO: this should be a lemma
--     dunfold pullback.flip' iso_apex_of_iso_cone flip_limit_cone flip_hom flip_twice, dsimp, erw id_comp, rw [limit.lift_π], refl,
--   rw this, apply epi_comp _ _, apply is_iso.epi_of_iso,
--   apply pullback_preserves_epi _ hg
-- end
lemma pullback_preserves_epi'' {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} (hg : epi g) {c : pullback_cone g f} (t : is_limit c) :
epi (pullback_cone.snd c) :=
begin
  have y := is_limit.unique_up_to_iso t (limit.is_limit _),
  have z: pullback_cone.snd c = y.hom.hom ≫ pullback_cone.snd (limit.cone (cospan g f)),
    rw y.hom.w,
  rw z, apply epi_comp _ _,
    apply @is_iso.epi_of_iso _ _ _ _ _ _, refine ⟨_, _, _⟩, apply y.inv.hom,
    show ((y.hom ≫ y.inv).hom = 𝟙 c.X), rw y.hom_inv_id, refl,
    show ((y.inv ≫ y.hom).hom = 𝟙 _), rw y.inv_hom_id, refl,
  exact pullback_preserves_epi' f hg
end

lemma prod_map_epi {A B : C} (D : C) {q : A ⟶ B} [hq : epi q] : epi (limits.prod.map q (𝟙 D)) :=
pullback_preserves_epi'' _ hq (pullback_prod _ _)

lemma prod_map_epi' {A B : C} (D : C) {q : A ⟶ B} [hq : epi q] : epi (limits.prod.map (𝟙 D) q) :=
pullback_preserves_epi'' _ hq (pullback_prod' q D)

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

variables [has_coequalizers.{v} C] {A B : C} (f : A ⟶ B)

-- Technically the regular coimage, but in a LCCC with coequalizers it is the image
def image : C := coequalizer (pullback.fst : pullback f f ⟶ A) (pullback.snd : pullback f f ⟶ A)
def epi_part : A ⟶ image f := coequalizer.π pullback.fst pullback.snd
def mono_part : image f ⟶ B := coequalizer.desc f pullback.condition

lemma factorises : epi_part f ≫ mono_part f = f :=
by simp [epi_part, mono_part]

lemma coequalizer_epi (g h : A ⟶ B) : epi (coequalizer.π g h) :=
begin
  split, intros k l m q, apply colimit.hom_ext, intro, cases j,
  rw ← colimit.w (parallel_pair _ _) walking_parallel_pair_hom.left, rw assoc, rw q, simp,
  exact q,
end
instance epi_part_is_epi : epi (epi_part f) := coequalizer_epi _ _

lemma mono_part_is_mono : mono (mono_part f) :=
begin
  split, intros D g h gmhm,
  set R := pullback f f,
  set I := image f,
  set q := epi_part f,
  set m := mono_part f,
  set E := pullback (limits.prod.map q q) (limits.prod.lift g h),
  set n : E ⟶ D := pullback.snd,
  set kl : E ⟶ A ⨯ A := pullback.fst,
  set a : R ⟶ A := pullback.fst,
  set b : R ⟶ A := pullback.snd,
  set k : E ⟶ A := kl ≫ limits.prod.fst,
  set l : E ⟶ A := kl ≫ limits.prod.snd,
  have kqng: k ≫ q = n ≫ g,
    have: (kl ≫ limits.prod.map q q) ≫ limits.prod.fst = (n ≫ limits.prod.lift g h) ≫ limits.prod.fst, rw pullback.condition,
    rw [assoc, assoc, prod.lift_fst, limits.prod.map_fst, ← assoc] at this, exact this,
  have lqnh: l ≫ q = n ≫ h,
    have: (kl ≫ limits.prod.map q q) ≫ limits.prod.snd = (n ≫ limits.prod.lift g h) ≫ limits.prod.snd, rw pullback.condition,
    rw [assoc, assoc, prod.lift_snd, limits.prod.map_snd, ← assoc] at this, exact this,
  have kflf: k ≫ f = l ≫ f,
    rw [← factorises f, ← assoc, kqng, assoc, gmhm, ← assoc, ← lqnh, assoc],
  set p : E ⟶ R := pullback.lift k l kflf,
  have pak: p ≫ a = k, simp,
  have pbl: p ≫ b = l, simp,
  have aqbq: a ≫ q = b ≫ q := coequalizer.condition a b,
  have: n ≫ g = n ≫ h,
    rw [← kqng, ← pak, assoc, aqbq, ← assoc, pbl, lqnh],
  haveI: epi n := pullback_preserves_epi' _ _,
  rwa ← cancel_epi n,
  apply_instance,
end

variable {f}
def image_map {A' B' : C} {f' : A' ⟶ B'} {l : A ⟶ A'} {r : B ⟶ B'} (h : l ≫ f' = f ≫ r) : image f ⟶ image f' :=
begin
  apply coequalizer.desc (l ≫ epi_part f'),
  rw ← @cancel_mono _ _ _ _ _ (mono_part f') (mono_part_is_mono _),
  rw assoc, rw assoc, rw factorises, rw assoc, rw assoc, rw factorises,
  rw h,
  rw ← factorises f, rw ← assoc, rw ← assoc, rw ← assoc, rw ← assoc,
  congr' 2, rw factorises, apply coequalizer.condition
end

lemma image_map_comm_left {A' B' : C} {f' : A' ⟶ B'} {l : A ⟶ A'} {r : B ⟶ B'} (h : l ≫ f' = f ≫ r) :
  epi_part f ≫ image_map h = l ≫ epi_part f' :=
colimit.ι_desc _ _

lemma image_map_comm_right {A' B' : C} {f' : A' ⟶ B'} {l : A ⟶ A'} {r : B ⟶ B'} (h : l ≫ f' = f ≫ r) :
  image_map h ≫ mono_part f' = mono_part f ≫ r :=
begin
  rw ← cancel_epi (epi_part f),
  rw ← assoc, rw image_map_comm_left, rw assoc, rw factorises, rw h, rw ← assoc, rw factorises
end

-- lemma cofork.of_π_app_zero {X Y : C} {f g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
--   (cofork.of_π π w).ι.app walking_parallel_pair.zero = f ≫ π := rfl
-- lemma cofork.of_π_app_one {X Y : C} {f g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
--   (cofork.of_π π w).ι.app walking_parallel_pair.one = π := rfl

lemma coequalizer.hom_ext {X Y P : C} {f g : X ⟶ Y} {h k : coequalizer f g ⟶ P}
  (hyp : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) :
h = k :=
begin
  apply colimit.hom_ext, intro j, cases j,
  rw ← colimit.w (parallel_pair f g) walking_parallel_pair_hom.left, rw assoc, rw assoc, congr' 1,
  rw hyp, rw hyp
end

lemma image_map_uniq {A' B' : C} {f' : A' ⟶ B'} {l : A ⟶ A'} {r : B ⟶ B'} (h : l ≫ f' = f ≫ r) (k : image f ⟶ image f') :
  epi_part f ≫ k = l ≫ epi_part f' → k ≫ mono_part f' = mono_part f ≫ r → k = image_map h :=
begin
  intros, refine coequalizer.hom_ext _,
  erw a, erw image_map_comm_left
end

-- Image is a functor from the "arrow" category
def image.functor : comma (𝟭 C) (𝟭 C) ⥤ C :=
{ obj := λ f, image f.hom,
  map := λ f g k, image_map k.w,
  map_id' := λ f, begin symmetry, apply image_map_uniq, erw [id_comp, comp_id], erw [id_comp, comp_id] end,
  map_comp' := λ f g h α β,
    begin
      symmetry,
      apply image_map_uniq,
      rw [← assoc, image_map_comm_left, assoc, image_map_comm_left, ← assoc], refl,
      rw [assoc, image_map_comm_right, ← assoc, image_map_comm_right, assoc], refl
    end
}

def image_is_smallest_subobject {I : C} {q : A ⟶ I} {m : I ⟶ B} (hm : mono m) (h : q ≫ m = f) :
  image f ⟶ I :=
begin
  apply coequalizer.desc q, rw ← cancel_mono m, simp [h], rw pullback.condition
end

lemma smallest_subobject_factors {I : C} {q : A ⟶ I} {m : I ⟶ B} (hm : mono m) (h : q ≫ m = f) :
  image_is_smallest_subobject hm h ≫ m = mono_part f :=
begin
  rw ← cancel_epi (epi_part f),
  rw factorises, rw ← assoc, erw colimit.ι_desc,
  exact h
end
end category_theory
