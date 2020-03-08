import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.epi_mono
import cartesian_closed
import pullbacks
import comma
import to_mathlib

/-!
# Properties of the over category.

We can interpret the forgetful functor `forget : over B ⥤ C` as dependent sum,
(written `Σ_B`)
and when C has binary products, it has a right adjoint `B*` given by
`A ↦ (π₁ : B × A → B)`, denoted `star` in Lean.

Furthermore, if the original category C has pullbacks and terminal object (i.e.
all finite limits), `B*` has a right adjoint iff `B` is exponentiable in `C`.
This right adjoint is written `Π_B` and is interpreted as dependent product.

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
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section adjunction

variable (B : C)
variable [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

@[reducible]
def star : C ⥤ over B :=
{ obj := λ A, @over.mk _ _ _ (B ⨯ A) limits.prod.fst,
  map := λ X Y f, over.hom_mk (limits.prod.map (𝟙 _) f) (by simp) }

def forget_adj_star : over.forget ⊣ star B :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g A,
  { to_fun := λ f, over.hom_mk (prod.lift g.hom f),
    inv_fun := λ k, k.left ≫ limits.prod.snd,
    left_inv := by tidy,
    right_inv := by tidy } }

variables [has_terminal.{v} C] [has_pullbacks.{v} C]

def Pi_obj [exponentiable B] (f : over B) : C := pullback (post B f.hom) (point_at_hom (𝟙 B))

private def pi_obj.equiv [exponentiable B] (X : C) (Y : over B) :
  ((star B).obj X ⟶ Y) ≃ (X ⟶ Pi_obj B Y) :=
{ to_fun := λ f, pullback.lift (exp_transpose.to_fun f.left) (terminal.from _)
    (begin rw ← exp_transpose_natural_right, erw ← exp_transpose_natural_left, tidy end),
  inv_fun := λ g,
    begin
      apply over.hom_mk _ _, apply (exp_transpose.inv_fun (g ≫ pullback.fst)),
      dsimp, apply function.injective_of_left_inverse exp_transpose.left_inv,
      rw exp_transpose_natural_right, rw exp_transpose.right_inv, rw assoc,
      rw pullback.condition, have : g ≫ pullback.snd = terminal.from X,
      apply subsingleton.elim, rw ← assoc, rw this, erw ← exp_transpose_natural_left,
      apply function.injective_of_left_inverse exp_transpose.right_inv,
      rw exp_transpose.left_inv, rw exp_transpose.left_inv, simp
    end,
  left_inv := λ f, begin apply over.over_morphism.ext, simp, rw exp_transpose.left_inv end,
  right_inv := λ g, begin apply pullback.hom_ext, simp, rw exp_transpose.right_inv, apply subsingleton.elim end
  }

private lemma pi_obj.natural_equiv [exponentiable B] (X' X : C) (Y : over B) (f : X' ⟶ X) (g : (star B).obj X ⟶ Y) :
  (pi_obj.equiv B X' Y).to_fun ((star B).map f ≫ g) = f ≫ (pi_obj.equiv B X Y).to_fun g :=
begin
  apply pullback.hom_ext, simp [pi_obj.equiv], rw ← exp_transpose_natural_left, refl,
  apply subsingleton.elim
end

def Pi_functor [exponentiable B] : over B ⥤ C := @adjunction.right_adjoint_of_equiv _ _ _ _ (star B) (Pi_obj B) (pi_obj.equiv B) (pi_obj.natural_equiv B)
def star_adj_pi_of_exponentiable [exponentiable B] : star B ⊣ Pi_functor B := adjunction.adjunction_of_equiv_right _ _
def star_is_left_adj_of_exponentiable [exponentiable B] : is_left_adjoint (star B) := ⟨Pi_functor B, star_adj_pi_of_exponentiable B⟩

def exponentiable_of_star_is_left_adj (h : is_left_adjoint (star B)) : exponentiable B :=
⟨⟨star B ⋙ h.right, adjunction.comp _ _ h.adj (forget_adj_star B)⟩⟩

end adjunction

section over_limits

def over_product_of_pullbacks (B : C) (F : discrete walking_pair ⥤ over B)
[q : has_limit (cospan (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom)]
: has_limit F :=
{ cone := begin
            refine ⟨_, _⟩,
            exact @over.mk _ _ B (pullback (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom) (pullback.fst ≫ (F.obj walking_pair.left).hom),
            apply nat_trans.of_homs, intro i, cases i,
            apply over.hom_mk _ _, apply pullback.fst, dsimp, refl,
            apply over.hom_mk _ _, apply pullback.snd, exact pullback.condition.symm
          end,
  is_limit :=
  { lift :=
      begin
        intro s, apply over.hom_mk _ _,
          apply pullback.lift _ _ _,
              exact (s.π.app walking_pair.left).left,
            exact (s.π.app walking_pair.right).left,
          erw over.w (s.π.app walking_pair.left),
          erw over.w (s.π.app walking_pair.right),
          refl,
        dsimp, erw ← assoc, simp,
      end,
    fac' := begin intros s j, ext, cases j, simp [nat_trans.of_homs], simp [nat_trans.of_homs] end,
    uniq' := begin intros s m j,
    ext, revert j_1, apply pi_app,
    simp, erw ← j walking_pair.left, erw limit.lift_π, simp, refl,
    simp, erw ← j walking_pair.right, simp, erw limit.lift_π, simp, refl end } }

instance (B : C) : has_terminal.{v} (over B) :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone := { X := over.mk (𝟙 _), π := { app := λ p, pempty.elim p } },
      is_limit := { lift := λ s, over.hom_mk _,
                    fac' := λ _ j, j.elim,
                    uniq' := λ s m _,
                    begin ext, rw over.hom_mk_left, have := m.w, dsimp at this, simp at this, assumption end } } } }

instance {B : C} [has_pullbacks.{v} C] : has_pullbacks.{v} (over B) :=
begin
    refine ⟨⟨λ F, _⟩⟩,
    let X : over B := F.obj walking_cospan.one,
    let Y : over B := F.obj walking_cospan.left,
    let Z : over B := F.obj walking_cospan.right,
    let f : Y ⟶ X := (F.map walking_cospan.hom.inl),
    let g : Z ⟶ X := (F.map walking_cospan.hom.inr),
    -- let L := pullback f.left g.left,
    let L : over B := over.mk (pullback.fst ≫ Y.hom : pullback f.left g.left ⟶ B),
    let π₁ : L ⟶ Y := over.hom_mk pullback.fst,
    let π₂ : L ⟶ Z, refine @over.hom_mk _ _ _ L Z (pullback.snd : L.left ⟶ Z.left) _,
      simp,
      rw [← over.w f, ← assoc,  pullback.condition, assoc,  over.w g],
    refine {cone := cone.of_pullback_cone (pullback_cone.mk π₁ π₂ _), is_limit := {lift := _, fac' := _, uniq' := _}},
      ext, simp, erw pullback.condition,
    intro s,
    -- let ss := pullback_cone.of_cone s,
    apply over.hom_mk _ _,
    apply pullback.lift (s.π.app walking_cospan.left).left (s.π.app walking_cospan.right).left,
    rw ← over.comp_left, rw ← over.comp_left,
    rw s.w, rw s.w, simp,
    show pullback.lift (((s.π).app walking_cospan.left).left) (((s.π).app walking_cospan.right).left) _ ≫
      (pullback.fst ≫ Y.hom : pullback f.left g.left ⟶ B) = (s.X).hom, simp, refl,
    intros s j, simp, ext1, dsimp,
    cases j, simp, simp, simp,
    show _ ≫ (((pullback_cone.mk π₁ π₂ _).π).app walking_cospan.one).left = ((s.π).app walking_cospan.one).left,
    dunfold pullback_cone.mk, dsimp,
    show pullback.lift (((s.π).app walking_cospan.left).left) (((s.π).app walking_cospan.right).left) _ ≫
      pullback.fst ≫ f.left =
    ((s.π).app walking_cospan.one).left, simp, rw ← over.comp_left, rw ← s.w walking_cospan.hom.inl,
    intros s m J, apply over.over_morphism.ext, simp, apply pullback.hom_ext,
    simp at J, dsimp at J,
    have := J walking_cospan.left, dsimp at this, simp, rw ← this, simp,
    have := J walking_cospan.right, dsimp at this, simp, rw ← this, simp
end

instance over_has_prods_of_pullback [has_pullbacks.{v} C] (B : C) :
  has_binary_products.{v} (over B) :=
{has_limits_of_shape := {has_limit := λ F, over_product_of_pullbacks B F}}

@[simp]
lemma over_prod_is_pullback [has_pullbacks.{v} C] {B : C} (F : discrete walking_pair ⥤ over B) :
  limits.limit F = @over.mk _ _ B (pullback (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom) (pullback.fst ≫ (F.obj walking_pair.left).hom) := rfl

@[simp]
lemma over_prod_left [has_pullbacks.{v} C] {B : C} (F : discrete walking_pair ⥤ over B) :
  (limits.limit F).left = (pullback (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom) := rfl

@[simp]
lemma over_prod_pair_left [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (prod f g).left = pullback f.hom g.hom := rfl

@[simp]
lemma over_prod_pair_hom [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (prod f g).hom = pullback.fst ≫ f.hom := rfl

@[simp]
lemma over_prod_pair [has_pullbacks.{v} C] {B : C} (f g : over B) :
  prod f g = @over.mk _ _ B (pullback f.hom g.hom) (pullback.fst ≫ f.hom) := rfl

@[simp]
lemma over_prod_fst [has_pullbacks.{v} C] {B : C} (f g : over B) :
  limits.prod.fst = (over.hom_mk pullback.fst : prod f g ⟶ f) := rfl

@[simp]
lemma over_prod_snd [has_pullbacks.{v} C] {B : C} (f g : over B) :
  limits.prod.snd = (over.hom_mk pullback.snd pullback.condition.symm : prod f g ⟶ g) := rfl

@[simp]
lemma over_prod_map [has_pullbacks.{v} C] {B : C} (f g h : over B) (k : g ⟶ h) :
  (limits.prod.map (𝟙 f) k : f ⨯ g ⟶ f ⨯ h) = over.hom_mk (pullback.lift pullback.fst (pullback.snd ≫ k.left) (by dsimp; simp; apply pullback.condition)) (begin tidy end) :=
begin
  tidy, cases j, tidy
end

end over_limits

variable (C)
class is_locally_cartesian_closed extends has_pullbacks.{v} C :=
(overs_cc : Π (B : C), is_cartesian_closed (over B))

instance cartesian_closed_over_of_lcc [has_binary_products.{v} C] [is_locally_cartesian_closed.{v} C] {B : C} :
  is_cartesian_closed (over B) := @is_locally_cartesian_closed.overs_cc _ 𝒞 _ B

variable {C}
@[reducible]
def iterated_slice_forward {B : C} (f : over B) : over f ⥤ over f.left :=
{ obj := λ α, over.mk α.hom.left,
  map := λ α β κ, over.hom_mk κ.left.left (begin rw auto_param_eq, rw ← over.w κ, refl end)}

@[reducible]
def iterated_slice_backward {B : C} (f : over B) : over f.left ⥤ over f :=
{ obj := λ g, over.mk (over.hom_mk g.hom (by simp) : over.mk (g.hom ≫ f.hom) ⟶ _),
  map := λ g h α, @over.hom_mk _ _ f
              (over.mk (@over.hom_mk C 𝒞 B (over.mk (g.hom ≫ f.hom)) f g.hom (by simp) : _ ⟶ f))
              (over.mk (@over.hom_mk C 𝒞 B (over.mk (h.hom ≫ f.hom)) f h.hom (by simp) : _ ⟶ f))
              (over.hom_mk α.left (over.w_assoc α f.hom)) (over.over_morphism.ext (over.w α)) }

def iterated_slice_equiv {B : C} (f : over B) : over f ≌ over f.left :=
equivalence.mk (iterated_slice_forward f) (iterated_slice_backward f)
(nat_iso.of_components
  (λ g, ⟨over.hom_mk (over.hom_mk (𝟙 g.left.left)) (by apply_auto_param),
         over.hom_mk (over.hom_mk (𝟙 g.left.left)) (by apply_auto_param),
         by ext; dsimp; simp, by ext; dsimp; simp⟩) (λ X Y g, by ext; dsimp; simp))
(nat_iso.of_components
  (λ g, ⟨over.hom_mk (𝟙 g.left) (by apply_auto_param),
         over.hom_mk (𝟙 g.left) (by apply_auto_param),
         by ext; dsimp; simp, by ext; dsimp; simp⟩) (λ X Y g, by ext; dsimp; simp))

universe u₂

lemma equiv_reflects_mono {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.functor.map f)) : mono f :=
faithful_reflects_mono e.functor hef

lemma equiv_reflects_mono' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D)
  (hef : mono (e.inverse.map f)) : mono f :=
faithful_reflects_mono e.inverse hef

lemma equiv_reflects_epi {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D)
  (hef : epi (e.functor.map f)) : epi f :=
faithful_reflects_epi e.functor hef

lemma equiv_reflects_epi' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D)
  (hef : epi (e.inverse.map f)) : epi f :=
faithful_reflects_epi e.inverse hef

lemma equiv_preserves_mono {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D) :
  mono f → mono (e.functor.map f) :=
begin
  intro hf, apply equiv_reflects_mono ((e.functor).map f) e.symm,
  erw equivalence.inv_fun_map,
  apply mono_comp_of_mono,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso_inverse,
  apply mono_comp_of_mono _ _ hf,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso,
end

lemma equiv_preserves_mono' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D) :
  mono f → mono (e.inverse.map f) :=
begin
  intro hf, apply equiv_reflects_mono' (e.inverse.map f) e.symm,
  erw equivalence.fun_inv_map,
  apply mono_comp_of_mono,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso,
  apply mono_comp_of_mono _ _ hf,
  apply @is_iso.mono_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso_inverse,
end

lemma equiv_preserves_epi {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D) :
  epi f → epi (e.functor.map f) :=
begin
  intro hf, apply equiv_reflects_epi ((e.functor).map f) e.symm,
  erw equivalence.inv_fun_map,
  apply epi_comp_of_epi,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso_inverse,
  apply epi_comp_of_epi _ _ hf,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso,
end

lemma equiv_preserves_epi' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D) :
  epi f → epi (e.inverse.map f) :=
begin
  intro hf, apply equiv_reflects_epi' (e.inverse.map f) e.symm,
  erw equivalence.fun_inv_map,
  apply epi_comp_of_epi,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso,
  apply epi_comp_of_epi _ _ hf,
  apply @is_iso.epi_of_iso _ _ _ _ _ (nat_iso.is_iso_app_of_is_iso _ _), apply is_iso.of_iso_inverse,
end

lemma equiv_mono_iff {D : Type u₂} [category.{v} D] {X Y : C} (f : X ⟶ Y) (e : C ≌ D) :
  mono f ↔ mono (e.functor.map f) :=
⟨equiv_preserves_mono f e, equiv_reflects_mono f e⟩

lemma equiv_epi_iff {D : Type u₂} [category.{v} D] (X Y : C) (f : X ⟶ Y) (e : C ≌ D) :
  epi f ↔ epi (e.functor.map f) :=
⟨equiv_preserves_epi f e, equiv_reflects_epi f e⟩

lemma equiv_mono_iff' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D) :
  mono f ↔ mono (e.inverse.map f) :=
⟨equiv_preserves_mono' f e, equiv_reflects_mono' f e⟩

lemma equiv_epi_iff' {D : Type u₂} [category.{v} D] {X Y : D} (f : X ⟶ Y) (e : C ≌ D) :
  epi f ↔ epi (e.inverse.map f) :=
⟨equiv_preserves_epi' f e, equiv_reflects_epi' f e⟩

lemma over_epi {B : C} {f g : over B} {k : f ⟶ g} (ke : epi k.left) : epi k :=
begin
  split, intros h l m a, ext, rw [← cancel_epi k.left, ← over.comp_left, a], refl
end
lemma over_epi' [has_binary_products.{v} C] (B : C) (f g : over B) (k : f ⟶ g) (ke : epi k) : epi k.left :=
left_adjoint_preserves_epi (forget_adj_star _) ke

lemma over_epi'' [has_binary_products.{v} C] (B : C) (f g : over B) (k : f ⟶ g) : epi k ↔ epi k.left :=
⟨over_epi' _ _ _ _, over_epi⟩

-- variable (C)

@[reducible]
def pullback_along [has_pullbacks.{v} C] {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
star (over.mk f) ⋙ (iterated_slice_equiv _).functor

def over_iso {B : C} (f g : over B) (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) : (f ≅ g) :=
{ hom := over.hom_mk hl.hom, inv := over.hom_mk hl.inv (by simp [iso.inv_comp_eq, hw]) }

def over_left_iso {B : C} {f g : over B} (hf : f ≅ g) : f.left ≅ g.left :=
{ hom := hf.hom.left, inv := hf.inv.left, hom_inv_id' := begin rw [← over.comp_left, hf.hom_inv_id], refl end, inv_hom_id' := begin rw [← over.comp_left, hf.inv_hom_id], refl end}

set_option pp.all false
lemma pullback_along_obj_of_id [has_pullbacks.{v} C] {A B : C} (f : A ⟶ B) : (pullback_along f).obj (over.mk (𝟙 B)) ≅ over.mk (𝟙 A) :=
begin
  apply over_iso, swap,
  have: over.mk f⨯⊤_ over B ≅ over.mk f, apply prod.right_unitor,
  apply over_left_iso this,
  dunfold over_left_iso iterated_slice_equiv pullback_along equivalence.mk, simp, dsimp, simp,
end

lemma pullback_of_obj [has_pullbacks.{v} C] {A B D : C} (f : A ⟶ B) (g : D ⟶ B) :
  ((pullback_along f).map (terminal.from (over.mk g))).left = (pullback.fst : pullback f g ⟶ A) ≫ (pullback.with_id_l f).inv :=
begin
  dsimp [pullback_along, iterated_slice_equiv, equivalence.mk, pullback.with_id_l, pullback.with_id_r, identify_limit_apex, iso_apex_of_iso_cone, pullback.with_id_r', pullback.flip', flip_limit_cone, cospan_cone.flip, is_limit.unique_up_to_iso, is_limit.lift_cone_morphism],
  simp, ext, cases j, simp, dsimp, erw limit.lift_π, simp, dunfold pullback_cone.snd, dsimp, simp, dsimp, simp,
  erw limit.lift_π, simp, dunfold pullback_cone.fst, simp, symmetry, exact pullback.condition,
  simp, erw ← @limit.w walking_cospan _ _ _ _ _ _ _ walking_cospan.hom.inl, simp, dsimp, dunfold pullback_cone.mk, simp, dsimp,
  rw ← assoc, rw ← assoc, rw ← assoc, congr' 1, simp, erw limit.lift_π, simp, dunfold pullback_cone.snd, dsimp, simp
end

variables [is_locally_cartesian_closed.{v} C]

lemma thing {A B : C} (f : A ⟶ B) : is_left_adjoint (pullback_along f) :=
{ right := _ ⋙ _, adj := adjunction.comp _ _ (@star_adj_pi_of_exponentiable (over B) _ (over.mk f) _ _ _ (@is_cartesian_closed.cart_closed _ _ _ _ (is_locally_cartesian_closed.overs_cc B) _)) (equivalence.to_adjunction _) }

variables [has_binary_products.{v} C]
/--
 P ⟶ A
 ↓   ↓
 D ↠ B
If g : D ⟶ B is epi then the pullback of g along f is epi
-/
theorem pullback_preserves_epi {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} (hg : epi g) :
  epi (pullback.fst : pullback f g ⟶ A) :=
begin
  set g' : over.mk g ⟶ ⊤_ over B := terminal.from (over.mk g),
  have: epi g' := over_epi hg,
  have q: epi ((pullback_along f).map g'),
    apply left_adjoint_preserves_epi, apply (thing f).adj, assumption,
  rw over_epi'' at q,
  erw pullback_of_obj f g at q,
  have: (pullback.fst : pullback f g ⟶ A) ≫ (pullback.with_id_l f).inv ≫ (pullback.with_id_l f).hom = (pullback.fst : pullback f g ⟶ A),
    simp,
  rw ← this, rw ← assoc, apply epi_comp_of_epi, assumption, apply is_iso.epi_of_iso
end

lemma pullback_preserves_epi' {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} (hg : epi g) :
epi (pullback.snd : pullback g f ⟶ A) :=
begin
  have: (pullback.snd : pullback g f ⟶ A) = (pullback.flip' _ _).hom ≫ (pullback.fst : pullback f g ⟶ A), -- TODO: this should be a lemma
    dunfold pullback.flip' iso_apex_of_iso_cone flip_limit_cone flip_hom flip_twice, dsimp, erw id_comp, simp, refl,
  rw this, apply epi_comp_of_epi, apply is_iso.epi_of_iso,
  apply pullback_preserves_epi _ hg
end
lemma pullback_preserves_epi'' {A B D : C}
  (f : A ⟶ B) {g : D ⟶ B} (hg : epi g) {c : pullback_cone g f} (t : is_limit c) :
epi (pullback_cone.snd c) :=
begin
  have y := is_limit.unique_up_to_iso t (limit.is_limit _),
  have z: pullback_cone.snd c = y.hom.hom ≫ pullback_cone.snd (limit.cone (cospan g f)),
    rw y.hom.w,
  rw z, apply epi_comp_of_epi,
    apply @is_iso.epi_of_iso _ _ _ _ _ _, refine ⟨_, _, _⟩, apply y.inv.hom,
    show ((y.hom ≫ y.inv).hom = 𝟙 c.X), rw y.hom_inv_id, refl,
    show ((y.inv ≫ y.hom).hom = 𝟙 _), rw y.inv_hom_id, refl,
  exact pullback_preserves_epi' f hg
end

variables [has_coequalizers.{v} C] {A B : C} (f : A ⟶ B)

def image : C := coequalizer (pullback.fst : pullback f f ⟶ A) (pullback.snd : pullback f f ⟶ A)
def epi_part : A ⟶ image f := coequalizer.π pullback.fst pullback.snd
def mono_part : image f ⟶ B := coequalizer.desc _ _ f pullback.condition

lemma factorises : epi_part f ≫ mono_part f = f :=
begin
  simp [epi_part, mono_part], refl,
end
lemma coequalizer_epi (g h : A ⟶ B) : epi (coequalizer.π g h) :=
begin
  split, intros k l m q, apply colimit.hom_ext, intro, cases j,
  rw ← colimit.w (parallel_pair _ _) walking_parallel_pair_hom.left, rw assoc, rw q, simp,
  exact q,
end
lemma epi_part_is_epi : epi (epi_part f) := coequalizer_epi _ _

lemma prod_map_epi (D : C) {q : A ⟶ B} (hq : epi q) : epi (limits.prod.map q (𝟙 D)) :=
pullback_preserves_epi'' _ hq (pullback_prod _ _)

lemma prod_map_epi' (D : C) {q : A ⟶ B} (hq : epi q) : epi (limits.prod.map (𝟙 D) q) :=
pullback_preserves_epi'' _ hq (pullback_prod' q D)

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
    rw [assoc, assoc, lift_fst, map_fst, ← assoc] at this, exact this,
  have lqnh: l ≫ q = n ≫ h,
    have: (kl ≫ limits.prod.map q q) ≫ limits.prod.snd = (n ≫ limits.prod.lift g h) ≫ limits.prod.snd, rw pullback.condition,
    rw [assoc, assoc, lift_snd, map_snd, ← assoc] at this, exact this,
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
  have: limits.prod.map q q = limits.prod.map (𝟙 _) q ≫ limits.prod.map q (𝟙 _),
    apply prod.hom_ext, simp, dsimp, simp, simp,
  rw this, apply epi_comp_of_epi, apply prod_map_epi' A (epi_part_is_epi f),
  apply prod_map_epi _ (epi_part_is_epi f)
end

variable {f}
def image_map {A' B' : C} {f' : A' ⟶ B'} {l : A ⟶ A'} {r : B ⟶ B'} (h : l ≫ f' = f ≫ r) : image f ⟶ image f' :=
begin
  apply coequalizer.desc _ _ (l ≫ epi_part f'),
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
  haveI := epi_part_is_epi f,
  rw ← cancel_epi (epi_part f),
  rw ← assoc, rw image_map_comm_left, rw assoc, rw factorises, rw h, rw ← assoc, rw factorises
end

lemma cofork.of_π_app_zero {X Y : C} {f g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app walking_parallel_pair.zero = f ≫ π := rfl
lemma cofork.of_π_app_one {X Y : C} {f g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app walking_parallel_pair.one = π := rfl

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
  apply coequalizer.desc _ _ q, rw ← cancel_mono m, simp [h], rw pullback.condition
end

lemma smallest_subobject_factors {I : C} {q : A ⟶ I} {m : I ⟶ B} (hm : mono m) (h : q ≫ m = f) :
  image_is_smallest_subobject hm h ≫ m = mono_part f :=
begin
  haveI := epi_part_is_epi f,
  rw ← cancel_epi (epi_part f),
  rw factorises, rw ← assoc, erw colimit.ι_desc,
  exact h
end
end category_theory