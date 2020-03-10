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

Given `f : A ⟶ B` in `C/B`, the iterated slice `(C/B)/f` is isomorphic to
`C/A`.
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

-- TODO: See issue #27
instance {B : C} [has_pullbacks.{v} C] : has_pullbacks.{v} (over B) :=
begin
    refine ⟨⟨λ F, _⟩⟩,
    let X : over B := F.obj walking_cospan.one,
    let Y : over B := F.obj walking_cospan.left,
    let Z : over B := F.obj walking_cospan.right,
    let f : Y ⟶ X := (F.map walking_cospan.hom.inl),
    let g : Z ⟶ X := (F.map walking_cospan.hom.inr),
    let L : over B := over.mk (pullback.fst ≫ Y.hom : pullback f.left g.left ⟶ B),
    let π₁ : L ⟶ Y := over.hom_mk pullback.fst,
    let π₂ : L ⟶ Z, refine @over.hom_mk _ _ _ L Z (pullback.snd : L.left ⟶ Z.left) _,
      simp,
      rw [← over.w f, ← assoc,  pullback.condition, assoc,  over.w g],
    refine {cone := cone.of_pullback_cone (pullback_cone.mk π₁ π₂ _), is_limit := {lift := _, fac' := _, uniq' := _}},
      ext, simp, erw pullback.condition,
    intro s,
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

end category_theory