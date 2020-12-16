import category_theory.comma
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.epi_mono
import category_theory.limits.over
import category_theory.closed.cartesian
import category.binary_products
import category.adjunction

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
noncomputable theory
namespace category_theory
open category limits

universes v u
variables {C : Type u} [category.{v} C]

-- def has_finite_products_of_has_finite_limits [has_finite_limits.{v} C] : has_finite_products.{v} C :=
-- λ _ _ _, by resetI; apply_instance
def has_finite_coproducts_of_has_finite_colimits [has_finite_colimits.{v} C] : has_finite_coproducts.{v} C :=
λ _ _ _, by resetI; apply_instance

@[simps]
def over_iso {B : C} {f g : over B} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom) : f ≅ g :=
{ hom := over.hom_mk hl.hom, inv := over.hom_mk hl.inv (by simp [iso.inv_comp_eq, hw]) }

section adjunction

variable (B : C)

section

variable [has_pullbacks.{v} C]

@[simps]
def real_pullback {A B : C} (f : A ⟶ B) : over B ⥤ over A :=
{ obj := λ g, over.mk (pullback.snd : pullback g.hom f ⟶ A),
  map := λ g h k, over.hom_mk (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition])) (by tidy) }

end

section
variable [has_binary_products.{v} C]

@[simps]
def star : C ⥤ over B :=
{ obj := λ A, over.mk (limits.prod.fst : B ⨯ A ⟶ B),
  map := λ X Y f, over.hom_mk (limits.prod.map (𝟙 _) f),
  map_id' := λ X,
  begin
    apply over.over_morphism.ext,
    dsimp,
    simp,
  end,
  map_comp' := λ X Y Z f g,
  begin
    apply over.over_morphism.ext,
    dsimp,
    ext,
    { rw [limits.prod.map_fst, comp_id, assoc, limits.prod.map_fst, comp_id, limits.prod.map_fst,
          comp_id] },
    { rw [limits.prod.map_snd, assoc, limits.prod.map_snd, limits.prod.map_snd_assoc] }
  end }

local attribute [tidy] tactic.case_bash

def forget_adj_star : over.forget B ⊣ star B :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g A,
  { to_fun := λ f, over.hom_mk (prod.lift g.hom f),
    inv_fun := λ k, k.left ≫ limits.prod.snd,
    left_inv := λ f, prod.lift_snd _ _,
    right_inv := λ k,
    begin
      ext;
      dsimp,
      rw prod.lift_fst,
      rw ← over.w k,
      refl,
      rw prod.lift_snd,
    end },
  hom_equiv_naturality_right' := λ X Y Y' f g,
  begin
    dsimp,
    ext1,
    dsimp,
    rw prod.lift_map,
    rw comp_id,
  end,
  hom_equiv_naturality_left_symm' := λ X' X Y f g, begin dsimp, rw assoc end }
end

def exponentiable_of_star_is_left_adj [has_finite_products C] (h : is_left_adjoint (star B)) :
  exponentiable B :=
{ is_adj :=
  { right := star B ⋙ h.right,
    adj := adjunction.comp _ _ h.adj (forget_adj_star B) } }

def dependent_sum {A B : C} (f : A ⟶ B) : over A ⥤ over B :=
(over.iterated_slice_equiv (over.mk f)).inverse ⋙ over.forget _

/--
`over.map f` gives nice definitional equalities but `dependent_sum` makes it easy to prove
adjunction properties
-/
def over_map_iso_dependent_sum {A B : C} (f : A ⟶ B) : dependent_sum f ≅ over.map f :=
begin
  refine nat_iso.of_components (λ X, over_iso (iso.refl _) (id_comp _)) (λ X Y g, _),
  { ext1,
    change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left,
    rw [comp_id, id_comp] }
end

def over_map_id {A : C} : over.map (𝟙 A) ≅ 𝟭 _ :=
nat_iso.of_components (λ X, over_iso (iso.refl _) (begin dsimp, simp end)) (λ X Y f, begin ext, dsimp, simp end)

def over_map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : over.map (f ≫ g) ≅ over.map f ⋙ over.map g :=
nat_iso.of_components (λ X, over_iso (iso.refl _) (begin dsimp, simp end)) (λ X Y f, begin ext, dsimp, simp end)

-- local attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits

def pullback_along {A B : C} (f : A ⟶ B) [has_binary_products (over B)] : over B ⥤ over A :=
star (over.mk f) ⋙ (over.iterated_slice_equiv _).functor

lemma jointly_mono {A B : C} [has_binary_products (over B)] {f g : over B} (t₁ t₂ : A ⟶ (g ⨯ f).left) :
  t₁ ≫ (limits.prod.fst : g ⨯ f ⟶ _).left = t₂ ≫ (limits.prod.fst : g ⨯ f ⟶ _).left →
  t₁ ≫ (limits.prod.snd : g ⨯ f ⟶ _).left = t₂ ≫ (limits.prod.snd : g ⨯ f ⟶ _).left →
  t₁ = t₂ :=
begin
  intros h₁ h₂,
  let A' : over B := over.mk (t₂ ≫ (g ⨯ f).hom), -- usually easier in practice to use the second one
  have : t₁ ≫ (g ⨯ f).hom = t₂ ≫ (g ⨯ f).hom,
    rw [← over.w (limits.prod.fst : g ⨯ f ⟶ _), reassoc_of h₁],
  let t₁' : A' ⟶ g ⨯ f := over.hom_mk t₁ this,
  let t₂' : A' ⟶ g ⨯ f := over.hom_mk t₂,
  suffices : t₁' = t₂',
    apply congr_arg comma_morphism.left this,
  apply prod.hom_ext;
  { ext1, assumption }
end

def iso_pb {A B : C} (f : A ⟶ B) [has_binary_products (over B)] [has_pullbacks C] :
  pullback_along f ≅ real_pullback f :=
begin
  refine nat_iso.of_components _ _,
  { intro X,
    let p : over B := over.mk (pullback.snd ≫ f : pullback X.hom f ⟶ B),
    let q : p ⟶ over.mk f ⨯ X := prod.lift (over.hom_mk pullback.snd rfl) (over.hom_mk pullback.fst pullback.condition),
    apply over_iso _ _,
    refine ⟨pullback.lift _ _ _, q.left, _, _⟩,
    { apply (limits.prod.snd : over.mk f ⨯ X ⟶ _).left },
    { apply (limits.prod.fst : over.mk f ⨯ X ⟶ _).left },
    { rw [over.w limits.prod.snd, ← over.w limits.prod.fst, over.mk_hom] },
    { apply jointly_mono;
      simp [← over.comp_left] },
    { apply pullback.hom_ext;
      simp [← over.comp_left] },
    { apply pullback.lift_snd } },
  { intros X Y g,
    ext1,
    dsimp [pullback_along],
    apply pullback.hom_ext,
    { simp only [assoc, pullback.lift_fst, ← over.comp_left, limits.prod.map_snd, pullback.lift_fst_assoc] },
    { simp only [assoc, pullback.lift_snd, ← over.comp_left, limits.prod.map_fst, comp_id] } },
end

section
-- local attribute [instance] over.construct_products.over_binary_product_of_pullback
def radj {A B : C} (f : A ⟶ B) [has_pullbacks C] :
  over.map f ⊣ real_pullback f :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g h,
  { to_fun := λ X, over.hom_mk (pullback.lift X.left g.hom (over.w X)) (pullback.lift_snd _ _ _),
    inv_fun := λ Y,
    begin
      refine over.hom_mk _ _,
      refine Y.left ≫ pullback.fst,
      dsimp,
      rw [← over.w Y, assoc, pullback.condition, assoc], refl,
    end,
    left_inv := by tidy,
    right_inv := λ Y, by { ext, dsimp, simp, dsimp, rw [pullback.lift_snd, ← over.w Y], refl } } }
-- (((over.mk f).iterated_slice_equiv.symm.to_adjunction.comp _ _ (forget_adj_star _)).of_nat_iso_left (over_map_iso_dependent_sum f)).of_nat_iso_right (iso_pb f)

def pullback_id {A : C} [has_pullbacks C] : real_pullback (𝟙 A) ≅ 𝟭 _ :=
adjunction.right_adjoint_uniq (radj _) (adjunction.id.of_nat_iso_left over_map_id.symm)

def pullback_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [has_pullbacks C] :
  real_pullback (f ≫ g) ≅ real_pullback g ⋙ real_pullback f :=
adjunction.right_adjoint_uniq (radj _) (((radj _).comp _ _ (radj _)).of_nat_iso_left (over_map_comp _ _).symm)

instance thing {A B : C} (f : A ⟶ B) [has_pullbacks C] : is_right_adjoint (real_pullback f) :=
⟨_, radj f⟩
end

variables [has_finite_products.{v} C] [has_pullbacks.{v} C]

def Pi_obj [exponentiable B] (f : over B) : C := pullback ((exp B).map f.hom) (internalize_hom (𝟙 B))

@[simps]
private def pi_obj.equiv [exponentiable B] (X : C) (Y : over B) :
  ((star B).obj X ⟶ Y) ≃ (X ⟶ Pi_obj B Y) :=
{ to_fun := λ f, pullback.lift (cartesian_closed.curry f.left) (terminal.from _)
    (by { rw [internalize_hom, comp_id, ← curry_natural_left, ← curry_natural_right,
              limits.prod.map_fst, comp_id, over.w f], refl }),
  inv_fun := λ g,
    begin
      apply over.hom_mk _ _,
      { apply (cartesian_closed.uncurry (g ≫ pullback.fst)) },
      { rw [← uncurry_natural_right, assoc, pullback.condition, ← assoc, uncurry_natural_left],
        dsimp [internalize_hom],
        rw [uncurry_curry, limits.prod.map_fst_assoc, comp_id, comp_id] }
    end,
  left_inv := λ f, by { ext1, simp },
  right_inv := λ g,
  by { ext1, { simp }, { apply subsingleton.elim } } }

private lemma pi_obj.natural_equiv [exponentiable B] (X' X : C) (Y : over B) (f : X' ⟶ X) (g : (star B).obj X ⟶ Y) :
  (pi_obj.equiv B X' Y).to_fun ((star B).map f ≫ g) = f ≫ (pi_obj.equiv B X Y).to_fun g :=
begin
  apply pullback.hom_ext,
  { simp [curry_natural_left] },
  { apply subsingleton.elim }
end

def Pi_functor [exponentiable B] : over B ⥤ C :=
  adjunction.right_adjoint_of_equiv (pi_obj.equiv B) (pi_obj.natural_equiv B)
def star_adj_pi_of_exponentiable [exponentiable B] : star B ⊣ Pi_functor B :=
  adjunction.adjunction_of_equiv_right _ _
instance star_is_left_adj_of_exponentiable [exponentiable B] : is_left_adjoint (star B) :=
  ⟨Pi_functor B, star_adj_pi_of_exponentiable B⟩

end adjunction

end category_theory
