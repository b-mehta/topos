import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflects_isomorphisms
import category_theory.limits.shapes.constructions.preserve_binary_products
import category_theory.adjunction.fully_faithful
import category_theory.adjunction.limits
import category_theory.closed.cartesian
import cartesian_closed
import power

namespace category_theory

open category_theory category_theory.category category_theory.limits
open classifier

universes v u u₂

variables (C : Type u) [category.{v} C]

class topos :=
[lim : has_finite_limits.{v} C]
[sub : has_subobject_classifier.{v} C]
[cc : cartesian_closed.{v} C]

attribute [instance] topos.lim topos.sub topos.cc

variables [topos.{v} C]

variable {C}

lemma prod_iso_pb {B : C} (f : over B) : prod_functor.obj f = star f ⋙ over.forget := rfl

-- def pb_compose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : real_pullback g ⋙ real_pullback f ≅ real_pullback (f ≫ g) :=
-- begin
--   -- pullback_along g ⋙ pullback_along f ≅ pullback_along (f ⋙ g)
--   -- star (over.mk g) ⋙ (over.iterated_slice_equiv _).functor ⋙ star (over.mk f) ⋙ (over.iterated_slice_equiv _).functor ≅ star (over.mk (f ≫ g)) ⋙ (over.iterated_slice_equiv _).functor


--   -- star (over.mk g) ⋙ (over.iterated_slice_equiv _).functor ⋙ star (over.mk f) ⋙ (over.iterated_slice_equiv _).functor ⋙ over.forget ≅ star (over.mk (f ≫ g)) ⋙ (over.iterated_slice_equiv _).functor ⋙ over.forget
--   -- star (over.mk g) ⋙ (over.iterated_slice_equiv _).functor ⋙ star (over.mk f) ⋙ over.forget ⋙ over.forget ≅ star (over.mk (f ≫ g)) ⋙ over.forget ⋙ over.forget
--   -- star (over.mk g) ⋙ (over.iterated_slice_equiv _).functor ⋙ prod_functor.obj (over.mk f) ⋙ over.forget ≅ prod_functor.obj (f ≫ g) ⋙ over.forget
-- end

def prod_iso_pb' {B : C} (f : over B) : prod_functor.obj f ≅ real_pullback f.hom ⋙ dependent_sum f.hom :=
calc star f ⋙ over.forget ≅ star f ⋙ (over.iterated_slice_equiv _).functor ⋙ (over.iterated_slice_equiv f).inverse ⋙ over.forget :
            iso_whisker_left (star f) (iso_whisker_right f.iterated_slice_equiv.unit_iso over.forget)
     ... ≅ (star f ⋙ (over.iterated_slice_equiv _).functor) ⋙ ((over.iterated_slice_equiv f).inverse ⋙ over.forget) : iso.refl _
     ... ≅ (star f ⋙ (over.iterated_slice_equiv _).functor) ⋙ dependent_sum f.hom : iso.refl _
     ... ≅ real_pullback f.hom ⋙ dependent_sum f.hom :
      begin
        refine iso_whisker_right _ (dependent_sum f.hom),
        have : f = over.mk f.hom,
          cases f, congr, apply subsingleton.elim,
        convert iso_pb f.hom,
      end

def pullback_sum_iso {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W}
  {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk f g comm)) :
  real_pullback g ⋙ dependent_sum f ≅ dependent_sum k ⋙ real_pullback h :=
begin
  apply nat_iso.of_components _ _,
  { intro m,
    apply over_iso _ _,
    { refine ⟨_, _, _, _⟩,
      { apply pullback.lift pullback.fst (pullback.snd ≫ f) _,
        change pullback.fst ≫ _ ≫ k = _,
        simp only [pullback.condition_assoc, assoc, comm] },
      { apply pullback.lift pullback.fst _ _,
        refine (pullback_cone.is_limit.lift' t pullback.snd (pullback.fst ≫ m.hom) _).1,
        rw [← pullback.condition, assoc], refl,
        erw (pullback_cone.is_limit.lift' t pullback.snd (pullback.fst ≫ m.hom) _).2.2 },
      { apply pullback.hom_ext,
        { simp },
        { rw [assoc, id_comp, pullback.lift_snd],
          apply pullback_cone.is_limit.hom_ext t,
          { rw [assoc, (pullback_cone.is_limit.lift' t _ _ _).2.1, pullback.lift_snd], refl },
          { rw [assoc, (pullback_cone.is_limit.lift' t _ _ _).2.2, pullback.lift_fst_assoc,
                pullback.condition], refl } } },
      { apply pullback.hom_ext,
        { simp },
        { rw [id_comp, assoc, pullback.lift_snd, pullback.lift_snd_assoc],
          apply (pullback_cone.is_limit.lift' t _ _ _).2.1 } } },
    { apply pullback.lift_snd } },
  { intros,
    ext1,
    change pullback.lift _ _ _ ≫ pullback.lift _ _ _ = pullback.lift _ _ _ ≫ pullback.lift (pullback.fst ≫ f_1.left) _ _,
    ext1;
    simp }
end

def dependent_sum_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : dependent_sum (f ≫ g) ≅ (dependent_sum f : over _ ⥤ over _) ⋙ dependent_sum g :=
begin
  apply nat_iso.of_components _ _,
  intro h,
  refine over_iso (iso.refl _) _,
  dsimp [dependent_sum],
  simp,
  intros,
  ext1,
  dsimp [dependent_sum],
  simp,
end

def test' {A B : C} (f : over A) (k : B ⟶ A) :
  dependent_sum k ⋙ prod_functor.obj f ≅ prod_functor.obj ((real_pullback k).obj f) ⋙ dependent_sum k :=
calc dependent_sum k ⋙ prod_functor.obj f ≅ dependent_sum k ⋙ real_pullback f.hom ⋙ dependent_sum f.hom :
              iso_whisker_left (dependent_sum k) (prod_iso_pb' _)
     ... ≅ real_pullback pullback.snd ⋙ dependent_sum pullback.fst ⋙ dependent_sum f.hom :
              iso_whisker_right (pullback_sum_iso (cone_is_pullback _ _)).symm (dependent_sum f.hom)
     ... ≅ real_pullback pullback.snd ⋙ dependent_sum (_ ≫ f.hom) : iso_whisker_left (real_pullback _) (dependent_sum_comp _ _).symm
     ... ≅ real_pullback pullback.snd ⋙ dependent_sum (pullback.snd ≫ k) : iso_whisker_left (real_pullback _) (by rw pullback.condition)
     ... ≅ real_pullback ((real_pullback k).obj f).hom ⋙ dependent_sum pullback.snd ⋙ dependent_sum k : iso_whisker_left (real_pullback _) (dependent_sum_comp _ _)
     ... ≅ prod_functor.obj ((real_pullback k).obj f) ⋙ dependent_sum k : iso_whisker_right (prod_iso_pb' _).symm (dependent_sum k)

-- def test {A B : C} (f : over A) (k : B ⟶ A) :
--   exp f ⋙ real_pullback k ≅ real_pullback k ⋙ exp ((real_pullback k).obj f) :=
-- begin
--   apply right_adjoint_uniq,
--   apply adjunction.comp _ _ (radj k) (exp.adjunction _),
--   apply adjunction.of_nat_iso_left _ (test' f k).symm,
--   apply adjunction.comp _ _ (exp.adjunction _) (radj k),
-- end

/-- Pullback respects exponentials! (Natural in `g`) -/
-- def pullback_exp {X Y A B : C} (f g : over A) (k : B ⟶ A) :
--   (real_pullback k).obj (f ⟹ g) ≅ (real_pullback k).obj f ⟹ (real_pullback k).obj g :=
-- (test f k).app g

instance subq_cc (A : C) : cartesian_closed (subq A) :=
cartesian_closed_of_equiv (sub_one_over A).symm

-- local attribute [-simp] subtype.val_eq_coe

/-- The bottom of the subobject category. -/
def sub_bot (B : C) : sub B := sub.mk' (initial.to B)
@[simp] lemma sub_bot_left {B : C} : (↑(sub_bot B) : over B).left = ⊥_ C := rfl
@[simp] lemma sub_bot_arrow {B : C} : (sub_bot B).arrow = initial.to B := rfl
def subq_bot (B : C) : subq B := ⟦sub_bot B⟧

instance {B : C} : order_bot (subq B) :=
{ bot := subq_bot B,
  bot_le := quotient.ind
  begin
    intro a,
    refine ⟨sub.hom_mk (initial.to _) _⟩,
    dsimp,
    apply subsingleton.elim
  end,
  ..category_theory.subq.partial_order B }

lemma pullback_bot {A B : C} (f : A ⟶ B) : (subq.pullback f).obj ⊥ = ⊥ :=
begin
  apply quotient.sound,
  symmetry,
  refine ⟨sub.iso_mk _ _⟩,
  refine (as_iso pullback.fst).symm,
  dsimp,
  apply subsingleton.elim,
end

local attribute [instance] limits.has_coequalizers_of_has_finite_colimits
local attribute [instance] limits.has_finite_coproducts_of_has_finite_colimits

example (A B : C) (f : A ⟶ B) : regular_epi (factor_thru_image f) := by apply_instance

variables {A B : C}

-- def union' : sub' A → sub' A → sub' A := λ f g,
-- sub'.mk' (image.ι (coprod.desc f.arrow.hom g.arrow.hom))

-- lemma left_le_union' (f g : sub' A) : f ≤ union' f g :=
-- begin
--   refine ⟨_, _⟩,
--   apply coprod.inl ≫ factor_thru_image _,
--   dsimp [union'],
--   rw [assoc, image.fac, coprod.inl_desc],
-- end
-- lemma right_le_union' (f g : sub' A) : g ≤ union' f g :=
-- begin
--   refine ⟨_, _⟩,
--   apply coprod.inr ≫ factor_thru_image _,
--   dsimp [union'],
--   rw [assoc, image.fac, coprod.inr_desc],
-- end

-- lemma union'_le (f g h : sub' A) : f ≤ h → g ≤ h → union' f g ≤ h :=
-- begin
--   rintros ⟨hf, hf₁⟩ ⟨hg, hg₁⟩,
--   refine ⟨_, _⟩,
--   refine image.lift ⟨_, h.arrow.hom, coprod.desc hf hg⟩,
--   apply image.lift_fac,
-- end

-- lemma union'_mono {f₁ f₂ g₁ g₂ : sub' A} : f₁ ≤ f₂ → g₁ ≤ g₂ → union' f₁ g₁ ≤ union' f₂ g₂ :=
-- begin
--   intros hf hg,
--   apply union'_le,
--   apply le_trans hf (left_le_union' _ _),
--   apply le_trans hg (right_le_union' _ _),
-- end

-- def union : sub A → sub A → sub A := quotient.map₂ union'
-- begin
--   rintro f₁ f₂ ⟨hf₁, hf₂⟩ g₁ g₂ ⟨hg₁, hg₂⟩,
--   exact ⟨union'_mono hf₁ hg₁, union'_mono hf₂ hg₂⟩,
-- end

def equiv_to_iff {P Q : Prop} (h : P ≃ Q) : P ↔ Q :=
⟨h.to_fun, h.inv_fun⟩

lemma exp_transpose (a b c : subq A) : a ⊓ b ≤ c ↔ b ≤ (a ⟹ c) :=
begin
  rw ← prod_eq_inter,
  apply equiv_to_iff,
  apply equiv.plift.symm.trans (equiv.ulift.symm.trans (((exp.adjunction a).hom_equiv b c).trans (equiv.ulift.trans equiv.plift))),
end

-- def exist' (f : B ⟶ A) (a : sub' B) : sub' A :=
-- sub'.mk' (image.ι (a.arrow.hom ≫ f))

-- def exist'' (f : B ⟶ A) : sub' B ⥤ sub' A :=
-- preorder_functor (exist' f)
-- begin
--   rintros a₁ a₂ ⟨k, hk⟩,
--   refine ⟨_, _⟩,
--   refine image.lift {I := _, m := image.ι _, e := k ≫ factor_thru_image _, fac' := _},
--   rw [assoc, image.fac, reassoc_of hk],
--   apply image.lift_fac,
-- end

-- def exist (f : B ⟶ A) : sub B ⥤ sub A := lower_functor (exist'' f)

-- def pb_adj (f : B ⟶ A) : exist'' f ⊣ pullback_sub' f
  -- equiv.trans equiv.plift.symm $ equiv.trans equiv.ulift.symm $ equiv.trans ((exp.adjunction a).hom_equiv b c) _
-- begin
--   have : ulift (plift _) ≃ ulift (plift _) := (exp.adjunction a).hom_equiv b c,

-- end

instance : bounded_lattice (subq A) :=
{ ..category_theory.semilattice_inf_top,
  ..category_theory.semilattice_sup,
  ..category_theory.order_bot }

lemma coprod_eq_union {A : C} {f₁ f₂ : subq A} : (f₁ ⨿ f₂) = f₁ ⊔ f₂ :=
begin
  change f₁ ⊔ (f₂ ⊔ ⊥) = f₁ ⊔ f₂,
  simp,
end

-- (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
lemma subq.distrib (x y z : subq A) : x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) :=
begin
  rw [exp_transpose],
  apply sup_le,
  rw [← exp_transpose],
  exact le_sup_left,
  rw [← exp_transpose],
  exact le_sup_right,
end

lemma le_sup_inf_of_inf_sup_le {α : Type*} [lattice α]
  (inf_sup_le : ∀ x y z : α, x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z)) :
  ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z) :=
begin
  have : ∀ (x y z : α), x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z),
    intros x y z,
    apply le_antisymm (inf_sup_le x y z) (sup_le (inf_le_inf_left x le_sup_left) (inf_le_inf_left x le_sup_right)),
  intros,
  rw this,
  change ((x ⊔ y) ⊓ x) ⊔ ((x ⊔ y) ⊓ z) ≤ x ⊔ (y ⊓ z),
  apply sup_le,
    transitivity x,
      simp,
    simp,
  rw inf_comm,
  rw this,
  apply sup_le_sup,
  apply inf_le_right,
  rw inf_comm,
end

def sub.pullback_image_aux {A' : C} (f : A ⟶ B) (g : A' ⟶ B) :
  (sub.pullback f).obj (sub.image.obj (over.mk g)) ≅ sub.image.obj ((real_pullback f).obj (over.mk g)) :=
{ hom := sub.hom_mk (pullback_image _ _).hom (pullback_image_fac _ _),
  inv := sub.hom_mk (pullback_image _ _).inv (pullback_image_inv_fac _ _) }

/-- Image commutes with pullback. -/
def sub.pullback_image (f : A ⟶ B) :
  sub.image ⋙ sub.pullback f ≅ real_pullback f ⋙ sub.image :=
nat_iso.of_components (λ g, sub.pullback_image_aux f _) (by tidy)

/-- Lemma A1.3.3 of the Elephant. -/
def frobenius {A B : C} (f : A ⟶ B) (A' : sub A) (B' : sub B) :
    (sub.intersection.obj ((sub.exists f).obj A')).obj B' ≅
    (sub.exists f).obj ((sub.intersection.obj A').obj ((sub.pullback f).obj B')) :=
begin
  refine sub.iso_mk _ _,
  apply unique_factorise
    ((pullback.snd ≫ A'.arrow) ≫ f)
    (pullback B'.arrow (image.ι (A'.arrow ≫ f))) _ (pullback.fst ≫ B'.arrow) _,
  { apply pullback.lift (pullback.fst ≫ pullback.fst) (pullback.snd ≫ factor_thru_image _) _,
    rw [assoc, pullback.condition, assoc, image.fac],
    apply pullback.condition_assoc },
  { rw pullback.lift_fst_assoc,
    change (pullback.fst ≫ pullback.fst) ≫ B'.arrow = (pullback.snd ≫ A'.arrow) ≫ f,
    erw [assoc, pullback.condition, pullback.condition_assoc, assoc] },
  { apply category_theory.strong_epi_of_regular_epi _,
    apply regular_epi_of_is_pullback_alt _ pullback.snd pullback.snd (factor_thru_image (A'.arrow ≫ f)) _ _,
    apply pullback.lift_snd,
    refine both_pb_to_left_pb _ _ _ _ _ _ _ _ _ (cone_is_pullback _ _) _,
    simp only [pullback.lift_fst],
    have : factor_thru_image (A'.arrow ≫ f) ≫ image.ι (A'.arrow ≫ f) = A'.arrow ≫ f := image.fac _,
    convert left_pb_to_both_pb _ _ _ _ _ _ _ _ _ (cone_is_pullback pullback.snd A'.arrow) (cone_is_pullback B'.arrow f) },
  { erw unique_factorise_hom_comp_image, apply pullback.condition },
end

lemma subq.frobenius {A B : C} (f : A ⟶ B) (A' : subq A) (B' : subq B) :
  (subq.exists f).obj A' ⊓ B' = (subq.exists f).obj (A' ⊓ (subq.pullback f).obj B') :=
quotient.induction_on₂ A' B' $ λ a' b', quotient.sound ⟨frobenius f _ _⟩

instance pb_frob {A B : C} (f : A ⟶ B) (x : subq A) (y : subq B) :
  is_iso (frobenius_map y x (subq.exists_pull_adj f)) :=
{ inv :=
  begin
    refine ⟨⟨_⟩⟩,
    rw [prod_eq_inter, prod_eq_inter, inf_comm, subq.frobenius, inf_comm],
  end }

instance pb_preserves_lim (f : A ⟶ B) : preserves_limits (subq.pullback f) :=
adjunction.right_adjoint_preserves_limits (subq.exists_pull_adj f)

instance pullback_cc (f : A ⟶ B) : cartesian_closed_functor (subq.pullback f) :=
cartesian_closed_of_frobenius_iso (subq.exists_pull_adj f)

lemma pullback_exp (f : A ⟶ B) (x y : subq B) :
  (subq.pullback f).obj (x ⟹ y) = ((subq.pullback f).obj x ⟹ (subq.pullback f).obj y) :=
begin
  apply skel_is_skel,
  have := (category_theory.pullback_cc f).comparison_iso,
  refine @as_iso _ _ _ _ _ (this x y),
end

instance : bounded_distrib_lattice (subq A) :=
{ le_sup_inf := le_sup_inf_of_inf_sup_le subq.distrib,
  ..category_theory.bounded_lattice }

instance : has_compl (subq A) := { compl := λ x, x ⟹ ⊥ }

variables (x y z : subq A)

lemma imp_eq_top_iff_le : (x ⟹ y) = ⊤ ↔ x ≤ y :=
by rw [eq_top_iff, ← exp_transpose, inf_top_eq]

@[simp]
lemma imp_self : (x ⟹ x) = ⊤ :=
by rw [imp_eq_top_iff_le].

lemma classifier_of_pullback {E F A : C} (m : A ⟶ E) (f : F ⟶ E) [mono m] : f ≫ classifier_of m = classifier_of (pullback.snd : pullback m f ⟶ F) :=
begin
  symmetry,
  apply uniquely,
  apply left_right_hpb_to_both_hpb _ has_pullback_top_of_pb (classifies m),
end

lemma class_lift_of_is_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₁ ⟶ A₂) [is_iso h] :
  h ≫ m₂ = m₁ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros k,
  apply uniquely,
  change has_pullback_top _ _ _,
  rw ← id_comp (classifier_of m₂),
  apply left_right_hpb_to_both_hpb m₂,
  apply top_iso_has_pullback_top h,
    simpa,
  apply classifies,
end

lemma class_lift_of_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₁ ≅ A₂) (l : h.hom ≫ m₂ = m₁) :
  classifier_of m₁ = classifier_of m₂ :=
class_lift_of_is_iso h.hom l

lemma class_lift_of_both_factor {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (hom : A₁ ⟶ A₂) (inv : A₂ ⟶ A₁) :
  hom ≫ m₂ = m₁ → inv ≫ m₁ = m₂ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros k l,
  apply class_lift_of_iso ⟨hom, inv, _, _⟩ k,
  rw ← cancel_mono m₁, simp [k, l],
  rw ← cancel_mono m₂, simp [k, l],
end

def how_inj_is_classifier {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂]
  (h : classifier_of m₁ = classifier_of m₂) :
A₁ ≅ A₂ :=
{ hom := (pullback_cone.is_limit.lift' (classifies m₂).is_pb (classifies m₁).top m₁ (h ▸ (classifies m₁).comm)).1,
  inv := (pullback_cone.is_limit.lift' (classifies m₁).is_pb (classifies m₂).top m₂ (h.symm ▸ (classifies m₂).comm)).1,
  hom_inv_id' := by erw [← cancel_mono_id m₁, assoc, lift'_right, lift'_right],
  inv_hom_id' := by erw [← cancel_mono_id m₂, assoc, lift'_right, lift'_right] }

lemma c_very_inj {E A₁ A₂ : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : classifier_of m₁ = classifier_of m₂) :
  (how_inj_is_classifier _ _ h).hom ≫ m₂ = m₁ :=
lift'_right _ _ _ _

def get_subobject_obj {B : C} (c : B ⟶ Ω C) : C := pullback (truth C) c
def get_subobject {B : C} (c : B ⟶ Ω C) : get_subobject_obj c ⟶ B := pullback.snd
instance get_subobject_mono {B : C} (c : B ⟶ Ω C) : mono (get_subobject c) := pullback.snd_of_mono

lemma classify_inv {E : C} (c : E ⟶ Ω C) : classifier_of (get_subobject c) = c :=
(uniquely _ _ has_pullback_top_of_pb)

set_option pp.universes false

@[simps]
def classification {B : C} : (B ⟶ Ω C) ≃ subq B :=
{ to_fun := λ k, ⟦sub.mk' (get_subobject k)⟧,
  inv_fun :=
  begin
    refine quotient.lift (λ (k : sub B), _) _,
    exact classifier_of k.arrow,
    rintro a₁ a₂ ⟨⟨k₁, k₂, _, _⟩⟩,
    apply class_lift_of_both_factor _ _ (sub.w k₁) (sub.w k₂),
  end,
  left_inv := λ k, classify_inv k,
  right_inv := quotient.ind
  begin
    intro k,
    apply quotient.sound,
    refine equiv_of_both_ways
      (sub.hom_mk _ ((classifies k.arrow).is_pb.fac _ walking_cospan.right))
      (sub.hom_mk _ (pullback.lift_snd _ _ (classifies k.arrow).comm)),
  end }

abbreviation classify {B : C} : subq B → (B ⟶ Ω C) := classification.symm

lemma classify_eq_iff_eq {B : C} (m n : subq B) : classify m = classify n ↔ m = n :=
classification.right_inv.injective.eq_iff

lemma classify_pullback {B B' : C} (f : B ⟶ B') :
  ∀ m, classify ((subq.pullback f).obj m) = f ≫ classify m :=
quotient.ind $ by { intro m, exact (classifier_of_pullback _ _).symm }

lemma classification_natural_symm {B B' : C} (f : B ⟶ B') (c : B' ⟶ Ω C) :
  classification (f ≫ c) = (subq.pullback f).obj (classification c) :=
begin
  rw [← classification.eq_symm_apply],
  change _ = classify _,
  rw [classify_pullback],
  congr',
  symmetry,
  apply classification.symm_apply_apply c,
end
-- def indicators {B : C} (m : B ⟶ Ω C) (n : B ⟶ Ω C) : B ⟶ Ω C :=
-- classify (classification m ⊓ classification n)

-- def indicators_natural {B B' : C} (f : B' ⟶ B) (m : B ⟶ Ω C) (n : B ⟶ Ω C) :
--   f ≫ indicators m n = indicators (f ≫ m) (f ≫ n) :=
-- begin
--   dunfold indicators,
--   rw [classification_natural_symm, classification_natural_symm, ← intersect_pullback,
--       classification.eq_symm_apply, classification_natural_symm, classification.apply_symm_apply],
-- end

-- variable (C)
-- def and_arrow : Ω C ⨯ Ω C ⟶ Ω C := indicators limits.prod.fst limits.prod.snd
-- variable {C}h

lemma compl_natural (m : subq B) (f : A ⟶ B) : (subq.pullback f).obj mᶜ = ((subq.pullback f).obj m)ᶜ :=
by { erw [pullback_exp, pullback_bot], refl }

def neg_arrow_aux (m : B ⟶ Ω C) : B ⟶ Ω C :=
classify (classification m)ᶜ

lemma neg_arrow_aux_natural {B B' : C} (f : B' ⟶ B) (m : B ⟶ Ω C) :
  f ≫ neg_arrow_aux m = neg_arrow_aux (f ≫ m) :=
begin
  rw [neg_arrow_aux, neg_arrow_aux, classification.eq_symm_apply, classification_natural_symm,
      classification_natural_symm, classification.apply_symm_apply, compl_natural],
end

variable (C)
def not : Ω C ⟶ Ω C := neg_arrow_aux (𝟙 _)
variable {C}

lemma not_prop (f : subq B) : classify fᶜ = classify f ≫ not C :=
by rw [not, neg_arrow_aux_natural, comp_id, neg_arrow_aux, classification.apply_symm_apply]

end category_theory
