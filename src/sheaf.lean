import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflect_isomorphisms
import category_theory.limits.shapes.constructions.preserve_binary_products
import reflects
import equiv

open category_theory category_theory.category category_theory.limits
open classifier

universes v u u₂

def tag (n : ℕ) {α : Sort u} (x : α) : α := x

variables (C : Type u) [category.{v} C]

class topos extends has_finite_limits.{v} C, has_subobject_classifier.{v} C, is_cartesian_closed.{v} C.

variables [topos.{v} C]

variable {C}
def tag' (n : ℕ) (A B : C) (f : A ⟶ B) : A ⟶ B := f

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
def classification {B : C} : (B ⟶ Ω C) ≃ sub B :=
{ to_fun := λ k, sub.mk (get_subobject k),
  inv_fun :=
  begin
    refine quotient.lift (λ (k : sub'.{v} B), _) _,
    exact classifier_of k.arrow.hom,
    rintro a₁ a₂ ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩,
    apply class_lift_of_both_factor k₁ k₂ hk₁ hk₂,
  end,
  left_inv := λ k, classify_inv k,
  right_inv := quotient.ind
  begin
    intro k,
    apply quotient.sound,
    refine ⟨⟨_, (classifies k.arrow.hom).is_pb.fac _ walking_cospan.right⟩,
            ⟨_, pullback.lift_snd _ _ (classifies k.arrow.hom).comm⟩⟩,
  end }

abbreviation classify {B : C} : sub B → (B ⟶ Ω C) := classification.symm

lemma classify_eq_iff_eq {B : C} (m n : sub B) : classify m = classify n ↔ m = n :=
classification.right_inv.injective.eq_iff

lemma classify_pullback {B B' : C} (f : B ⟶ B') :
  ∀ m, classify (pullback_sub f m) = f ≫ classify m :=
quotient.ind $ by { intro m, exact (classifier_of_pullback _ _).symm }

lemma classification_natural_symm {B B' : C} (f : B ⟶ B') (c : B' ⟶ Ω C) :
  classification (f ≫ c) = pullback_sub f (classification c) :=
begin
  rw [← classification.eq_symm_apply],
  change _ = classify _,
  rw [classify_pullback],
  congr',
  symmetry,
  apply classification.symm_apply_apply c,
end

def sub_bot {B : C} : sub B := sub.mk (initial.to B)
instance {B : C} : order_bot (sub B) :=
{ bot := sub_bot,
  bot_le := quotient.ind
  begin
    intro a,
    refine ⟨initial.to _, _⟩,
    dsimp,
    apply subsingleton.elim,
  end,
  ..category_theory.sub_partial }

-- -- lemma inf_eq_intersection :
-- namespace intersect

def indicators {B : C} (m : B ⟶ Ω C) (n : B ⟶ Ω C) : B ⟶ Ω C :=
classify (classification m ⊓ classification n)

def indicators_natural {B B' : C} (f : B' ⟶ B) (m : B ⟶ Ω C) (n : B ⟶ Ω C) :
  f ≫ indicators m n = indicators (f ≫ m) (f ≫ n) :=
begin
  dunfold indicators,
  rw [classification_natural_symm, classification_natural_symm, ← intersect_pullback,
      classification.eq_symm_apply, classification_natural_symm, classification.apply_symm_apply],
end

variable (C)
def and_arrow : Ω C ⨯ Ω C ⟶ Ω C := indicators limits.prod.fst limits.prod.snd
variable {C}

lemma property {B : C} (m₁ m₂ : sub B) :
  prod.lift (classify m₁) (classify m₂) ≫ and_arrow C = classify (m₁ ⊓ m₂) :=
by rw [and_arrow, indicators_natural, prod.lift_fst, prod.lift_snd, indicators,
       classification.apply_symm_apply, classification.apply_symm_apply]

lemma leq_iff_comp_and {E : C} (m n : sub E) :
  m ≤ n ↔ prod.lift (classify m) (classify n) ≫ and_arrow C = classify m :=
by simp only [← inf_eq_left, property, ← classification.apply_eq_iff_eq, classification.apply_symm_apply]

lemma factors_iff_comp_and {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] :
  factors_through m₁ m₂ ↔ prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁ :=
leq_iff_comp_and (sub.mk m₁) (sub.mk m₂)

@[reassoc] lemma classify_postcompose {A A' E : C} (n : A ⟶ A') (m : A' ⟶ E) [mono n] [mono m] :
  classifier_of n = m ≫ classifier_of (n ≫ m) :=
uniquely _ _ (left_right_hpb_to_both_hpb _ (top_iso_has_pullback_top _ n _ m (id_comp _)) (classifies (n ≫ m)))

class topology (j : Ω C ⟶ Ω C) :=
(ax1 : truth C ≫ j = truth C)
(ax2 : j ≫ j = j)
(ax3 : and_arrow C ≫ j = limits.prod.map j j ≫ and_arrow C)

-- variable {C}

lemma classify_self {E : C} : classifier_of (𝟙 E) = default (E ⟶ Ω₀ C) ≫ truth C :=
begin
  apply uniquely,
  apply left_iso_has_pullback_top (default (E ⟶ Ω₀ C)),
  rw id_comp
end

lemma classify_mk {A E : C} (m : A ⟶ E) [mono m] : classify (sub.mk m) = classifier_of m := rfl

lemma classify_top (E : C) : classify ⊤ = default (E ⟶ Ω₀ C) ≫ truth C :=
by { dsimp [top_eq_top, classification_to_fun, sub_top], exact classify_self }

variables (j : Ω C ⟶ Ω C) [topology.{v} j]

namespace closure

variables {E A : C}

def obj (m : A ⟶ E) [mono m] : C := pullback (truth C) (classifier_of m ≫ j)
def arrow (m : A ⟶ E) [mono m] : closure.obj j m ⟶ E := pullback.snd
instance is_sub (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := pullback.snd_of_mono
lemma classifier (m : A ⟶ E) [mono m] : classifier_of (arrow j m) = classifier_of m ≫ j :=
uniquely _ _ (has_pullback_top_of_pb)
def operator (m : sub E) : sub E := classification (_root_.classify m ≫ j)
def subobj (m : A ⟶ E) [mono m] : sub E := operator j (sub.mk m)
lemma classify_op : ∀ (m : sub E), classify (operator j m) = classify m ≫ j :=
quotient.ind $
begin
  intro a,
  exact classifier j _,
end
lemma classify (m : A ⟶ E) [mono m] : classify (subobj j m) = classify (sub.mk m) ≫ j :=
classifier j m

def less_than_closure (m : A ⟶ E) [mono m] : A ⟶ closure.obj j m :=
pullback.lift (classifies m).top m $ by rw [← (classifies m).comm_assoc, topology.ax1]

@[reassoc] lemma is_lt (m : A ⟶ E) [mono m] : less_than_closure j m ≫ closure.arrow j m = m :=
pullback.lift_snd _ _ _

instance (m : A ⟶ E) [mono m] : mono (less_than_closure j m) := mono_of_mono_fac (is_lt j m)

def idem (m : A ⟶ E) [mono m] : obj j (arrow j m) ≅ obj j m :=
begin
  have: classifier_of (arrow j (arrow j m)) = classifier_of (arrow j m),
    rw [classifier, classifier, assoc, topology.ax2],
  exact how_inj_is_classifier _ _ this,
end

def closure_intersection {E : C} {m m' : sub E} : closure.operator j (m ⊓ m') = closure.operator j m ⊓ closure.operator j m' :=
by simp only [← classify_eq_iff_eq, closure.classify_op, ← property, ← prod.lift_map, assoc, topology.ax3]

def monotone {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (h : factors_through m n) :
  factors_through (arrow j m) (arrow j n) :=
begin
  rw [factors_iff_comp_and] at h,
  rw [factors_iff_comp_and, closure.classifier, closure.classifier, ← prod.lift_map, assoc,
      ← topology.ax3, reassoc_of h],
end
def mono_sub : ∀ (m n : sub E), m ≤ n → operator j m ≤ operator j n :=
quotient.ind₂ $
begin
  intros a b,
  exact monotone j a.arrow.hom b.arrow.hom
end
lemma comm_pullback (m : sub E) (f : A ⟶ E) :
  pullback_sub f (operator j m) = operator j (pullback_sub f m) :=
by rw [← classify_eq_iff_eq, classify_pullback, classify_op, classify_op, classify_pullback, assoc]

class dense (m : A ⟶ E) extends mono.{v} m :=
(closure_eq_top : subobj j m = ⊤)

def dense_of_classifier_eq {m : A ⟶ E} [mono m] (hm : classifier_of m ≫ j = default _ ≫ truth C) : dense j m :=
⟨by { rw [← classify_eq_iff_eq, classify_top, ← hm, ← closure.classifier], refl }⟩

instance dense_inclusion (m : A ⟶ E) [mono m] : dense j (less_than_closure j m) :=
begin
  apply dense_of_classifier_eq,
  rw [classify_postcompose _ (arrow j m)],
  slice_lhs 2 2 {congr, rw is_lt},
  rw [← closure.classifier, ← (classifies (arrow j m)).comm],
  congr,
end

lemma classifier_eq_of_dense (m : A ⟶ E) [d : dense j m] : classifier_of m ≫ j = default _ ≫ truth C :=
by { rw [← classify_top, ← d.closure_eq_top, ← closure.classifier], refl }

class closed (m : A ⟶ E) extends mono.{v} m :=
(closure_eq_self : subobj j m = sub.mk m)

def closed_of_classifier_eq {m : A ⟶ E} [mono m] (hm : classifier_of m ≫ j = classifier_of m) : closed j m :=
⟨by rwa [← classify_eq_iff_eq, classify_mk, closure.classify]⟩

lemma classifier_eq_of_closed (m : A ⟶ E) [c : closed j m] : classifier_of m ≫ j = classifier_of m :=
by rw [← classify_mk, ← classify, c.closure_eq_self]

instance is_closed (m : A ⟶ E) [mono m] : closed j (arrow j m) :=
begin
  apply closed_of_classifier_eq,
  rw [closure.classifier, assoc, topology.ax2],
end

def mono_of_is_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [mono m] : mono l :=
begin
  refine ⟨λ Z g h eq, _⟩,
  apply lim.hom_ext,
  apply (pullback_cone.mk t l comm).equalizer_ext,
  rw ← cancel_mono m,
  erw [assoc, assoc, comm, reassoc_of eq],
  exact eq
end

def dense_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [d : closure.dense j m] : closure.dense j l :=
begin
  haveI := mono_of_is_pullback comm lim,
  have : sub.mk l = pullback_sub f (sub.mk m),
    apply quotient.sound,
    refine ⟨⟨_, pullback.lift_snd _ _ comm⟩, ⟨lim.lift _, lim.fac _ walking_cospan.right⟩⟩,
  refine ⟨_⟩,
  rw [subobj, this, ← closure.comm_pullback],
  convert pullback_top f,
  apply d.closure_eq_top,
end

def dense_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j f] : dense j t :=
dense_of_pullback _ comm.symm (pullback_flip lim)

end closure

def lifting_square {A A' B B' : C} {f' : B' ⟶ A'} {m : A' ⟶ A} {n : B' ⟶ B} {f : B ⟶ A}
  (comm : f' ≫ m = n ≫ f) [d : closure.dense j n] [c : closure.closed j m] : {k // k ≫ m = f} :=
begin
  have : ⊤ ≤ pullback_sub f (sub.mk m),
    rw [← d.closure_eq_top, ← c.closure_eq_self, closure.subobj, closure.subobj,
        closure.comm_pullback],
    apply closure.mono_sub,
    refine ⟨_, pullback.lift_snd _ _ comm⟩,
  obtain ⟨p, hp⟩ : {p : B ⟶ pullback m f // p ≫ pullback.snd = 𝟙 B } := raised_factors this,
  refine ⟨p ≫ pullback.fst, _⟩,
  rw [assoc, pullback.condition, reassoc_of hp],
end


-- -- This proof is a bit trash.
-- def characterised {m m' : sub' E} (hm : m ≤ m') [d : dense j ⟦mediating_subobject hm⟧] [c : closed j ⟦m'⟧] :
--   closure j ⟦m⟧ = ⟦m'⟧ :=
-- begin
--   rw [closure, classification_inv_fun],
--   apply quotient.sound,
--   resetI,
--   refine ⟨_, ⟨_, _⟩⟩,
--   cases hm,
--   refine ⟨_, _⟩,
--   refine lifting_square j (get_subobject _) (mediating_subobject (less_than_closure j ⟦m⟧)) m' hm_w _,
--   rw ← hm_h, symmetry, apply mediating_subobject_prop,
--   rw lifting_square_prop, refl,
--   apply @lifting_square _ _ _ _ _ j _ _ _ m'.1.hom (mediating_subobject hm) _ (raise_le (less_than_closure j ⟦m⟧)) (id _) _ _,
--   apply closed_of_classifier_eq, dsimp, rw classify_inv, rw assoc, rw topology.ax2,
--   rw raise_le_prop, rw mediating_subobject_prop,
--   rw lifting_square_prop,
-- end

-- end closure

-- variable (C)
-- -- structure separated :=
-- -- (A : C)
-- -- (subsingleton_extend : Π B B' (m : B' ⟶ B) f' [closure.dense j m],
-- --   subsingleton {f : B ⟶ A // m ≫ f = f'})

-- -- def exists_lifting (A : C) : Prop := ∀ {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ A) [closure.dense j m],
-- -- nonempty {f : B ⟶ A // m ≫ f = f'}

-- -- def make_lifting (A : C) (h : exists_lifting )

structure sheaf' :=
(A : C)
(unique_extend : Π {B B'} (m : B' ⟶ B) f' [closure.dense j m], unique {f : B ⟶ A // m ≫ f = f'})

def forget_sheaf : sheaf'.{v} j → C := sheaf'.A

def sheaf := induced_category C (forget_sheaf j)

instance sheaf_category.category : category (sheaf j) := induced_category.category _
def forget : sheaf j ⥤ C := induced_functor _

variables {j}

@[simps]
def sheaf.mk (A : C) (h : Π {B B'} (m : B' ⟶ B) f' [closure.dense j m], unique {f : B ⟶ A // m ≫ f = f'}) : sheaf j :=
{ A := A,
  unique_extend := λ B B' m f' d, by { resetI; apply h } }

@[reducible]
def sheaf.mk' (A : C) (h : Π {B B'} (m : B' ⟶ B) f' [closure.dense j m], {f : B ⟶ A // m ≫ f = f' ∧ ∀ a, m ≫ a = f' → a = f}) : sheaf j :=
sheaf.mk A $ λ B B' m f' d,
begin
  haveI := d,
  refine ⟨⟨⟨(h m f').1, (h m f').2.1⟩⟩, _⟩,
  rintro ⟨a, ha⟩,
  congr,
  apply (h m f').2.2 _ ha,
end

def sheaf.A (A : sheaf j) : C := (forget j).obj A

def sheaf.hom_mk (A B : sheaf j) (f : A.A ⟶ B.A) : A ⟶ B := f

def extend_map' (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : {f // m ≫ f = f'} :=
(A.unique_extend m f').1.1

def extend_map (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : B ⟶ A.A :=
(extend_map' A m f').1

lemma extend_map_prop (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : m ≫ extend_map A m f' = f' :=
(extend_map' A m f').2

lemma unique_extension (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A)
  (f : B ⟶ A.A) (h : m ≫ f = f') :
f = extend_map A m f' :=
congr_arg subtype.val ((A.unique_extend m f').2 ⟨f, h⟩)

def unique_ext (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A)
  (f₁ f₂ : B ⟶ A.A) (h₁ : m ≫ f₁ = f') (h₂ : m ≫ f₂ = f') :
  f₁ = f₂ :=
(unique_extension A m f' f₁ h₁).trans (unique_extension A m f' f₂ h₂).symm

instance sheaf_forget_full : full (forget j) := induced_category.full _
instance sheaf_forget_faithful : faithful (forget j) := induced_category.faithful _
instance sheaf_forget_reflects_limits : reflects_limits (forget j) := by apply_instance

attribute [irreducible] sheaf

-- -- section biject
-- -- variables {A : C} (j) (m : sub' A) [closure.dense j ⟦m⟧]

-- -- def bijection : {n : sub A // closure.closure j n = n} ≃ {n' : sub m.1.left // closure.closure j n' = n'} :=
-- -- { to_fun := λ n,
-- --   { val := sub_map m.1.hom n.val,
-- --     property :=
-- --     begin
-- --       apply classification.left_inv.injective,
-- --       rw [closure.classify, ← classification_natural, assoc, ← closure.classify, n.2],
-- --     end },
-- --   inv_fun := λ n',
-- --   { val :=
-- --     begin
-- --       haveI := m.2,
-- --       apply closure.closure j (postcompose m.1.hom n'.1),
-- --     end,
-- --     property := closure.idem _ _ },
-- --   left_inv :=
-- --   begin
-- --     rintro ⟨N, hN⟩,
-- --     dsimp,
-- --     revert hN,
-- --     apply quotient.induction_on N,
-- --     intros n hn,
-- --     congr' 1,
-- --     apply characterised j _,
-- --     refine ⟨pullback.fst, pullback.condition.symm⟩,
-- --     refine ⟨_⟩,
-- --     rw ← top_le_iff,
-- --     refine ⟨pullback.lift (default _) (𝟙 _) _, _⟩,
-- --     dsimp, rw [id_comp],
-- --     dsimp [mediating_subobject],
-- --     erw classify_postcompose,


-- --     apply quotient.sound,

-- --     sorry,
-- --     refine ⟨hn⟩,
-- --   end,
-- --   right_inv :=
-- --   begin
-- --     rintro ⟨n', hn'⟩,
-- --     dsimp, congr' 1,
-- --     rw comm_pullback,
-- --     haveI := m.2,
-- --     rw ← postcompose_sub_comm (𝟙 _) (𝟙 _) m.val.hom m.val.hom rfl (pullback_square_iso _ _ _ _ _) n',
-- --     rw [postcompose_map_id, sub_map_id, hn'],
-- --   end
-- --   -- { obj := sub_map m.1.hom n.obj,
-- --   --   is_closed :=
-- --   --   begin
-- --   --     apply closed_of_classifier_eq,
-- --   --     rw ← classification_natural,
-- --   --     rw assoc,
-- --   --     haveI := n.is_closed,
-- --   --     rw classifier_eq_of_closed j n.obj,
-- --   --   end },
-- --   -- inv_fun := λ n',
-- --   -- { obj :=
-- --   --   begin
-- --   --     haveI := m.2,
-- --   --     exact closure j (postcompose m.1.hom n'.obj),
-- --   --   end },
-- --   -- left_inv :=
-- --   -- begin
-- --   --   rintro ⟨n, hn⟩,
-- --   --   dsimp,
-- --   --   congr' 1,
-- --   --   sorry,


-- --   -- end

-- -- }
-- -- -- def pushforward_closed_subobject {B' : C} (n : B' ⟶ B) [mono n] :
-- -- --   C :=
-- -- -- closure.obj j (n ≫ m)

-- -- -- def pushforward_closed_arrow {B' : C} (n : B' ⟶ B) [mono n]:
-- -- --   pushforward_closed_subobject j m n ⟶ A :=
-- -- -- closure.arrow j (n ≫ m)

-- -- -- instance {B' : C} (n : B' ⟶ B) [mono n] :
-- -- --   mono (pushforward_closed_arrow j m n) :=
-- -- -- closure.is_sub j _

-- -- -- instance {B' : C} (n : B' ⟶ B) [mono n] :
-- -- --   closure.closed j (pushforward_closed_arrow j m n) :=
-- -- -- closure.is_closed j _

-- -- -- lemma classify_pushforward_obj {B' : C} (n : B' ⟶ B) [mono n] :
-- -- --   classifier_of (pushforward_closed_arrow j m n) = classifier_of (n ≫ m) ≫ j :=
-- -- -- closure.hat j _

-- -- -- def pullback_closed_subobject {A' : C} (n : A' ⟶ A) [mono n] :
-- -- --   C :=
-- -- -- pullback n m

-- -- -- def pullback_closed_arrow {A' : C} (n : A' ⟶ A) [mono n] :
-- -- --   pullback_closed_subobject m n ⟶ B :=
-- -- -- pullback.snd

-- -- -- instance {A' : C} (n : A' ⟶ A) [mono n] :
-- -- --   mono (pullback_closed_arrow m n) :=
-- -- -- pullback.snd_of_mono

-- -- -- instance {A' : C} (n : A' ⟶ A) [closure.closed j n] :
-- -- --   closure.closed j (pullback_closed_arrow m n) :=
-- -- -- begin
-- -- --   apply closure.closed_of_classifier_eq,
-- -- --   erw [← classify_pullback, assoc, closure.classifier_eq_of_closed],
-- -- -- end

-- -- -- lemma classify_pullback_obj {A' : C} (n : A' ⟶ A) [mono n] :
-- -- --   classifier_of (pullback_closed_arrow m n) = m ≫ classifier_of n :=
-- -- -- (classify_pullback _ _).symm

-- -- -- def classify_pullback_pushout {A' : C} (n : A' ⟶ A) [closure.closed j n] :
-- -- --   pushforward_closed_subobject j m (pullback_closed_arrow m n) ≅ A' :=
-- -- -- begin
-- -- --   apply closure.characterised j _ pullback.fst n pullback.condition,
-- -- --   apply closure.dense_top_of_pullback j pullback.condition (cone_is_pullback _ m),
-- -- -- end

-- -- -- lemma classify_pullback_pushout_comm {A' : C} (n : A' ⟶ A) [closure.closed j n] :
-- -- --   (classify_pullback_pushout j m n).hom ≫ n = pushforward_closed_arrow j m (pullback_closed_arrow m n) :=
-- -- -- begin
-- -- --   rw classify_pullback_pushout,
-- -- --   rw closure.characterised,
-- -- --   dsimp,
-- -- --   rw closure.lifting_square_prop,
-- -- --   refl,
-- -- -- end

-- -- -- lemma classify_pullback_pushforward {A' : C} (n : A' ⟶ A) [closure.closed j n] :
-- -- --   classifier_of (pushforward_closed_arrow j m (pullback_closed_arrow m n)) = classifier_of n :=
-- -- -- class_lift_of_iso _ (classify_pullback_pushout_comm j m n).symm

-- -- -- lemma classify_pushforward_pullback {B' : C} (n : B' ⟶ B) [closure.closed j n] :
-- -- --   classifier_of (pullback_closed_arrow m (pushforward_closed_arrow j m n)) = classifier_of n :=
-- -- -- begin
-- -- --   rw [classify_pullback_obj, classify_pushforward_obj, ← assoc, ← closure.classify_subobj],
-- -- --   apply closure.classifier_eq_of_closed
-- -- -- end

-- -- -- @[simps]
-- -- -- def bijection (m : B ⟶ A) [closure.dense j m] : {cm : B ⟶ Ω C // cm ≫ j = cm} ≃ {cm' : A ⟶ Ω C // cm' ≫ j = cm'} :=
-- -- -- { to_fun :=
-- -- --   begin
-- -- --     intro a,
-- -- --     let Bsubobj : pullback (truth C) a.1 ⟶ B := pullback.snd,
-- -- --     refine ⟨classifier_of (pushforward_closed_arrow j m Bsubobj), closure.classifier_eq_of_closed j _⟩,
-- -- --   end,
-- -- --   inv_fun :=
-- -- --   begin
-- -- --     intro a,
-- -- --     let Asubobj : pullback (truth C) a.1 ⟶ A := pullback.snd,
-- -- --     have : a.1 = classifier_of Asubobj,
-- -- --       apply has_subobject_classifier.uniquely _ _ ⟨_, _, cone_is_pullback _ _⟩,
-- -- --     have : classifier_of Asubobj ≫ j = classifier_of Asubobj,
-- -- --       rw ← this,
-- -- --       exact a.2,
-- -- --     haveI : closure.closed j Asubobj := closure.closed_of_classifier_eq j _ this,
-- -- --     refine ⟨classifier_of (pullback_closed_arrow m Asubobj), closure.classifier_eq_of_closed j _⟩,
-- -- --   end,
-- -- --   left_inv :=
-- -- --   begin
-- -- --     rintro ⟨a, ha⟩,
-- -- --     dsimp,
-- -- --     congr,
-- -- --     rwa [classify_pullback_obj, classify_inv, classify_pushforward_obj, ← assoc, ← closure.classify_subobj, classify_inv a],
-- -- --   end,
-- -- --   right_inv :=
-- -- --   begin
-- -- --     rintro ⟨a, ha⟩,
-- -- --     dsimp,
-- -- --     congr,
-- -- --     let Asubobj : pullback (truth C) a ⟶ A := pullback.snd,
-- -- --     have z : classifier_of Asubobj = a := classify_inv a,
-- -- --     have : classifier_of Asubobj ≫ j = classifier_of Asubobj,
-- -- --       rw [z, ha],
-- -- --     haveI := closure.closed_of_classifier_eq j _ this,
-- -- --     conv_rhs {rw ← z},
-- -- --     rw classify_pushforward_obj,
-- -- --     rw classify_pullback_obj,
-- -- --     have z₁ : m ≫ classifier_of Asubobj = classifier_of (pullback.snd : pullback Asubobj m ⟶ B) := classify_pullback Asubobj m,
-- -- --     have z₂ : classifier_of (pullback.snd : pullback (truth C) (m ≫ classifier_of Asubobj) ⟶ B) = m ≫ classifier_of Asubobj := classify_inv (m ≫ classifier_of Asubobj),
-- -- --     have : classifier_of (pullback.snd : pullback (truth C) (m ≫ classifier_of Asubobj) ⟶ B) = classifier_of (pullback.snd : pullback Asubobj m ⟶ B), cc,
-- -- --     have := pushforward_well_defined m _ _ this,
-- -- --     rw this,
-- -- --     change classifier_of (pullback_closed_arrow m Asubobj ≫ m) ≫ j = _,
-- -- --     rw ← classify_pushforward_obj,
-- -- --     rw classify_pullback_pushforward j m Asubobj,
-- -- --   end
-- -- -- }

-- -- end biject

namespace construct_limits


variables {C} {J : Type v} [𝒥₁ : small_category J] {K : J ⥤ sheaf j} {c : cone (K ⋙ forget j)} (t : is_limit c)
variables {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ c.X)

@[simps]
def alt_cone [closure.dense j m] : cone (K ⋙ forget j) :=
{ X := B,
  π :=
  { app := λ i, extend_map (K.obj i) m (f' ≫ c.π.app i),
    naturality' := λ i₁ i₂ g,
    begin
      dsimp,
      rw [id_comp],
      symmetry,
      apply unique_extension (K.obj i₂) m (f' ≫ c.π.app i₂),
      erw [← assoc, extend_map_prop, assoc, c.w g],
    end } }

instance sheaf_forget_creates_limits : creates_limits (forget j) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X := sheaf.mk' c.X $
          λ B B' m f' d,
            begin
              refine ⟨t.lift (alt_cone m f'), _, _⟩,
              { apply t.hom_ext,
                intro i,
                rw [assoc, t.fac (alt_cone m f')],
                exact extend_map_prop (K.obj i) m (f' ≫ c.π.app i) },
              { intros f₂ hf₂,
                apply t.uniq (alt_cone m f'),
                intro i,
                apply unique_extension (K.obj i) m,
                rw [← hf₂, assoc] }
            end,
          π :=
          { app := c.π.app,
            naturality' := λ X Y f, c.π.naturality f } },
        valid_lift := cones.ext (iso.refl _) (λ i, (id_comp _).symm) } } } }

end construct_limits

instance sheaf_has_finite_limits : has_finite_limits.{v} (sheaf j) :=
{ has_limits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI
  { has_limit := λ F, has_limit_of_created F (forget j) } }

def iso_limit (J : Type v) [small_category J] [fin_category J] (F : J ⥤ sheaf j) : (forget j).obj (limit F) ≅ limit (F ⋙ forget j) :=
by apply (cones.forget (F ⋙ forget j)).map_iso (lifted_limit_maps_to_original (limit.is_limit (F ⋙ forget j)))

variables (j)

def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
  closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
closure.dense_of_pullback j _ (pullback_prod' m A)

def sheaf_exponential (A : C) (s : sheaf j) : sheaf j :=
sheaf.mk' (A ⟹ s.A) $ λ B B' m f' d,
begin
  haveI := d,
  haveI := dense_prod_map_id j A m,
  refine ⟨cart_closed.curry _, _, _⟩,
  { exact extend_map s (limits.prod.map (𝟙 A) m) (cart_closed.uncurry f') },
  { rw [← curry_natural_left, extend_map_prop s, curry_uncurry] },
  { rintro a ha,
    rw eq_curry_iff,
    apply unique_extension s,
    rw [← uncurry_natural_left, ha] }
end

instance : is_cartesian_closed (sheaf j) :=
{ cart_closed := λ A,
  { is_adj :=
    { right :=
      { obj := λ s, sheaf_exponential j A.A s,
        map := λ s₁ s₂ f, post A.A f,
        map_id' := λ s, (exp.functor A.A).map_id _,
        map_comp' := λ _ _ _ _ _, (exp.functor A.A).map_comp _ _ },
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ X Y,
        { to_fun := λ f, cart_closed.curry (inv (prod_comparison (forget j) A X) ≫ f),
          inv_fun := λ g, by apply (prod_comparison (forget j) A X) ≫ cart_closed.uncurry g,
          left_inv := λ f, by simp,
          right_inv := λ g, by simp },
        hom_equiv_naturality_left_symm' :=
        begin
          intros X' X Y f g,
          dsimp,
          conv_lhs {congr, skip, erw uncurry_natural_left },
          apply (prod_comparison_natural_assoc (forget j) (𝟙 A) f _).symm,
        end,
        hom_equiv_naturality_right' :=
        begin
          intros X Y Y' f g,
          dsimp,
          conv_rhs {apply_congr (curry_natural_right _ _).symm},
          simpa
        end } } } }

def subobject_of_closed_sheaf (A : sheaf j) (A' : C) (m : A' ⟶ A.A) [closure.closed j m] : sheaf j :=
sheaf.mk' A' $ λ B B' n f' d, by exactI
begin
  obtain ⟨g, comm⟩ := extend_map' A n (f' ≫ m),
  refine ⟨(lifting_square j comm.symm).1, _, _⟩,
  rwa [← cancel_mono m, assoc, (lifting_square j comm.symm).2],
  intros a ha,
  rw [← cancel_mono m, (lifting_square j comm.symm).2],
  apply unique_ext A n (f' ≫ m) (a ≫ m) g _ comm,
  rw reassoc_of ha,
end

def closed_of_subsheaf (E A : sheaf j) (m : A.A ⟶ E.A) [mono m] : closure.closed j m :=
begin
  obtain ⟨r, hr⟩ := extend_map' A (closure.less_than_closure j m) (𝟙 _),
  have := unique_ext _ _ _ (r ≫ m) _ (by rw [reassoc_of hr]) (closure.is_lt _ _),
  refine ⟨quotient.sound ⟨⟨r, this⟩, ⟨closure.less_than_closure j m, closure.is_lt j m⟩⟩⟩,
end

def closed_classifier : C := equalizer j (𝟙 _)

def eq_equiv (B : C) : (B ⟶ closed_classifier j) ≃ {cm : B ⟶ Ω C // cm ≫ j = cm} :=
{ to_fun := λ f, ⟨f ≫ equalizer.ι _ _, by simp [equalizer.condition]⟩,
  inv_fun := λ f, equalizer.lift f.1 (by rw [f.2, comp_id]),
  left_inv := λ f, equalizer.hom_ext (equalizer.lift_ι _ _),
  right_inv := λ ⟨f, hf⟩, subtype.eq' (equalizer.lift_ι _ _) }

def closed_equiv {B B' : C} (m : B' ⟶ B) [closure.dense j m] : {cB' : B' ⟶ Ω C // cB' ≫ j = cB'} ≃ {cB : B ⟶ Ω C // cB ≫ j = cB} :=
{ to_fun := λ k, ⟨classifier_of (closure.arrow j (get_subobject k.1 ≫ m)), closure.classifier_eq_of_closed j _⟩,
  inv_fun := λ k, ⟨m ≫ k.1, by rw [assoc, k.2]⟩,
  left_inv :=
  begin
    rintro ⟨k, hk⟩,
    dsimp,
    congr' 1,
    rwa [closure.classifier, ← classify_postcompose_assoc, classify_inv],
  end,
  right_inv :=
  begin
    rintro ⟨k, hk⟩,
    dsimp,
    congr' 1,
    sorry,
  end }

def closed_class_equiv {B B' : C} (m : B' ⟶ B) [closure.dense j m] :
  (B ⟶ closed_classifier j) ≃ (B' ⟶ closed_classifier j) :=
(eq_equiv j B).trans ((eq_equiv j B').trans (closed_equiv j m)).symm

-- -- def closed_biject {A B : C} (m : A ⟶ B) [closure.dense j m] : (B ⟶ closed_classifier j) ≃ (A ⟶ closed_classifier j) :=
-- -- equiv.trans (eq_equiv j B) (equiv.trans (eq_equiv j A) (bijection j m)).symm

-- -- lemma closed_biject_prop {A B : C} (m : A ⟶ B) [closure.dense j m] (f' : B ⟶ closed_classifier j) : (closed_biject j m).to_fun f' = m ≫ f' :=
-- -- begin
-- --   dsimp [closed_biject, equiv.trans, equiv.symm, eq_equiv, bijection],
-- --   apply equalizer.hom_ext,
-- --   rw equalizer.lift_ι,
-- --   rw classify_pullback_obj,
-- --   rw ← classify_pullback,
-- --   have : 𝟙 _ = classifier_of (truth C),
-- --     apply has_subobject_classifier.uniquely _ _ ⟨𝟙 _, _, pullback_square_iso' (𝟙 _) (truth C) (truth C) (𝟙 _) _⟩,
-- --     rw [id_comp, comp_id],
-- --   rw [← this, comp_id, assoc],
-- -- end
-- -- lemma closed_biject_prop' {A B : C} (m : A ⟶ B) [closure.dense j m] (f' : A ⟶ closed_classifier j) : m ≫ (closed_biject j m).inv_fun f' = f' :=
-- -- begin
-- --   symmetry,
-- --   rw ← closed_biject_prop,
-- --   rw (closed_biject j m).right_inv,
-- -- end

def sheaf_classifier : sheaf j :=
sheaf.mk' (closed_classifier j) $ λ B B' m f' d, sorry

-- -- -- -- Define what it means for χ to classify the mono f.
-- -- -- structure classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) :=
-- -- -- (k : U ⟶ Ω₀)
-- -- -- (commutes : k ≫ true = f ≫ χ)
-- -- -- (forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
-- -- -- restate_axiom classifying.forms_pullback'


-- This is a super dodgy proof but oh well.
def forget_terminal_sheaf : (⊤_ (sheaf j)).A ≅ ⊤_ C :=
begin
  apply (cones.forget _).map_iso (lifted_limit_maps_to_original (limit.is_limit (functor.empty _ ⋙ forget j))) ≪≫ _,
  change limit (functor.empty (sheaf j) ⋙ forget j) ≅ ⊤_ C,
  have : functor.empty (sheaf j) ⋙ forget j = functor.empty _,
  refine category_theory.functor.ext _ _,
  simp, simp,
  rw this,
end

instance : has_subobject_classifier.{v} (sheaf j) :=
{ Ω := sheaf_classifier j,
  Ω₀ := ⊤_ _,
  truth :=
  begin
    apply (forget_terminal_sheaf j).hom ≫ _,
    apply equalizer.lift (default (⊤_ C ⟶ Ω₀ C) ≫ truth C) _,
    rw [assoc, comp_id, topology.ax1],
  end,
  truth_mono :=
  begin
    -- change mono ((forget_terminal_sheaf j).hom ≫ equalizer.lift (default (⊤_ C ⟶ Ω₀ C) ≫ truth C) _),
  end

}