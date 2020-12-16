import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflects_isomorphisms
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.terminal
import category_theory.adjunction.fully_faithful
import category_theory.closed.cartesian
import category.reflects
import equiv
import construction
import topos
import equalizers

namespace category_theory

open category_theory category_theory.category category_theory.limits
open classifier
noncomputable theory
universes v u u₂

variables {C : Type u} [category.{v} C] [topos C]

def indicators {B : C} (m : B ⟶ Ω C) (n : B ⟶ Ω C) : B ⟶ Ω C :=
classify (classification m ⊓ classification n)

def indicators_natural {B B' : C} (f : B' ⟶ B) (m : B ⟶ Ω C) (n : B ⟶ Ω C) :
  f ≫ indicators m n = indicators (f ≫ m) (f ≫ n) :=
begin
  dunfold indicators,
  rw [classification_natural_symm, classification_natural_symm, ← inf_pullback,
      classification.eq_symm_apply, classification_natural_symm, classification.apply_symm_apply],
end

variable (C)
def and_arrow : Ω C ⨯ Ω C ⟶ Ω C := indicators limits.prod.fst limits.prod.snd
variable {C}

@[reassoc]
lemma and_property {B : C} (m₁ m₂ : subq B) :
  prod.lift (classify m₁) (classify m₂) ≫ and_arrow C = classify (m₁ ⊓ m₂) :=
by rw [and_arrow, indicators_natural, prod.lift_fst, prod.lift_snd, indicators,
       classification.apply_symm_apply, classification.apply_symm_apply]

lemma leq_iff_comp_and {E : C} (m n : subq E) :
  m ≤ n ↔ prod.lift (classify m) (classify n) ≫ and_arrow C = classify m :=
by simp only [← inf_eq_left, and_property, ← classification.apply_eq_iff_eq, classification.apply_symm_apply]

lemma factors_iff_comp_and {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] :
  factors_through m₁ m₂ ↔ prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁ :=
leq_iff_comp_and ⟦sub.mk' m₁⟧ ⟦sub.mk' m₂⟧

@[reassoc] lemma classify_postcompose {A A' E : C} (n : A ⟶ A') (m : A' ⟶ E) [mono n] [mono m] :
  classifier_of n = m ≫ classifier_of (n ≫ m) :=
uniquely _ _ (left_right_hpb_to_both_hpb _ (top_iso_has_pullback_top _ n _ m (id_comp _)) (classifies (n ≫ m)))

lemma classify_self {E : C} : classifier_of (𝟙 E) = default (E ⟶ Ω₀ C) ≫ truth C :=
begin
  apply uniquely,
  apply left_iso_has_pullback_top (default (E ⟶ Ω₀ C)),
  rw id_comp
end

lemma classify_mk {A E : C} (m : A ⟶ E) [mono m] : classify ⟦sub.mk' m⟧ = classifier_of m := rfl

lemma classify_top (E : C) : classify ⊤ = default (E ⟶ Ω₀ C) ≫ truth C :=
classify_self

class topology (j : Ω C ⟶ Ω C) :=
(ax1 : truth C ≫ j = truth C)
(ax2 : j ≫ j = j)
(ax3 : and_arrow C ≫ j = limits.prod.map j j ≫ and_arrow C)

variables (j : Ω C ⟶ Ω C) [topology.{v} j]

namespace closure

variables {E A : C}

def obj (m : A ⟶ E) [mono m] : C := get_subobject_obj (classifier_of m ≫ j)
def arrow (m : A ⟶ E) [mono m] : get_subobject_obj (classifier_of m ≫ j) ⟶ E := get_subobject (classifier_of m ≫ j)
instance is_sub (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := category_theory.get_subobject_mono _
lemma classifier (m : A ⟶ E) [mono m] : classifier_of (arrow j m) = classifier_of m ≫ j :=
uniquely _ _ (has_pullback_top_of_pb)
def operator (m : subq E) : subq E := classification (classify m ≫ j)
def subobj (m : A ⟶ E) [mono m] : subq E := operator j ⟦sub.mk' m⟧
lemma classify_op : ∀ (m : subq E), classify (operator j m) = classify m ≫ j :=
quotient.ind $
begin
  intro a,
  exact classifier j _,
end
lemma classify (m : A ⟶ E) [mono m] : classify (subobj j m) = classify ⟦sub.mk' m⟧ ≫ j :=
classifier j m
lemma operator_idem (m : subq E) : operator j (operator j m) = operator j m :=
begin
  simp only [← classify_eq_iff_eq, classify_op, assoc, topology.ax2],
end

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

def closure_intersection {E : C} {m m' : subq E} : closure.operator j (m ⊓ m') = closure.operator j m ⊓ closure.operator j m' :=
by simp only [← classify_eq_iff_eq, closure.classify_op, ← and_property, ← prod.lift_map, assoc, topology.ax3]

def monotone {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (h : factors_through m n) :
  factors_through (arrow j m) (arrow j n) :=
begin
  rw [factors_iff_comp_and] at h,
  rw [factors_iff_comp_and, closure.classifier, closure.classifier, ← prod.lift_map, assoc,
      ← topology.ax3, reassoc_of h],
end
def mono_sub : ∀ {m n : subq E}, m ≤ n → operator j m ≤ operator j n :=
quotient.ind₂ $
begin
  intros a b h,
  apply monotone,
  cases h,
  refine ⟨over.hom_mk h.left (sub.w h)⟩,
end
lemma comm_pullback (m : subq E) (f : A ⟶ E) :
  (subq.pullback f).obj (operator j m) = operator j ((subq.pullback f).obj m) :=
by rw [← classify_eq_iff_eq, classify_pullback, classify_op, classify_op, classify_pullback, assoc]

class dense (m : A ⟶ E) extends mono.{v} m : Prop :=
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
(closure_eq_self : subobj j m = ⟦sub.mk' m⟧)

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
  have : ⟦sub.mk' l⟧ = (subq.pullback f).obj ⟦sub.mk' m⟧,
    apply quotient.sound,
    refine equiv_of_both_ways (sub.hom_mk _ (pullback.lift_snd _ _ comm)) (sub.hom_mk (lim.lift _) (lim.fac _ walking_cospan.right)),
  refine ⟨_⟩,
  rw [subobj, this, ← closure.comm_pullback],
  convert subq.pullback_top f,
  apply d.closure_eq_top,
end

instance dense_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [dense j g] : dense j (pullback.snd : pullback g f ⟶ X) :=
dense_of_pullback j pullback.condition (cone_is_pullback _ _)
instance dense_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [dense j g] : dense j (pullback.fst : pullback f g ⟶ X) :=
dense_of_pullback j pullback.condition.symm (pullback_cone.flip_is_limit (cone_is_pullback _ _))

def dense_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j f] : dense j t :=
dense_of_pullback _ comm.symm (pullback_flip lim)

def dense_of_iso {A₁ A₂ E : C} (m : A₁ ⟶ E) (i : A₁ ≅ A₂) [dense j m] : dense j (i.inv ≫ m) :=
{ closure_eq_top :=
  begin
    have : ⟦sub.mk' (i.inv ≫ m)⟧ = ⟦sub.mk' m⟧,
      apply quotient.sound,
      refine equiv_of_both_ways (sub.hom_mk i.inv rfl) (sub.hom_mk i.hom (i.hom_inv_id_assoc _)),
    rw [subobj, this],
    apply dense.closure_eq_top,
  end }

def closure_postcompose {A E₁ E₂ : C} (f : E₁ ⟶ E₂) [mono f] (m : A ⟶ E₁) [mono m] :
  classifier_of (closure.arrow j m : _ ⟶ E₁) = f ≫ classifier_of (closure.arrow j (m ≫ f)) :=
by rw [classifier, classifier, ← classify_postcompose_assoc]

def is_iso_of_dense_of_closed {A B : C} (f : A ⟶ B) [d : dense j f] [c : closed j f] : is_iso f :=
begin
  have := d.closure_eq_top,
  rw c.closure_eq_self at this,
  have : nonempty (⊤ ⟶ sub.mk' f),
    obtain ⟨⟨_, b, _, _⟩⟩ := quotient.exact this,
    refine ⟨b⟩,
  obtain ⟨r, hr⟩ := raised_factors this,
  refine ⟨r, _, hr⟩,
  rw [← cancel_mono f, assoc, hr], simp,
end

end closure

def lifting_square {A A' B B' : C} {f' : B' ⟶ A'} {m : A' ⟶ A} {n : B' ⟶ B} {f : B ⟶ A}
  (comm : f' ≫ m = n ≫ f) [d : closure.dense j n] [c : closure.closed j m] : {k // k ≫ m = f} :=
begin
  have : ⊤ ≤ (subq.pullback f).obj ⟦sub.mk' m⟧,
    rw [← d.closure_eq_top, ← c.closure_eq_self, closure.subobj, closure.subobj,
        closure.comm_pullback],
    apply closure.mono_sub,
    refine ⟨sub.hom_mk _ (pullback.lift_snd _ _ comm)⟩,
  obtain ⟨p, hp⟩ : {p : B ⟶ pullback m f // p ≫ pullback.snd = 𝟙 B } := raised_factors this,
  refine ⟨p ≫ pullback.fst, _⟩,
  rw [assoc, pullback.condition, reassoc_of hp],
end

instance dense_comp {E₁ E₂ E₃ : C} (m₁ : E₁ ⟶ E₂) (m₂ : E₂ ⟶ E₃) [closure.dense j m₁] [d : closure.dense j m₂] : closure.dense j (m₁ ≫ m₂) :=
{ closure_eq_top :=
 begin
  have : closure.less_than_closure j (m₁ ≫ m₂) ≫ closure.arrow j (m₁ ≫ m₂) = m₁ ≫ m₂ := closure.is_lt j (m₁ ≫ m₂),
  obtain ⟨r, hr⟩ := lifting_square j this,
  have : r ≫ closure.arrow j (m₁ ≫ m₂) = m₂ ≫ 𝟙 _,
    rw [hr, comp_id],
  obtain ⟨s, hs⟩ := lifting_square j this,
  rw eq_top_iff,
  refine ⟨sub.hom_mk s hs⟩,
end }

instance dense_prod_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) [closure.dense j f] [closure.dense j g] :
  closure.dense j (limits.prod.map f g) :=
begin
  have : closure.dense j (limits.prod.map f (𝟙 Y)) := closure.dense_of_pullback j _ (pullback_prod _ _),
  haveI : closure.dense j (limits.prod.map (𝟙 X) g) := closure.dense_of_pullback j _ (pullback_prod' _ _),
  have : limits.prod.map f g = limits.prod.map f (𝟙 Y) ≫ limits.prod.map (𝟙 X) g,
    apply prod.hom_ext; simp only [limits.prod.map_fst, limits.prod.map_snd, limits.prod.map_snd_assoc, assoc, comp_id, id_comp],
  rw this,
  apply_instance,
end

@[derive subsingleton]
def sheaf_condition (A : C) : Type (max u v) :=
Π ⦃B B'⦄ (m : B' ⟶ B) f' [closure.dense j m], unique {f : B ⟶ A // m ≫ f = f'}

def sheaf_condition.mk' (A : C) (h : Π ⦃B B'⦄ (m : B' ⟶ B) f' [closure.dense j m], {f : B ⟶ A // m ≫ f = f' ∧ ∀ a, m ≫ a = f' → a = f}) :
  sheaf_condition j A :=
begin
  introsI B B' m f' d,
  refine ⟨⟨⟨(h m f').1, (h m f').2.1⟩⟩, _⟩,
  rintro ⟨a, ha⟩,
  apply subtype.ext,
  apply (h m f').2.2 _ ha,
end

structure sheaf' : Type (max u v) :=
(A : C)
(unique_extend : sheaf_condition j A)

def forget_sheaf : sheaf'.{v} j → C := sheaf'.A

def sheaf := induced_category C (forget_sheaf j)

instance sheaf_category.category : category (sheaf j) := induced_category.category _
def sheaf.forget : sheaf j ⥤ C := induced_functor _

variables {j}

@[simps]
def sheaf.mk (A : C) (h : sheaf_condition j A) : sheaf j :=
{ A := A,
  unique_extend := h }

@[reducible]
def sheaf.mk' (A : C) (h : Π ⦃B B'⦄ (m : B' ⟶ B) f' [closure.dense j m], {f : B ⟶ A // m ≫ f = f' ∧ ∀ a, m ≫ a = f' → a = f}) : sheaf j :=
sheaf.mk A (sheaf_condition.mk' j A h)

def sheaf.A (A : sheaf j) : C := (sheaf.forget j).obj A

def sheaf.hom_mk (A B : sheaf j) (f : A.A ⟶ B.A) : A ⟶ B := f

def get_condition (A : sheaf j) : sheaf_condition j A.A := A.2

def unique_extend (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : unique {f // m ≫ f = f'} :=
(A.unique_extend m f')

def extend_map' (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : {f // m ≫ f = f'} :=
(A.unique_extend m f').1.1

def extend_map (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : B ⟶ A.A :=
(extend_map' A m f').1

@[reassoc] lemma extend_map_prop (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A) : m ≫ extend_map A m f' = f' :=
(extend_map' A m f').2

lemma unique_extension (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A)
  (f : B ⟶ A.A) (h : m ≫ f = f') :
f = extend_map A m f' :=
congr_arg subtype.val ((A.unique_extend m f').2 ⟨f, h⟩)

def unique_ext (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f' : B' ⟶ A.A)
  (f₁ f₂ : B ⟶ A.A) (h₁ : m ≫ f₁ = f') (h₂ : m ≫ f₂ = f') :
  f₁ = f₂ :=
(unique_extension A m f' f₁ h₁).trans (unique_extension A m f' f₂ h₂).symm

def cancel_dense (A : sheaf j) {B B' : C} (m : B' ⟶ B) [closure.dense j m]
  (f₁ f₂ : B ⟶ A.A) (h : m ≫ f₁ = m ≫ f₂) :
  f₁ = f₂ :=
unique_ext A m (m ≫ f₂) f₁ f₂ h rfl

instance sheaf_forget_full : full (sheaf.forget j) := induced_category.full _
instance sheaf_forget_faithful : faithful (sheaf.forget j) := induced_category.faithful _
instance sheaf_forget_reflects_limits : reflects_limits (sheaf.forget j) := by apply_instance

attribute [irreducible] sheaf

namespace construct_limits

variables {C} {J : Type v} [𝒥₁ : small_category J] {K : J ⥤ sheaf j} {c : cone (K ⋙ sheaf.forget j)} (t : is_limit c)
variables {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ c.X)

@[simps]
def alt_cone [closure.dense j m] : cone (K ⋙ sheaf.forget j) :=
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

instance sheaf_forget_creates_limits : creates_limits (sheaf.forget j) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X := sheaf.mk' c.X $
          λ B B' m f' d, by exactI
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

variables (j)

def sheaf_has_finite_limits : has_finite_limits.{v} (sheaf j) :=
λ J 𝒥₁ 𝒥₂, by exactI
{ has_limit := λ F, has_limit_of_created F (sheaf.forget j) }

local attribute [instance, priority 10] sheaf_has_finite_limits

-- def iso_limit (J : Type v) [small_category J] [fin_category J] (F : J ⥤ sheaf j) : (sheaf.forget j).obj (limit F) ≅ limit (F ⋙ sheaf.forget j) :=
-- by apply (cones.forget (F ⋙ sheaf.forget j)).map_iso (lifted_limit_maps_to_original (limit.is_limit (F ⋙ sheaf.forget j)))

def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
  closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
closure.dense_of_pullback j _ (pullback_prod' m A)

local attribute [instance] has_finite_products_of_has_finite_limits

def sheaf_exponential (A : C) (s : sheaf j) : sheaf j :=
sheaf.mk' (A ⟹ s.A) $ λ B B' m f' d,
begin
  haveI := d,
  haveI := dense_prod_map_id j A m,
  refine ⟨cartesian_closed.curry _, _, _⟩,
  { exact extend_map s (limits.prod.map (𝟙 A) m) (cartesian_closed.uncurry f') },
  { rw [← curry_natural_left, extend_map_prop s, curry_uncurry] },
  { rintro a ha,
    rw eq_curry_iff,
    apply unique_extension s,
    rw [← uncurry_natural_left, ha] }
end

instance sheaf_cc : cartesian_closed (sheaf j) :=
{ closed := λ A,
  { is_adj :=
    { right :=
      { obj := λ s, sheaf_exponential j A.A s,
        map := λ s₁ s₂ f, (exp A.A).map f,
        map_id' := λ s, (exp A.A).map_id _,
        map_comp' := λ _ _ _ _ _, (exp A.A).map_comp _ _ },
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ X Y,
        { to_fun := λ f, cartesian_closed.curry (inv (prod_comparison (sheaf.forget j) A X) ≫ f),
          inv_fun := λ g, by apply (prod_comparison (sheaf.forget j) A X) ≫ cartesian_closed.uncurry g,
          left_inv := λ f, by simp,
          right_inv := λ g, by simp },
        hom_equiv_naturality_left_symm' :=
        begin
          intros X' X Y f g,
          dsimp,
          conv_lhs {congr, skip, erw uncurry_natural_left },
          apply (prod_comparison_natural_assoc (sheaf.forget j) (𝟙 A) f _).symm,
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
  refine ⟨quotient.sound (equiv_of_both_ways (sub.hom_mk r this) (sub.hom_mk (closure.less_than_closure j m) (closure.is_lt j m)))⟩,
end

def closed_classifier : C := equalizer j (𝟙 _)

def eq_equiv (B : C) : (B ⟶ closed_classifier j) ≃ {cm : B ⟶ Ω C // cm ≫ j = cm} :=
{ to_fun := λ f, ⟨f ≫ equalizer.ι _ _, by simp [equalizer.condition]⟩,
  inv_fun := λ f, equalizer.lift f.1 (by rw [f.2, comp_id]),
  left_inv := λ f, equalizer.hom_ext (equalizer.lift_ι _ _),
  right_inv := λ ⟨f, hf⟩, subtype.eq (equalizer.lift_ι _ _) }

def action {B B' : C} (m : B' ⟶ B) [d : closure.dense j m] :
  {n' : subq B // closure.operator j n' = n'} ≃ {n : subq B' // closure.operator j n = n} :=
{ to_fun :=
  begin
    intro n,
    refine ⟨(subq.pullback m).obj n.1, _⟩,
    rw [← closure.comm_pullback, n.2],
  end,
  inv_fun := λ n, ⟨closure.operator j ((subq.post m).obj n.1), closure.operator_idem j _⟩,
  left_inv :=
  begin
    rintro ⟨n, hn⟩,
    dsimp,
    congr' 1,
    have : _ = (subq.post m).obj ((subq.pullback m).obj _) := subq.inf_eq_post_pull (sub.mk' m) n,
    rw ← this,
    rw closure.closure_intersection,
    rw hn,
    change closure.subobj j _ ⊓ n = _,
    rw d.closure_eq_top,
    exact top_inf_eq,
  end,
  right_inv :=
  begin
    rintro ⟨n, hn⟩,
    dsimp,
    congr' 1,
    rwa [closure.comm_pullback, subq.pull_post_self],
  end }

def closure_equiv {B : C} : {cB : B ⟶ Ω C // cB ≫ j = cB} ≃ {n : subq B // closure.operator j n = n} :=
begin
  apply classification.subtype_congr,
  intro a,
  rw ← classify_eq_iff_eq,
  rw closure.classify_op,
  change _ ↔ classification.symm _ ≫ _ = classification.symm _,
  rw classification.symm_apply_apply,
end

def closed_equiv {B B' : C} (m : B' ⟶ B) [closure.dense j m] : {cB : B ⟶ Ω C // cB ≫ j = cB} ≃ {cB : B' ⟶ Ω C // cB ≫ j = cB} :=
(closure_equiv j).trans ((action j m).trans (closure_equiv j).symm)

def closed_class_equiv {B B' : C} (m : B' ⟶ B) [closure.dense j m] :
  (B ⟶ closed_classifier j) ≃ (B' ⟶ closed_classifier j) :=
(eq_equiv j B).trans ((closed_equiv j m).trans (eq_equiv j B').symm)

lemma closed_class_equiv_forward {B B' : C} (m : B' ⟶ B) [closure.dense j m] (f : B ⟶ closed_classifier j) :
  m ≫ f = closed_class_equiv j m f :=
begin
  sorry
  -- dsimp [closed_class_equiv, eq_equiv, closed_equiv, action, closure_equiv, equiv.subtype_congr],
  -- ext1,
  -- rw equalizer.lift_ι,
  -- change _ = quotient.lift _ _ (quotient.mk _),
  -- dsimp,
  -- change _ = classifier_of ((sub.pullback m).obj (sub.mk' (get_subobject (f ≫ equalizer.ι j (𝟙 (Ω C)))))),

  -- change _ = classify ((subq.pullback m).obj ⟦_⟧),
  -- sorry,
  -- dsimp [cl]
  -- change _ = classify _,
  -- rw classify_pullback,

  -- simp [closed_class_equiv, eq_equiv, closed_equiv, action, closure_equiv, equiv.subtype_congr],
  -- ext1,
  -- rw equalizer.lift_ι,
  -- change _ = classify _,
  -- rw classify_pullback,
  -- change _ = m ≫ classification.symm (classification _),
  -- rw classification.symm_apply_apply,
  -- rw [assoc], refl,
end

def sheaf_classifier : sheaf j :=
sheaf.mk' (closed_classifier j) $ λ B B' m f' d, by exactI
begin
  refine ⟨(closed_class_equiv j m).symm f', _, _⟩,
  rw [closed_class_equiv_forward, equiv.apply_symm_apply],
  intros a ha,
  rwa [(closed_class_equiv j m).eq_symm_apply, ← closed_class_equiv_forward],
end

def forget_terminal_sheaf : (⊤_ (sheaf j)).A ≅ ⊤_ C :=
preserves_terminal.iso (sheaf.forget j)

def sheaf_classify {U X : C} (f : U ⟶ X) [closure.closed j f] : X ⟶ closed_classifier j :=
equalizer.lift (classifier_of f) (by rw [comp_id, closure.classifier_eq_of_closed])

def sheaf_truth : (⊤_ (sheaf j)).A ⟶ closed_classifier j :=
(forget_terminal_sheaf j).hom ≫ equalizer.lift (default _ ≫ truth C) (by rw [assoc, comp_id, topology.ax1])

def sheaf_hpb {U X : C} (f : U ⟶ X) [closure.closed j f] :
  has_pullback_top f (sheaf_classify j f) (sheaf_truth j) :=
begin
  apply right_both_hpb_to_left_hpb (truth C) (equalizer.ι _ _),
  rw [sheaf_classify, equalizer.lift_ι],
  apply classifies,
  refine top_iso_has_pullback_top _ _ _ _ _,
  apply (forget_terminal_sheaf j).hom ≫ (default (⊤_ C ⟶ Ω₀ C)),
  haveI : is_iso (default (⊤_ C ⟶ Ω₀ C)) := ⟨default _, subsingleton.elim _ _, subsingleton.elim _ _⟩,
  apply_instance,
  rw [sheaf_truth, assoc, assoc, equalizer.lift_ι],
end

def sheaf_has_subobj_classifier : has_subobject_classifier.{v} (sheaf j) :=
{ Ω := sheaf_classifier j,
  Ω₀ := ⊤_ _,
  truth :=
  begin
    apply (forget_terminal_sheaf j).hom ≫ _,
    apply equalizer.lift (default (⊤_ C ⟶ Ω₀ C) ≫ truth C) _,
    rw [assoc, comp_id, topology.ax1],
  end,
  truth_mono := ⟨λ Z g h eq, subsingleton.elim _ _⟩,
  is_subobj_classifier :=
  { classifier_of := λ U X f hf, by exactI
    begin
      haveI := preserves_mono_of_preserves_pullback (sheaf.forget j) _ _ f,
      haveI := closed_of_subsheaf j X U ((sheaf.forget j).map f),
      apply (sheaf.forget j).preimage,
      apply sheaf_classify j ((sheaf.forget j).map f),
    end,
    classifies' := λ U X f hf,
    begin
      apply fully_faithful_reflects_hpb (sheaf.forget j),
      apply sheaf_hpb,
    end,
    uniquely' := λ U X f hf χ hχ,
    begin
      apply (sheaf.forget j).map_injective,
      rw [functor.image_preimage],
      rw ← cancel_mono (equalizer.ι j (𝟙 _)),
      rw [sheaf_classify, equalizer.lift_ι],
      apply uniquely,
      apply left_right_hpb_to_both_hpb _ (preserves_hpb (sheaf.forget j) hχ),
      refine top_iso_has_pullback_top _ _ _ _ _,
      apply (forget_terminal_sheaf j).hom ≫ (default (⊤_ C ⟶ Ω₀ C)),
      haveI : is_iso (default (⊤_ C ⟶ Ω₀ C)) := ⟨default _, subsingleton.elim _ _, subsingleton.elim _ _⟩,
      apply_instance,
      change _ = (_ ≫ _) ≫ _,
      rw [assoc, assoc, equalizer.lift_ι],
    end } }

/-- The topos of sheaves! -/
instance : topos.{v} (sheaf j) := { sub := sheaf_has_subobj_classifier j }

section close_equiv
variables {R A : C} (rel : relation.{v} R A)

abbreviation close_relation [mono rel] : relation.{v} (closure.obj j rel) A := closure.arrow j rel

instance close_rel_refl [mono rel] [reflexive rel] : reflexive (close_relation j rel) :=
{ r := reflexive.r rel ≫ closure.less_than_closure j _,
  cancel_a := by rw [assoc, closure.is_lt_assoc, reflexive.cancel_a],
  cancel_b := by rw [assoc, closure.is_lt_assoc, reflexive.cancel_b] }

def symmetric_of_swap_eq_self [mono rel] (h : classifier_of rel = classifier_of (rel ≫ (limits.prod.braiding _ _).hom)) :
  symmetric rel :=
begin
  have : (how_inj_is_classifier _ _ h).hom ≫ _ = _ := c_very_inj h,
  have eq : prod.lift rel.a rel.b ≫ (limits.prod.braiding A A).hom = prod.lift rel.b rel.a,
    apply prod.hom_ext; simp,

  refine ⟨(how_inj_is_classifier _ _ h).hom, _, _⟩,
  have := (c_very_inj h) =≫ limits.prod.snd,
    simp only [prod.lift_fst, assoc, prod.lift_snd, prod.braiding_hom] at this,
  exact this,
  have := (c_very_inj h) =≫ limits.prod.fst,
    simp only [prod.lift_fst, assoc, prod.lift_snd, prod.braiding_hom] at this,
  exact this,
end
def swap_eq_self_of_symmetric [mono rel] [symmetric rel] :
  classifier_of rel = classifier_of (rel ≫ (limits.prod.braiding _ _).inv) :=
begin
  apply class_lift_of_iso ⟨symmetric.s rel, symmetric.s rel, symmetric_idem rel, symmetric_idem rel⟩,
  dsimp, rw symmetric_pair_assoc rel,
  apply prod.hom_ext; simp,
end

instance close_rel_symm [mono rel] [symmetric rel] : symmetric (close_relation j rel) :=
begin
  apply symmetric_of_swap_eq_self,
  have := classify_postcompose (closure.arrow j rel) (limits.prod.braiding _ _).hom,
  rw ← cancel_epi (limits.prod.braiding A A).hom,
  erw ← this,
  rw closure.classifier,
  have := classify_postcompose rel (limits.prod.braiding _ _).inv,
  conv_lhs {rw this},
  rw [assoc, (limits.prod.braiding A A).hom_inv_id_assoc],
  rw ← swap_eq_self_of_symmetric,
end

end close_equiv

def equality (A : C) : relation A A := relation.of_pair (𝟙 A) (𝟙 A)
instance equality_mono {A : C} : mono (equality A) := category_theory.mono_prod_lift_of_left _ _

def equality_sub (A : C) : subq (A ⨯ A) := subq.mk (equality A)

def j_equal (A : C) : relation (closure.obj j (equality A)) A := close_relation j (equality A)
instance j_equal_mono (A : C) : mono (j_equal j A) := closure.is_sub j _
def j_equal_sub (A : C) : subq (A ⨯ A) := subq.mk (j_equal j A)

lemma j_equal_sub_eq (A : C) : j_equal_sub j A = closure.operator j (equality_sub A) := rfl

section
-- Prove that if x' = x and R(x, y) then R(x', y)
variables {A B R : C} (r : R ⟶ A ⨯ B)

def x'_eq_x (A B) : C := pullback (equality A) (limits.prod.fst : A ⨯ A ⨯ B ⟶ A ⨯ A)
def x'_eq_x_arrow (A B : C) : x'_eq_x A B ⟶ A ⨯ A ⨯ B := pullback.snd
instance x'_eq_x_mono [mono r] : mono (x'_eq_x_arrow A B) := pullback.snd_of_mono

def Rxy : C := pullback r (limits.prod.map limits.prod.snd (𝟙 B) : A ⨯ A ⨯ B ⟶ A ⨯ B)

def Rx'y : C := pullback r (limits.prod.map limits.prod.fst (𝟙 B) : A ⨯ A ⨯ B ⟶ A ⨯ B)

def Rxy_arrow : Rxy r ⟶ A ⨯ A ⨯ B := pullback.snd
instance Rxy_mono [mono r] : mono (Rxy_arrow r) := pullback.snd_of_mono
def Rx'y_arrow : Rx'y r ⟶ A ⨯ A ⨯ B := pullback.snd
instance Rx'y_mono [mono r] : mono (Rx'y_arrow r) := pullback.snd_of_mono
def x'_eq_x_and_Rxy : C := pullback (x'_eq_x_arrow A B) (Rxy_arrow r)
def x'_eq_x_and_Rxy_arrow : x'_eq_x_and_Rxy r ⟶ A ⨯ A ⨯ B := pullback.snd ≫ Rxy_arrow r
instance x'_eq_x_and_Rxy_mono [mono r] : mono (x'_eq_x_and_Rxy_arrow r) := mono_comp _ _

def x'_eq_x_sub (A B : C) : subq (A ⨯ A ⨯ B) := (subq.pullback (limits.prod.fst : A ⨯ A ⨯ B ⟶ A ⨯ A)).obj (equality_sub A)
def R_sub [mono r] : subq (A ⨯ B) := subq.mk r
def Rxy_sub [mono r] : subq (A ⨯ A ⨯ B) := (subq.pullback (limits.prod.map limits.prod.snd (𝟙 B) : A ⨯ A ⨯ B ⟶ A ⨯ B)).obj (R_sub r)
def Rx'y_sub [mono r] : subq (A ⨯ A ⨯ B) := (subq.pullback (limits.prod.map limits.prod.fst (𝟙 B) : A ⨯ A ⨯ B ⟶ A ⨯ B)).obj (R_sub r)

lemma x'_eq_x_prop : x'_eq_x_arrow A B ≫ limits.prod.fst ≫ limits.prod.fst = x'_eq_x_arrow A B ≫ limits.prod.fst ≫ limits.prod.snd :=
begin
  have : pullback.fst ≫ (prod.lift (𝟙 A) (𝟙 A)) = x'_eq_x_arrow A B ≫ _ := pullback.condition,
    rw [← reassoc_of this, ← reassoc_of this],
  simp,
end

lemma factors : factors_through (x'_eq_x_and_Rxy_arrow r) (Rx'y_arrow r) :=
begin
  refine ⟨over.hom_mk _ (pullback.lift_snd (pullback.snd ≫ pullback.fst) _ _)⟩,
  rw x'_eq_x_and_Rxy_arrow,
  apply prod.hom_ext,
  { rw [assoc, assoc, assoc, limits.prod.map_fst, ← pullback.condition, over.mk_hom, assoc,
        x'_eq_x_prop, pullback.condition_assoc, limits.prod.map_fst, pullback.condition_assoc],
        refl },
  { simpa only [limits.prod.map_snd, pullback.condition, assoc, over.mk_hom] },
end

lemma factors_sub [mono r] : x'_eq_x_sub A B ⊓ Rxy_sub r ≤ Rx'y_sub r :=
begin
  rw inf_comm,
  exact factors r,
end

lemma closure_factors_sub [c : closure.closed j r] :
  (subq.pullback limits.prod.fst).obj (j_equal_sub j A) ⊓ Rxy_sub r ≤ Rx'y_sub r :=
begin
  have := closure.mono_sub j (factors_sub r),
    rw [closure.closure_intersection, Rxy_sub, Rx'y_sub, x'_eq_x_sub,
        ← closure.comm_pullback, ← closure.comm_pullback, ← closure.comm_pullback] at this,
  have r_closed : closure.operator j (R_sub r) = R_sub r := c.closure_eq_self,
  rw r_closed at this,
  exact this
end

end

section
open category_theory.limits.prod

variables {A R : C} (r : relation R A)

def transitive_of_pair (t : triples r ⟶ R) (ht : t ≫ r = prod.lift (p r ≫ r.a) (q r ≫ r.b)) : transitive r :=
{ t := t,
  w₁ := by simpa using ht =≫ limits.prod.fst,
  w₂ := by simpa using ht =≫ limits.prod.snd }

def transitive_of_factors_sub [mono r]
  (fac : (subq.pullback fst).obj (subq.mk r) ⊓ (subq.pullback (map snd (𝟙 _))).obj (subq.mk r) ≤ (subq.pullback (map fst (𝟙 _))).obj (subq.mk r)) :
  transitive r :=
begin
  obtain ⟨t, ht⟩ : {t : pullback pullback.snd pullback.snd ⟶ pullback r _ // t ≫ pullback.snd = pullback.snd ≫ pullback.snd} :=
    raised_factors fac,
  let big : triples r ⟶ A ⨯ A ⨯ A,
    apply prod.lift (prod.lift (p r ≫ r.a) (q r ≫ r.a)) (q r ≫ r.b),
  fapply transitive_of_pair,
  apply pullback.lift (pullback.lift (q r) big _) (pullback.lift (p r) big _) _ ≫ t ≫ pullback.fst,
  { rw [prod.lift_map, comp_id, prod.lift_snd],
    apply prod.hom_ext; simp },
  { rw prod.lift_fst,
    apply prod.hom_ext,
    { simp },
    { rw [lift_snd, ← consistent r, assoc], refl } },
  { simp },
  { simp only [assoc],
    rw [pullback.condition, reassoc_of ht, pullback.lift_snd_assoc, pullback.lift_snd_assoc, lift_map, comp_id],
    apply prod.hom_ext; simp }
end

end

instance eq_reflexive (A : C) : reflexive.{v} (equality A) :=
{ r := 𝟙 A,
  cancel_a := by simp [equality],
  cancel_b := by simp [equality] }

instance eq_symmetric (A : C) : symmetric.{v} (equality A) :=
{ s := 𝟙 A,
  w₁ := by simp [equality],
  w₂ := by simp [equality] }

instance j_eq_reflexive (A : C) : reflexive (j_equal j A) :=
category_theory.close_rel_refl j (equality A)

instance j_eq_symmetric (A : C) : symmetric (j_equal j A) :=
category_theory.close_rel_symm j (equality A)

instance j_eq_transitive (A : C) : transitive (j_equal j A) :=
begin
  apply transitive_of_factors_sub,
  apply closure_factors_sub _ _,
  rw j_equal,
  apply_instance,
end

def j_eq_kernel_pair (A : C) : is_kernel_pair (named (j_equal j A)) (j_equal j A).a (j_equal j A).b :=
equiv_to_kernel_pair (j_equal j A)

def sub_kernel_pair {X Y Z W : C} (a b : X ⟶ Y) (f₁ : Y ⟶ Z) (f₂ : Z ⟶ W) (comm : a ≫ f₁ = b ≫ f₁)
  (big_kernel_pair : is_limit (pullback_cone.mk a b (by rw reassoc_of comm) : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂))) :
is_limit (pullback_cone.mk a b comm) :=
is_limit.mk' _
begin
  intro s,
  let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) := pullback_cone.mk s.fst s.snd (s.condition_assoc _),
  refine ⟨big_kernel_pair.lift s', big_kernel_pair.fac _ walking_cospan.left, big_kernel_pair.fac _ walking_cospan.right, λ m m₁ m₂, _⟩,
  apply big_kernel_pair.hom_ext,
  refine ((pullback_cone.mk a b _) : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _,
  erw m₁,
  symmetry,
  apply big_kernel_pair.fac _ walking_cospan.left,
  erw m₂,
  symmetry,
  apply big_kernel_pair.fac _ walking_cospan.right,
end

def Pj (A : C) : sheaf j := sheaf_exponential j A (sheaf_classifier j)

def named_factors (A : C) : {hat : A ⟶ (Pj j A).A // hat ≫ (exp _).map (equalizer.ι _ _) = named (j_equal j A)} :=
begin
  refine ⟨cartesian_closed.curry (equalizer.lift ((limits.prod.braiding A A).inv ≫ classifier_of (j_equal j A)) _), _⟩,
  { rw [assoc, comp_id, closure.classifier_eq_of_closed _ _],
    rw j_equal,
    apply_instance },
  { erw [← curry_natural_right, equalizer.lift_ι, curry_eq_iff, named, uncurry_curry] },
end

-- def regular_epi_is_coequalizer_of_kernel_pair {A B Y : C} (e : A ⟶ B) [he : regular_epi e] (h k : Y ⟶ A)
--   (comm : h ≫ e = k ≫ e) (l : is_limit (pullback_cone.mk _ _ comm)) :
--   is_colimit (cofork.of_π e comm) :=
-- begin
--   let t := l.lift (pullback_cone.mk _ _ he.w),
--   have ht : t ≫ h = he.left := l.fac _ walking_cospan.left,
--   have kt : t ≫ k = he.right := l.fac _ walking_cospan.right,
--   apply cofork.is_colimit.mk _ _ _ _,
--   { intro s,
--     apply (cofork.is_colimit.desc' he.is_colimit s.π _).1,
--     rw [← ht, assoc, s.condition, reassoc_of kt] },
--   { intro s,
--     apply (cofork.is_colimit.desc' he.is_colimit s.π _).2 },
--   { intros s m w,
--     apply he.is_colimit.hom_ext,
--     rintro ⟨⟩,
--     change (he.left ≫ e) ≫ m = (he.left ≫ e) ≫ _,
--     rw [assoc, assoc],
--     congr' 1,
--     erw (cofork.is_colimit.desc' he.is_colimit s.π _).2,
--     apply w walking_parallel_pair.one,
--     erw (cofork.is_colimit.desc' he.is_colimit s.π _).2,
--     apply w walking_parallel_pair.one }
-- end

instance mono_post_of_mono {A X Y : C} (f : X ⟶ Y) [mono f] : mono ((exp A).map f) :=
⟨λ Z g h eq, by rw [← uncurry_injective.eq_iff, ← cancel_mono f, ← uncurry_natural_right, ← uncurry_natural_right, eq]⟩

-- local attribute [instance] limits.has_coequalizers_of_has_finite_colimits

def tag' (n : ℕ) (A B : C) (f : A ⟶ B) := f
set_option pp.implicit false

-- lemma pullback_image_fac {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [has_coequalizers.{v} C] :
--   (pullback_image f g).hom ≫ image.ι (pullback.snd : pullback g f ⟶ Y) = (pullback.snd : pullback (image.ι g) f ⟶ Y) :=
-- is_image.lift_fac _ _

-- lemma pullback_image_inv_fac {X Y Z : C} (f : Y ⟶ Z) (g : X ⟶ Z) [has_coequalizers.{v} C] :
--   (pullback_image f g).inv ≫ (pullback.snd : pullback (image.ι g) f ⟶ Y) = image.ι (pullback.snd : pullback g f ⟶ Y) :=
-- image.lift_fac _

def dense_image_pullback_of_dense_image {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [closure.dense j (image.ι g)] :
  closure.dense j (image.ι (pullback.snd : pullback g f ⟶ X)) :=
begin
  rw ← pullback_image_inv_fac f g,
  apply closure.dense_of_iso _ _ _,
  apply closure.dense_pullback,
end

lemma cancel_dense_image {P X : C} (Y : sheaf j) (r : P ⟶ X) (u v : X ⟶ Y.A) [closure.dense j (image.ι r)] :
  r ≫ u = r ≫ v → u = v :=
begin
  intro eq,
  rw [← image.fac r, assoc, assoc, cancel_epi (factor_thru_image r)] at eq,
  apply cancel_dense Y _ _ _ eq,
end

def M (A : C) : C := image (named_factors j A).1
def M_sub (A : C) : M j A ⟶ (Pj j A).A := image.ι _
instance M_sub_mono (A : C) : mono (M_sub j A) :=
begin
  rw [M_sub],
  apply_instance
end

def L' (A : C) : C := closure.obj j (M_sub j A)
-- Sheafification!
def L (A : C) : sheaf j := subobject_of_closed_sheaf j (Pj j A) (L' j A) (closure.arrow j (M_sub j A))

def main_kernel_pair (A : C) :
  is_kernel_pair (factor_thru_image (named_factors j A).1) (j_equal j A).a (j_equal j A).b :=
begin
  have := j_eq_kernel_pair j A,
  rw [← (named_factors j A).2, ← image.fac (named_factors j A).1, assoc] at this,
  apply this.cancel_right_of_mono,
end

def main_coequalizer (A : C) : is_colimit (cofork.of_π (factor_thru_image (named_factors j A).val) (main_kernel_pair j A).comm) :=
is_kernel_pair.to_coequalizer _

@[simps]
def equivalate (A : C) (B : sheaf j) : (L j A ⟶ B) ≃ (A ⟶ (sheaf.forget j).obj B) :=
{ to_fun := λ f, factor_thru_image (named_factors j A).1 ≫ closure.less_than_closure j _ ≫ f,
  inv_fun := λ f,
  begin
    have : (j_equal j A).a ≫ f = (j_equal j A).b ≫ f,
      refine unique_ext B (closure.less_than_closure j (equality A)) f _ _ _ _;
      simp [j_equal, closure.is_lt_assoc, equality, relation.of_pair],
    let q : M j A ⟶ B.A := (cofork.is_colimit.desc' (main_coequalizer j A) f this).1,
    exact extend_map B (closure.less_than_closure j (M_sub j A)) q,
  end,
  left_inv := λ f,
  begin
    symmetry,
    apply unique_extension,
    apply @epi.left_cancellation _ _ _ _ (factor_thru_image (named_factors j A).val),
    symmetry,
    apply (cofork.is_colimit.desc' (main_coequalizer j A) _ _).2
  end,
  right_inv := λ f,
  begin
    dsimp,
    conv_lhs {congr, skip, apply_congr extend_map_prop},
    apply (cofork.is_colimit.desc' (main_coequalizer j A) _ _).2
  end }

def sheafification : C ⥤ sheaf j :=
begin
  apply adjunction.left_adjoint_of_equiv (equivalate j),
  intros A B B' g h,
  dsimp [equivalate],
  rw [assoc, assoc], refl,
end

def sheafification_is_adjoint : sheafification j ⊣ sheaf.forget j :=
adjunction.adjunction_of_equiv_left _ _

def sheafy_unit (A : C) :
  (sheafification_is_adjoint j).unit.app A = factor_thru_image (named_factors j A).1 ≫ closure.less_than_closure j _ :=
begin
  dsimp [sheafification_is_adjoint, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv, equivalate],
  erw comp_id,
end

def kernel_pair_unit (A : C) :
  is_kernel_pair ((sheafification_is_adjoint j).unit.app A) (j_equal j A).a (j_equal j A).b :=
begin
  rw sheafy_unit,
  apply is_kernel_pair.comp_of_mono,
  apply main_kernel_pair
end

def image_unit (A : C) : image ((sheafification_is_adjoint j).unit.app A) ≅ M j A :=
begin
  symmetry,
  apply unique_factorise _ _ (factor_thru_image _) (closure.less_than_closure j (M_sub j A)) _,
  rw sheafy_unit,
end

instance unit_has_dense_image {A : C} : closure.dense j (image.ι ((sheafification_is_adjoint j).unit.app A)) :=
begin
  set η := (sheafification_is_adjoint j).unit,
  have : (image_unit j A).hom ≫ closure.less_than_closure j (M_sub j A) = image.ι (η.app A),
    apply unique_factorise_inv_comp_mono,
  rw ← this,
  apply closure.dense_of_iso,
end

@[simps]
def prod_iso {X₁ X₂ Y₁ Y₂ : C} (hX : X₁ ≅ X₂) (hY : Y₁ ≅ Y₂) : X₁ ⨯ Y₁ ≅ X₂ ⨯ Y₂ :=
{ hom := limits.prod.map hX.hom hY.hom,
  inv := limits.prod.map hX.inv hY.inv }

instance forget_adj : is_right_adjoint (sheaf.forget j) :=
{ left := sheafification j,
  adj := adjunction.adjunction_of_equiv_left _ _ }

instance : reflective (sheaf.forget j) := {}.

def sheafification_preserves_terminal : preserves_limits_of_shape (discrete pempty) (sheafification j) :=
{ preserves_limit := λ K,
  begin
    haveI := nat_iso.is_iso_app_of_is_iso (sheafification_is_adjoint j).counit,
    apply preserves_limit_of_iso_diagram _ (functor.unique_from_empty _).symm,
    apply preserves_limit_of_preserves_limit_cone (limit.is_limit (functor.empty C)),
    have i : (sheafification j).obj (⊤_ C) ≅ (⊤_ sheaf j),
      apply functor.map_iso (sheafification j) (forget_terminal_sheaf j).symm ≪≫ (as_iso ((sheafification_is_adjoint j).counit.app _)),
    refine ⟨λ s, default _ ≫ i.inv, λ s, _, λ s m w, _⟩,
    rintro ⟨⟩,
    rw iso.eq_comp_inv,
    apply subsingleton.elim,
  end }.

instance : exponential_ideal (sheaf.forget j) :=
exponential_ideal_of (sheaf.forget j)
begin
  intros A B,
  apply in_subcategory_of_has_iso _ (sheaf_exponential _ A B),
  apply iso.refl _,
end

def sheafification_preserves_finite_products (J : Type v) [fintype J] [decidable_eq J] :
  preserves_limits_of_shape (discrete J) (sheafification j) :=
begin
  apply preserves_finite_products_of_preserves_binary_and_terminal _,
  apply preserves_binary_products_of_exponential_ideal (sheaf.forget j),
  apply sheafification_preserves_terminal,
  apply_instance,
  apply_instance
end

namespace preserve_equalizers

def aux (A : C) : closure.dense j (image.ι (limits.prod.map ((sheafification_is_adjoint j).unit.app A) ((sheafification_is_adjoint j).unit.app A))) :=
begin
  set η := (sheafification_is_adjoint j).unit,
  let i : image (limits.prod.map (η.app A) (η.app A)) ≅ M j A ⨯ M j A := image_prod_map (η.app A) _ ≪≫ prod_iso (image_unit j A) (image_unit j A),
  have : image.ι (limits.prod.map (η.app A) (η.app A)) = i.hom ≫ limits.prod.map (closure.less_than_closure j (M_sub j A)) (closure.less_than_closure j (M_sub j A)),
    change _ = (_ ≫ _) ≫ _,
    dsimp [prod_iso_hom],
    rw [assoc],
    have : limits.prod.map (image_unit j A).hom (image_unit j A).hom ≫ limits.prod.map (closure.less_than_closure j (M_sub j A)) (closure.less_than_closure j (M_sub j A)) =
            limits.prod.map ((image_unit j A).hom ≫ closure.less_than_closure j (M_sub j A)) ((image_unit j A).hom ≫ closure.less_than_closure j (M_sub j A)),
      apply prod.hom_ext,
      rw [assoc, limits.prod.map_fst, limits.prod.map_fst, limits.prod.map_fst_assoc],
      rw [assoc, limits.prod.map_snd, limits.prod.map_snd, limits.prod.map_snd_assoc],
    rw this,
    have : (image_unit j A).hom ≫ closure.less_than_closure j (M_sub j A) = image.ι (η.app A),
      apply unique_factorise_inv_comp_mono,
    rw [this, image_prod_map_comp],
  rw this,
  apply closure.dense_of_iso j _ i.symm,
  apply_instance,
end

-- local attribute [instance] has_equalizers_of_has_finite_limits

variables {B c : C} (f g : B ⟶ c)

def k : (sheaf.forget j).obj ((sheafification j).obj (equalizer f g)) ⟶ (sheaf.forget j).obj (equalizer ((sheafification j).map f) ((sheafification j).map g)) :=
(sheaf.forget j).map (equalizing_map (sheafification j) f g)

instance mono_k : mono (k j f g) :=
begin
  let A := equalizer f g,
  let L := sheafification j,
  let E := equalizer (L.map f) (L.map g),
  let e : A ⟶ B := equalizer.ι _ _,
  let d : E ⟶ L.obj B := equalizer.ι _ _,
  let k : L.obj A ⟶ E := k j f g,
  have hk : k ≫ d = L.map e := equalizer.lift_ι (L.map e) _,
  let η := (sheafification_is_adjoint j).unit,
  change @mono C _ _ _ k,
  refine ⟨λ X u v eq, _⟩,
  let P := pullback (limits.prod.map (η.app A) (η.app A)) (prod.lift u v),
  let r : P ⟶ X := pullback.snd,
  let pq : P ⟶ A ⨯ A := pullback.fst,
  let p : P ⟶ A := pq ≫ limits.prod.fst,
  let q : P ⟶ A := pq ≫ limits.prod.snd,
  have pb : r ≫ _ = pq ≫ _ := pullback.condition.symm,
  have pb₁ : r ≫ u = p ≫ η.app A,
    simpa only [prod.lift_fst, limits.prod.map_fst, assoc] using pb =≫ limits.prod.fst,
  have pb₂ : r ≫ v = q ≫ η.app A,
    simpa only [prod.lift_snd, limits.prod.map_snd, assoc] using pb =≫ limits.prod.snd,
  have : p ≫ e ≫ η.app B = q ≫ e ≫ η.app B,
    erw [η.naturality e, functor.comp_map],
    conv_lhs {rw ← assoc, congr, apply_congr pb₁.symm},
    conv_rhs {rw ← assoc, congr, apply_congr pb₂.symm},
    conv_lhs {congr, skip, congr, apply_congr hk.symm},
    conv_rhs {congr, skip, congr, apply_congr hk.symm},
    change (r ≫ u) ≫ k ≫ d = (r ≫ v) ≫ k ≫ d,
    simp only [assoc],
    congr' 1,
    simp only [← assoc],
    congr' 1,
    exact eq,
  have : (p ≫ e) ≫ η.app B = (q ≫ e) ≫ η.app B,
    rwa [← assoc, ← assoc] at this,
  obtain ⟨t, ht₁, ht₂⟩ := (kernel_pair_unit j B).lift' (p ≫ e) (q ≫ e) this,
  let denseB : B ⟶ closure.obj j (equality B) := closure.less_than_closure j _,
  let P' := pullback denseB t,
  let denseP : P' ⟶ P := pullback.snd,
  have dpdq : denseP ≫ p = denseP ≫ q,
    rw [← cancel_mono e, assoc, ← ht₁, assoc, ← ht₂, ← pullback.condition_assoc, ← pullback.condition_assoc],
    erw [closure.is_lt_assoc, closure.is_lt_assoc, prod.lift_fst, prod.lift_snd, comp_id],
  have : p ≫ η.app A = q ≫ η.app A,
    apply cancel_dense _ denseP,
    rw [← assoc, dpdq, assoc],
    apply closure.dense_of_pullback j pullback.condition,
    apply cone_is_pullback,
  have rurv  : r ≫ u = r ≫ v,
    apply pb₁.trans (this.trans pb₂.symm),
  have : closure.dense j (image.ι (limits.prod.map (η.app A) (η.app A))) := aux j A,
  resetI,
  haveI : closure.dense j (image.ι r) := dense_image_pullback_of_dense_image j (prod.lift u v) (limits.prod.map (η.app A) (η.app A)),
  apply cancel_dense_image j (L.obj A) r u v rurv,
end

instance : closure.closed j (k j f g) :=
closed_of_subsheaf j _ _ _

noncomputable instance : closure.dense j (k j f g) :=
begin
  let A := equalizer f g,
  let L := sheafification j,
  let E := equalizer (L.map f) (L.map g),
  let e : A ⟶ B := equalizer.ι _ _,
  let d : E ⟶ L.obj B := equalizer.ι _ _,
  let k : (L.obj A).A ⟶ E.A := k j f g,
  let k' : L.obj A ⟶ E := equalizing_map (sheafification j) f g,
  have hk' : k' ≫ d = L.map e := equalizer.lift_ι (L.map e) _,
  have hk : k ≫ (sheaf.forget j).map d = (sheaf.forget j).map (L.map e),
    change (sheaf.forget j).map _ ≫ (sheaf.forget j).map _ = _,
    rw ← (sheaf.forget j).map_comp,
    congr' 1,
  let η := (sheafification_is_adjoint j).unit,
  change closure.dense j k,
  let Q := pullback (η.app B) ((sheaf.forget j).map d),
  let h : Q ⟶ B := pullback.fst,
  let i : Q ⟶ E.A := pullback.snd,
  have : d ≫ L.map f = d ≫ L.map g := equalizer.condition (L.map f) (L.map g),
  have : (sheaf.forget j).map d ≫ (sheaf.forget j).map (L.map f) = (sheaf.forget j).map d ≫ (sheaf.forget j).map (L.map g),
    rw [← (sheaf.forget j).map_comp, ← (sheaf.forget j).map_comp],
    congr' 1,
  have : h ≫ f ≫ η.app c = h ≫ g ≫ η.app c,
    erw [η.naturality, η.naturality],
    rw [pullback.condition_assoc, functor.comp_map, this, pullback.condition_assoc],
    refl,
  have : (h ≫ f) ≫ η.app c = (h ≫ g) ≫ η.app c,
    rw [assoc, assoc, this],
  obtain ⟨t, ht₁, ht₂⟩ := (kernel_pair_unit j c).lift' (h ≫ f) (h ≫ g) this,
  let denseC : c ⟶ closure.obj j (equality c) := closure.less_than_closure j _,
  let Q' := pullback denseC t,
  let m : Q' ⟶ Q := pullback.snd,
  have : (m ≫ h) ≫ f = (m ≫ h) ≫ g,
    rw [assoc, assoc, ← ht₁, ← ht₂, ← pullback.condition_assoc, ← pullback.condition_assoc],
    erw [closure.is_lt_assoc, closure.is_lt_assoc, prod.lift_fst, prod.lift_snd, comp_id],
  obtain ⟨l', hl'⟩ := equalizer.lift' (m ≫ h) this,
  obtain ⟨l, hl⟩ := extend_map' (L.obj A) m (l' ≫ η.app A),
  haveI : mono ((sheaf.forget j).map d) := preserves_mono_of_preserves_pullback _ _ _ _,
  have lk : l ≫ k = i,
    suffices : l ≫ k ≫ (sheaf.forget j).map d = i ≫ (sheaf.forget j).map d,
      simp only [← assoc] at this,
      apply mono.right_cancellation _ _ this,
    apply cancel_dense (L.obj B) m,
    erw [hk, reassoc_of hl, ← η.naturality, functor.id_map, reassoc_of hl', pullback.condition],
  let im_i : image i ⟶ E.A := image.ι i,
  have : subq.mk im_i ≤ subq.mk k,
    refine ⟨sub.hom_mk _ _⟩,
    apply image.lift ⟨_, k, l, lk⟩,
    apply image.lift_fac,
  haveI : closure.dense j im_i := dense_image_pullback_of_dense_image j ((sheaf.forget j).map d) (η.app B),
  have : closure.subobj j im_i ≤ closure.subobj j k := closure.mono_sub j ‹subq.mk im_i ≤ subq.mk k›,
  rw closure.dense.closure_eq_top at this,
  refine ⟨_⟩,
  rwa eq_top_iff,
end

def sheafification_preserves_equalizer {B c : C} (f g : B ⟶ c) :
  preserves_limit.{v} (parallel_pair f g) (sheafification j) :=
begin
  apply equalizer_of_iso_point,
  suffices : is_iso (k j f g),
  { apply is_iso_of_reflects_iso _ (sheaf.forget j),
    apply this },
  apply closure.is_iso_of_dense_of_closed j,
end

end preserve_equalizers

def sheafification_preserves_equalizers : preserves_limits_of_shape.{v} walking_parallel_pair (sheafification j) :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso_diagram (sheafification j) (diagram_iso_parallel_pair _).symm,
    apply preserve_equalizers.sheafification_preserves_equalizer,
  end }

end category_theory
