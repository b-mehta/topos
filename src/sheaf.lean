import power
import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflect_isomorphisms
import reflects
import cartesian_closed

open category_theory category_theory.category category_theory.limits
open subobj

universes v u u₂

variables (C : Type u) [𝒞 : category.{v} C] [has_finite_limits.{v} C] [has_power_objects.{v} C]
include 𝒞

def and_arrow : (Ω : C) ⨯ Ω ⟶ Ω := intersect.intersect _

class topology (j : (Ω : C) ⟶ Ω) :=
(ax1 : truth ≫ j = truth)
(ax2 : j ≫ j = j)
(ax3 : and_arrow C ≫ j = limits.prod.map j j ≫ and_arrow C)

variable {C}

lemma classify_pullback {E F A : C} (m : A ⟶ E) (f : F ⟶ E) [mono m] : f ≫ classifier_of m = classifier_of (pullback.snd : pullback m f ⟶ F) :=
begin
  apply has_subobject_classifier.uniquely,
  refine ⟨pullback.fst ≫ subobj.square.k m, _, _⟩,
  rw [assoc, subobj.square.commutes m, pullback.condition_assoc],
  apply (pasting _ _ _ _ _ _ _ _ _ (subobj.square.is_pullback m)).inv (cone_is_pullback _ _),
end
lemma classify_self {E : C} : classifier_of (𝟙 E) = terminal.from _ ≫ truth :=
begin
  symmetry,
  apply has_subobject_classifier.uniquely,
  refine ⟨terminal.from E, by rw [id_comp], _⟩,
  refine is_limit.mk' _ (λ s, ⟨pullback_cone.snd s, subsingleton.elim _ _, comp_id _, λ m m₁ m₂, trans (comp_id _).symm m₂⟩)
end

lemma class_lift_of_both_factor {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (hom : A₁ ⟶ A₂) (inv : A₂ ⟶ A₁) :
  m₁ = hom ≫ m₂ → m₂ = inv ≫ m₁ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros,
  apply lifting hom inv _ _,
  rw [a, assoc],
  rw [a_1, assoc],
end
lemma class_lift_of_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₁ ≅ A₂) :
  m₁ = h.hom ≫ m₂ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros,
  apply class_lift_of_both_factor h.hom h.inv a,
  rw [iso.eq_inv_comp, a]
end
lemma class_lift_of_is_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₁ ⟶ A₂) [is_iso h] :
  m₁ = h ≫ m₂ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros,
  apply class_lift_of_iso (as_iso h) a,
end

def how_inj_is_classifier {E A₁ A₂ : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : classifier_of m₁ = classifier_of m₂) :
A₁ ≅ A₂ :=
{ hom := (subobj.square.is_pullback m₂).lift (pullback_cone.mk (subobj.square.k m₁) m₁ (h ▸ subobj.square.commutes m₁)),
  inv := (subobj.square.is_pullback m₁).lift (pullback_cone.mk (subobj.square.k m₂) m₂ (h.symm ▸ subobj.square.commutes m₂)),
  hom_inv_id' :=
  begin
    erw [← cancel_mono m₁, assoc,
         (subobj.square.is_pullback m₁).fac _ walking_cospan.right,
         (subobj.square.is_pullback m₂).fac _ walking_cospan.right],
    simp
  end,
  inv_hom_id' :=
  begin
    erw [← cancel_mono m₂, assoc,
         (subobj.square.is_pullback m₂).fac _ walking_cospan.right,
         (subobj.square.is_pullback m₁).fac _ walking_cospan.right],
    simp
  end }

lemma c_very_inj {E A₁ A₂ : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : classifier_of m₁ = classifier_of m₂) :
  (how_inj_is_classifier h).hom ≫ m₂ = m₁ :=
(subobj.square.is_pullback m₂).fac _ walking_cospan.right

variables (j : (Ω : C) ⟶ Ω) [topology.{v} C j]

namespace closure

variables {E A : C}

def obj (m : A ⟶ E) [mono m] : C := pullback truth (classifier_of m ≫ j)

def arrow (m : A ⟶ E) [mono m] : closure.obj j m ⟶ E := pullback.snd

instance (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := pullback.snd_of_mono

def hat (m : A ⟶ E) [mono m] : classifier_of (arrow j m) = classifier_of m ≫ j :=
(has_subobject_classifier.uniquely _ _ ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩).symm

def less_than_closure (m : A ⟶ E) [mono m] : A ⟶ closure.obj j m :=
pullback.lift (square.k m) m (by rw [← reassoc_of (subobj.square.commutes m), topology.ax1])

lemma is_lt (m : A ⟶ E) [mono m] : less_than_closure j m ≫ closure.arrow j m = m :=
pullback.lift_snd _ _ _

class dense (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (arrow j m))

class closed (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (less_than_closure j m))

def dense_of_classifier_eq (m : A ⟶ E) [mono m] (hm : classifier_of m ≫ j = terminal.from _ ≫ truth) : dense j m :=
begin
  rw [← closure.hat, ← classify_self] at hm,
  refine ⟨_⟩,
  rw [← c_very_inj hm, comp_id],
  apply_instance
end

lemma classifier_eq_of_dense (m : A ⟶ E) [d : dense j m] : classifier_of m ≫ j = terminal.from _ ≫ truth :=
begin
  rw ← classify_self,
  rw ← closure.hat,
  haveI := d.gives_iso,
  apply class_lift_of_is_iso (arrow j m),
  rw comp_id
end

def mono_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
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
  (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j m] : dense j l :=
begin
  haveI := mono_of_pullback comm lim,
  apply dense_of_classifier_eq,
  suffices: classifier_of l = f ≫ classifier_of m,
    rw [this, assoc, classifier_eq_of_dense j m, ← assoc],
    congr,
  rw classify_pullback,
  fapply class_lift_of_both_factor,
  fapply pullback.lift t l comm,
  fapply lim.lift (pullback_cone.mk pullback.fst pullback.snd pullback.condition),
  rw pullback.lift_snd,
  exact (lim.fac (pullback_cone.mk pullback.fst pullback.snd pullback.condition) walking_cospan.right).symm,
end

end closure

variable (C)
structure separated :=
(A : C)
(subsingleton_extend : Π B B' (m : B' ⟶ B) f' [closure.dense j m],
  subsingleton {f : B ⟶ A // m ≫ f = f'})

structure sheaf' :=
(A : C)
(unique_extend : Π {B B'} (m : B' ⟶ B) f' [closure.dense j m],
  unique {f : B ⟶ A // m ≫ f = f'})

def forget_sheaf : sheaf'.{v} C j → C := sheaf'.A

def sheaf := induced_category C (forget_sheaf C j)

instance sheaf_category.category : category (sheaf C j) := induced_category.category _
def forget : sheaf C j ⥤ C := induced_functor _

namespace construct_limits

instance sheaf_forget_reflects_limits : reflects_limits (forget C j) :=
forget_reflects_limits (forget_sheaf C j)

variables {C} {J : Type v} [𝒥₁ : small_category J] {K : J ⥤ sheaf C j} {c : cone (K ⋙ forget C j)} (t : is_limit c)
variables {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ c.X)

@[simps]
def alt_cone [mono m] [closure.dense j m] : cone (K ⋙ forget C j) :=
{ X := B,
  π :=
  { app := λ i, ((K.obj i).unique_extend m (f' ≫ c.π.app i)).1.1.1,
    naturality' := λ i₁ i₂ g,
    begin
      dsimp,
      rw [id_comp],
      have q := ((K.obj i₂).unique_extend m (f' ≫ c.π.app i₂)).2,
      let h : {f // m ≫ f = f' ≫ c.π.app i₂} := ⟨((K.obj i₁).unique_extend m (f' ≫ c.π.app i₁)).1.1.1 ≫ (K ⋙ forget C j).map g, _⟩,
      specialize q h,
      rw subtype.ext at q,
      exact q.symm,
      rw [reassoc_of ((K.obj i₁).unique_extend m (f' ≫ c.π.app i₁)).1.1.2, c.w g],
    end } }

instance sheaf_forget_creates_limits : creates_limits (forget C j) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X :=
          { A := c.X,
            unique_extend := λ B B' m f' d,
            begin
              refine ⟨⟨⟨t.lift (alt_cone j m f'), _⟩⟩, _⟩,
              { apply t.hom_ext,
                intro i,
                rw [assoc, t.fac (alt_cone j m f')],
                exact ((K.obj i).unique_extend m (f' ≫ c.π.app i)).1.1.2 },
              { rintro ⟨f₂, hf₂⟩,
                congr,
                apply t.uniq (alt_cone j m f'),
                intro i,
                dsimp [alt_cone],
                apply congr_arg subtype.val (((K.obj i).unique_extend m (f' ≫ c.π.app i)).2 ⟨_, _⟩),
                rw reassoc_of hf₂ }
            end },
          π :=
          { app := c.π.app,
            naturality' := λ X Y f, c.π.naturality f } },
        valid_lift := cones.ext (iso.refl _) (λ i, (id_comp _).symm) } } } }

end construct_limits

instance sheaf_has_finite_limits : has_finite_limits.{v} (sheaf C j) :=
{ has_limits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI
  { has_limit := λ F,
    has_limit_of_created F (forget C j) } }

variable {C}

def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
  closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
closure.dense_of_pullback j _ (pullback_prod' m A)

def sheaf_exponential (A : C) (s : sheaf C j) : (sheaf C j) :=
{ A := exp A s.A,
  unique_extend := λ B B' m f' d,
  begin
    haveI := d,
    haveI := dense_prod_map_id j A m,
    refine ⟨⟨⟨cchat (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).1.1.1, _⟩⟩, _⟩,
    { rw ← exp_transpose_natural_left,
      rw (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).1.1.2,
      exact ((exp.adjunction _).hom_equiv _ _).right_inv f' },
    rintro ⟨a, ha⟩,
    have z : limits.prod.map (𝟙 A) m ≫ unhat a = unhat f',
      rw [← exp_transpose_natural_left_symm m a, ha],

    rw ← (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).2 ⟨unhat a, z⟩,
    congr,
    symmetry,
    have p : cchat (unhat a) = a := ((exp.adjunction A).hom_equiv _ _).right_inv a,
    change cchat (unhat a) = a,
    exact p,
    sorry,
  end
}