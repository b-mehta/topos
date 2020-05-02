import power
import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflect_isomorphisms
import reflects
import cartesian_closed

open category_theory category_theory.category category_theory.limits
open subobj

universes v u u₂

def tag (n : ℕ) {α : Sort u} (x : α) : α := x

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variable {C}
def tag' (n : ℕ) (A B : C) (f : A ⟶ B) : A ⟶ B := f
variable (C)

variables [has_finite_limits.{v} C] [has_power_objects.{v} C]

def and_arrow : Ω C ⨯ Ω C ⟶ Ω C := intersect.intersect _

class topology (j : Ω C ⟶ Ω C) :=
(ax1 : truth C ≫ j = truth C)
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
lemma classify_self {E : C} : classifier_of (𝟙 E) = default (E ⟶ Ω₀ C) ≫ truth C :=
begin
  symmetry,
  apply has_subobject_classifier.uniquely,
  refine ⟨default (E ⟶ Ω₀ C), by rw [id_comp], _⟩,
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

def how_inj_is_classifier {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] (h : classifier_of m₁ = classifier_of m₂) :
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
  (how_inj_is_classifier _ _ h).hom ≫ m₂ = m₁ :=
(subobj.square.is_pullback m₂).fac _ walking_cospan.right

def intersection {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] : pullback m₁ m₂ ⟶ E := pullback.snd ≫ m₂
instance {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] : mono (intersection m₁ m₂) := mono_comp _ _

def c_leq_prop {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] :
  (∃ (k : A₁ ⟶ A₂), m₁ = k ≫ m₂) ↔ prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁ :=
begin
  have q : ∀ k, m₁ ≫ prod.lift (𝟙 E) (terminal.from E) = k ≫ m₂ ≫ prod.lift (𝟙 E) (terminal.from E) ↔ m₁ = k ≫ m₂,
    intro k,
    refine ⟨λ p, _, _⟩,
    { simpa using p =≫ limits.prod.fst },
    { intro,
      rw ← assoc,
      congr' 1,
      exact a },
  have : (∃ (k : A₁ ⟶ A₂), m₁ ≫ prod.lift (𝟙 E) (terminal.from E) = k ≫ m₂ ≫ prod.lift (𝟙 E) (terminal.from E)) ↔
         limits.prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = prod.lift (classifier_of _) _ ≫ _ := leq_prop _ _ _ _ _ _,
    rw prod.lift_fst at this,
    conv_lhs at this {congr, funext, rw q k},
  exact this,
end

-- Heh. Lift the exists from `c_leq_prop` into data.
def make_le {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂]
  (h : prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁) :
  A₁ ⟶ A₂ :=
begin
  rw ← c_leq_prop at h,
  have comm : default _ ≫ truth C = m₁ ≫ classifier_of m₂,
    cases h,
    rw h_h,
    rw assoc,
    rw ← subobj.square.commutes m₂,
    rw ← assoc,
    congr,
  exact (subobj.square.is_pullback m₂).lift (pullback_cone.mk _ _ comm)
end

lemma make_le_comm {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂]
  (h : prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁) :
  make_le m₁ m₂ h ≫ m₂ = m₁ :=
(subobj.square.is_pullback m₂).fac _ walking_cospan.right


-- def classify_intersect

variables (j : Ω C ⟶ Ω C) [topology.{v} C j]

namespace closure

variables {E A : C}

def obj (m : A ⟶ E) [mono m] : C := pullback (truth C) (classifier_of m ≫ j)

def arrow (m : A ⟶ E) [mono m] : closure.obj j m ⟶ E := pullback.snd

instance is_sub (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := pullback.snd_of_mono

def hat (m : A ⟶ E) [mono m] : classifier_of (arrow j m) = classifier_of m ≫ j :=
(has_subobject_classifier.uniquely _ _ ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩).symm

def less_than_closure (m : A ⟶ E) [mono m] : A ⟶ closure.obj j m :=
pullback.lift (square.k m) m (by rw [← reassoc_of (subobj.square.commutes m), topology.ax1])

lemma is_lt (m : A ⟶ E) [mono m] : less_than_closure j m ≫ closure.arrow j m = m :=
pullback.lift_snd _ _ _

def classify_subobj {A' : C} (n : A ⟶ A') (m : A' ⟶ E) [mono n] [mono m] :
  classifier_of n = m ≫ classifier_of (n ≫ m) :=
begin
  symmetry,
  apply has_subobject_classifier.uniquely,
  refine ⟨𝟙 _ ≫ square.k (n ≫ m), _, _⟩,
  { rw [← assoc, ← subobj.square.commutes (n ≫ m)], congr },
  apply (pasting (𝟙 A) _ n (n ≫ m) (truth C) m (classifier_of (n ≫ m)) _ _ (subobj.square.is_pullback (n ≫ m))).inv
    (pullback_square_iso' _ _ _ _ _),
  rw id_comp,
end

def idem (m : A ⟶ E) [mono m] : obj j (arrow j m) ≅ obj j m :=
begin
  have: classifier_of (arrow j (arrow j m)) = classifier_of (arrow j m),
    rw [hat, hat, assoc, topology.ax2],
  exact how_inj_is_classifier _ _ this,
end

def monotone {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (hk : ∃ (k : A ⟶ B), m = k ≫ n) : obj j m ⟶ obj j n :=
begin
  apply make_le (arrow j m) (arrow j n),
  rw [hat, hat, ← prod.lift_map, assoc, ← topology.ax3, ← assoc, (c_leq_prop _ _).1 hk]
end

lemma monotone_comm {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (hk : ∃ (k : A ⟶ B), m = k ≫ n) :
  monotone j m n hk ≫ arrow j n = arrow j m :=
make_le_comm _ _ _

class dense (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (arrow j m))

def dense_of_classifier_eq (m : A ⟶ E) [mono m] (hm : classifier_of m ≫ j = default _ ≫ truth C) : dense j m :=
begin
  rw [← closure.hat, ← classify_self] at hm,
  refine ⟨_⟩,
  rw [← c_very_inj hm, comp_id],
  apply_instance
end

instance dense_inclusion (m : A ⟶ E) [mono m] : dense j (less_than_closure j m) :=
begin
  haveI := mono_of_mono_fac (is_lt j m),
  apply dense_of_classifier_eq,
  rw classify_subobj _ (closure.arrow j m),
  rw assoc,
  slice_lhs 2 2 {congr, rw is_lt},
  rw ← hat,
  rw ← subobj.square.commutes (arrow j m),
  congr
end

lemma classifier_eq_of_dense (m : A ⟶ E) [d : dense j m] : classifier_of m ≫ j = default _ ≫ truth C :=
begin
  rw ← classify_self,
  rw ← closure.hat,
  haveI := d.gives_iso,
  apply class_lift_of_is_iso (arrow j m),
  rw comp_id
end

class closed (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (less_than_closure j m))

def closed_of_classifier_eq (m : A ⟶ E) [mono m] (hm : classifier_of m ≫ j = classifier_of m) : closed j m :=
begin
  rw [← closure.hat] at hm,
  refine ⟨_⟩,
  have := c_very_inj hm,
  conv_lhs at this {congr, skip, rw ← is_lt j m},
  rw [← assoc, cancel_mono_id (arrow j m), iso.hom_comp_eq_id] at this,
  rw this,
  apply_instance,
end
lemma classifier_eq_of_closed (m : A ⟶ E) [c : closed j m] : classifier_of m ≫ j = classifier_of m :=
begin
  rw ← closure.hat,
  haveI := c.gives_iso,
  symmetry,
  apply class_lift_of_is_iso (less_than_closure j m),
  rw is_lt,
end
instance is_closed (m : A ⟶ E) [mono m] : closed j (arrow j m) :=
begin
  apply closed_of_classifier_eq,
  rw [hat, assoc, topology.ax2],
end

def lifting_square {A A' B B' : C} {f' : B' ⟶ A'} {m : A' ⟶ A} {n : B' ⟶ B} {f : B ⟶ A}
  (comm : f' ≫ m = n ≫ f) [d : closure.dense j n] [c : closure.closed j m] : B ⟶ A' :=
begin
  let finvA' : C := pullback m f,
  let k : B' ⟶ finvA' := pullback.lift f' n comm,
  let i₂ : closure.obj j n ⟶ closure.obj j pullback.snd := closure.monotone _ _ _ ⟨k, (pullback.lift_snd _ _ _).symm⟩,
  have: classifier_of (closure.arrow j (pullback.snd : finvA' ⟶ B)) = classifier_of (pullback.snd : finvA' ⟶ B),
    rw closure.hat,
    rw ← classify_pullback _ _,
    rw assoc,
    rw closure.classifier_eq_of_closed,
  let i₃ := how_inj_is_classifier _ _ this,
  refine d.gives_iso.inv ≫ i₂ ≫ i₃.hom ≫ pullback.fst,
end

lemma lifting_square_prop {A A' B B' : C} {f' : B' ⟶ A'} {m : A' ⟶ A} {n : B' ⟶ B} {f : B ⟶ A}
  (comm : f' ≫ m = n ≫ f) [d : closure.dense j n] [c : closure.closed j m] : lifting_square j comm ≫ m = f :=
begin
  let finvA' : C := pullback m f,
  have q : classifier_of (closure.arrow j (pullback.snd : finvA' ⟶ B)) = classifier_of (pullback.snd : finvA' ⟶ B),
    rw closure.hat,
    rw ← classify_pullback _ _,
    rw assoc,
    rw closure.classifier_eq_of_closed,
  rw [lifting_square, assoc, assoc, assoc, pullback.condition],
  change _ ≫ closure.monotone j n pullback.snd _ ≫ (how_inj_is_classifier _ _ q).hom ≫ pullback.snd ≫ f = f,
  have := c_very_inj q,
  rw reassoc_of (c_very_inj q),
  slice_lhs 2 3 {rw closure.monotone_comm},
  rw is_iso.inv_hom_id_assoc
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

def mono_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [mono f] : mono t :=
begin
  refine ⟨λ Z g h eq, _⟩,
  apply lim.hom_ext,
  apply (pullback_cone.mk t l comm).equalizer_ext,
  exact eq,
  rw ← cancel_mono f,
  erw [assoc, assoc, ← comm, reassoc_of eq],
end

def dense_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
  (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j f] : dense j t :=
begin
  haveI := mono_top_of_pullback comm lim,
  apply dense_of_classifier_eq,
  suffices: classifier_of t = m ≫ classifier_of f,
    rw [this, assoc, classifier_eq_of_dense j f, ← assoc],
    congr,
  rw classify_pullback,
  apply class_lift_of_both_factor _ _ _ _,
  apply pullback.lift l t comm.symm,
  apply lim.lift (pullback_cone.mk _ _ pullback.condition.symm),
  rw pullback.lift_snd,
  exact (lim.fac (pullback_cone.mk _ _ pullback.condition.symm) walking_cospan.left).symm,
end

def characterised {A A' A'' : C} (m : A' ⟶ A) [mono m] (d : A' ⟶ A'') (c : A'' ⟶ A) (h : d ≫ c = m) [dense j d] [closed j c] :
  obj j m ≅ A'' :=
{ hom :=
  begin
    have : d ≫ c = less_than_closure j m ≫ arrow j m,
      rw h, rw is_lt,
    apply lifting_square j this,
  end,
  inv :=
  begin
    have : less_than_closure j m ≫ arrow j m = d ≫ c,
      rw h, rw is_lt,
    apply lifting_square j this,
  end,
  hom_inv_id' :=
  begin
    have z₁ : less_than_closure j m ≫ arrow j m = d ≫ c,
      rw h, rw is_lt,
    rw [← cancel_mono_id (arrow j m), assoc, lifting_square_prop j z₁, lifting_square_prop j z₁.symm],
  end,
  inv_hom_id' :=
  begin
    have z₁ : less_than_closure j m ≫ arrow j m = d ≫ c,
      rw h, rw is_lt,
    rw [← cancel_mono_id c, assoc, lifting_square_prop j z₁.symm, lifting_square_prop j z₁],
  end }

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

variables {C j}
def unique_ext (A : sheaf C j) {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ A.A) [closure.dense j m]
  (f₁ f₂ : B ⟶ A.A) (h₁ : m ≫ f₁ = f') (h₂ : m ≫ f₂ = f') :
  f₁ = f₂ :=
begin
  have z := (A.unique_extend m f').2,
  have := (z ⟨f₁, h₁⟩).trans (z ⟨f₂, h₂⟩).symm,
  rw subtype.ext at this,
  exact this
end

section biject
variables (j) {A B : C} (m : B ⟶ A) [closure.dense j m]

def pushforward_closed_subobject {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  C :=
closure.obj j (n ≫ m)

def pushforward_closed_arrow {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  pushforward_closed_subobject j m n ⟶ A :=
closure.arrow j (n ≫ m)

instance {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  mono (pushforward_closed_arrow j m n) :=
closure.is_sub j _

instance {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  closure.closed j (pushforward_closed_arrow j m n) :=
closure.is_closed j _

lemma classify_pushforward_obj {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  classifier_of (pushforward_closed_arrow j m n) = classifier_of (n ≫ m) ≫ j :=
closure.hat j _

def pullback_closed_subobject {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  C :=
pullback n m

def pullback_closed_arrow {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  pullback_closed_subobject j m n ⟶ B :=
pullback.snd

instance {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  mono (pullback_closed_arrow j m n) :=
pullback.snd_of_mono

instance {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  closure.closed j (pullback_closed_arrow j m n) :=
begin
  apply closure.closed_of_classifier_eq,
  erw [← classify_pullback, assoc, closure.classifier_eq_of_closed],
end

lemma classify_pullback_obj {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  classifier_of (pullback_closed_arrow j m n) = m ≫ classifier_of n :=
(classify_pullback _ _).symm

def classify_pullback_pushout {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  pushforward_closed_subobject j m (pullback_closed_arrow j m n) ≅ A' :=
begin
  apply closure.characterised j _ pullback.fst n pullback.condition,
  apply closure.dense_top_of_pullback j pullback.condition (cone_is_pullback _ m),
end

lemma classify_pullback_pushout_comm {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  (classify_pullback_pushout j m n).hom ≫ n = pushforward_closed_arrow j m (pullback_closed_arrow j m n) :=
begin
  rw classify_pullback_pushout,
  rw closure.characterised,
  dsimp,
  rw closure.lifting_square_prop,
  refl,
end

lemma classify_pullback_pushforward {A' : C} (n : A' ⟶ A) [closure.closed j n] :
  classifier_of (pushforward_closed_arrow j m (pullback_closed_arrow j m n)) = classifier_of n :=
class_lift_of_iso _ (classify_pullback_pushout_comm j m n).symm

lemma classify_pushforward_pullback {B' : C} (n : B' ⟶ B) [closure.closed j n] :
  classifier_of (pullback_closed_arrow j m (pushforward_closed_arrow j m n)) = classifier_of n :=
begin
  rw [classify_pullback_obj, classify_pushforward_obj, ← assoc, ← closure.classify_subobj],
  apply closure.classifier_eq_of_closed
end

end biject

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
              refine ⟨⟨⟨t.lift (alt_cone m f'), _⟩⟩, _⟩,
              { apply t.hom_ext,
                intro i,
                rw [assoc, t.fac (alt_cone m f')],
                exact ((K.obj i).unique_extend m (f' ≫ c.π.app i)).1.1.2 },
              { rintro ⟨f₂, hf₂⟩,
                congr,
                apply t.uniq (alt_cone m f'),
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

variables {C} (j)

def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
  closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
closure.dense_of_pullback j _ (pullback_prod' m A)

def sheaf_exponential (A : C) (s : sheaf C j) : sheaf C j :=
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
  end
  }


def subobject_of_closed_sheaf (A : sheaf C j) (A' : C) (m : A' ⟶ A.A) [closure.closed j m] : sheaf C j :=
{ A := A',
  unique_extend := λ B B' n f' d,
  begin
    haveI := d,
    obtain ⟨⟨⟨g, comm⟩⟩, _⟩ := A.unique_extend n (f' ≫ m),
    refine ⟨⟨⟨closure.lifting_square j comm.symm, _⟩⟩, _⟩,
    rw ← cancel_mono m,
    rw assoc,
    rw closure.lifting_square_prop j comm.symm, rw comm,
    intro a,
    cases a,
    congr,
    rw ← cancel_mono m,
    rw closure.lifting_square_prop j comm.symm,
    apply unique_ext A n (f' ≫ m) (a_val ≫ m) g _ comm,
    rw reassoc_of a_property,
  end }

def closed_of_subsheaf (E A : sheaf C j) (m : A ⟶ E) [@mono C 𝒞 _ _ m] : closure.closed j m :=
begin
  obtain ⟨⟨r, hr⟩⟩ := (A.unique_extend (closure.less_than_closure j m) (𝟙 _)).1,
  have := unique_ext E (closure.less_than_closure j m) m (r ≫ m) (closure.arrow j m) (by rw [reassoc_of hr]) (closure.is_lt _ _),
  refine ⟨⟨r, hr, _⟩⟩,
  rw [auto_param_eq, ← cancel_mono_id (closure.arrow j m), assoc, closure.is_lt, this],
end

def closed_classifier : C := equalizer j (𝟙 _)

def sheaf_classifier : sheaf C j :=
{ A := closed_classifier j,
  unique_extend := λ B B' m f' d,
  begin
    let f'' := f' ≫ equalizer.ι _ _,
    let B'' := pullback (truth C) f'',
    let B''sub : B'' ⟶ B' := pullback.snd,
    have z : classifier_of B''sub = f'',
      symmetry,
      apply has_subobject_classifier.uniquely,
      refine ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩,
    have : closure.closed j B''sub,
      apply closure.closed_of_classifier_eq,
      rw [z, assoc, equalizer.condition, comp_id],
    haveI := this,
    let new_sub := pushforward_closed_arrow j m B''sub,
    have q : classifier_of new_sub ≫ j = classifier_of new_sub ≫ 𝟙 _,
      rw comp_id,
      apply closure.classifier_eq_of_closed,
    let t := equalizer.lift (classifier_of new_sub) q,
    refine ⟨⟨⟨t, _⟩⟩, _⟩,
    apply equalizer.hom_ext,
    rw [assoc, equalizer.lift_ι, classify_pushforward_obj],
    change m ≫ classifier_of (B''sub ≫ m) ≫ j = f'',
    rw [← assoc, ← closure.classify_subobj B''sub m, ← z],
    apply closure.classifier_eq_of_closed,
    intro a,
    cases a,
    congr,
    apply equalizer.hom_ext,
    rw equalizer.lift_ι,


  end
}