import power
import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflect_isomorphisms
import reflects
import cartesian_closed
import sub

open category_theory category_theory.category category_theory.limits
open subobj

universes v u u₂

def tag (n : ℕ) {α : Sort u} (x : α) : α := x

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variable {C}
def tag' (n : ℕ) (A B : C) (f : A ⟶ B) : A ⟶ B := f

variables [has_finite_limits.{v} C] [has_subobject_classifier.{v} C] [is_cartesian_closed.{v} C]

lemma classify_pullback {E F A : C} (m : A ⟶ E) (f : F ⟶ E) [mono m] : f ≫ classifier_of m = classifier_of (pullback.snd : pullback m f ⟶ F) :=
begin
  apply has_subobject_classifier.uniquely,
  apply left_right_hpb_to_both_hpb _ has_pullback_top_of_pb (subobj.classifies m),
end

@[reducible]
def get_subobject_obj {B : C} (c : B ⟶ Ω C) : C := pullback (truth C) c
def get_subobject {B : C} (c : B ⟶ Ω C) : get_subobject_obj c ⟶ B := pullback.snd

instance get_subobject_mono {B : C} (c : B ⟶ Ω C) : mono (get_subobject c) := pullback.snd_of_mono

lemma classify_inv {E : C} (c : E ⟶ Ω C) : classifier_of (get_subobject c) = c :=
(has_subobject_classifier.uniquely _ _ has_pullback_top_of_pb).symm

lemma class_lift_of_is_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₂ ⟶ A₁) [is_iso h] :
  h ≫ m₁ = m₂ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros k,
  apply has_subobject_classifier.uniquely,
  change has_pullback_top _ _ _,
  rw ← id_comp (classifier_of m₁),
  apply left_right_hpb_to_both_hpb m₁,
  apply top_iso_has_pullback_top h,
    simpa,
  apply subobj.classifies,
end

lemma class_lift_of_iso {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (h : A₁ ≅ A₂) :
  m₁ = h.hom ≫ m₂ → classifier_of m₁ = classifier_of m₂ :=
begin
  intro l,
  apply class_lift_of_is_iso h.inv,
  simp [l],
end

lemma class_lift_of_both_factor {A₁ A₂ E : C} {m₁ : A₁ ⟶ E} {m₂ : A₂ ⟶ E} [mono m₁] [mono m₂] (hom : A₁ ⟶ A₂) (inv : A₂ ⟶ A₁) :
  m₁ = hom ≫ m₂ → m₂ = inv ≫ m₁ → classifier_of m₁ = classifier_of m₂ :=
begin
  intros k l,
  apply class_lift_of_iso ⟨hom, inv, _, _⟩ k,
  rw ← cancel_mono m₁, simp [← k, ← l],
  rw ← cancel_mono m₂, simp [← k, ← l],
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

@[simps]
def classification {B : C} : sub B ≃ (B ⟶ Ω C) :=
{ to_fun := λ f,
  begin
    apply quotient.lift_on f _ _,
    intro f',
    exact @classifier_of _ _ _ _ _ f'.1.hom f'.2,
    rintros a b ⟨⟨k, hk⟩, ⟨l, hl⟩⟩,
    haveI := a.2,
    haveI := b.2,
    refine class_lift_of_both_factor k l hk hl,
  end,
  inv_fun := λ f, ⟦⟨over.mk (get_subobject f), get_subobject_mono f⟩⟧,
  left_inv := λ f,
  begin
    dsimp,
    apply quotient.induction_on f,
    intro f',
    apply quotient.sound,
    haveI := f'.2,
    refine ⟨⟨_, ((subobj.square.is_pullback f'.1.hom).fac _ walking_cospan.right).symm⟩,
            ⟨_, (pullback.lift_snd _ _ (subobj.square.commutes f'.1.hom)).symm⟩⟩,
  end,
  right_inv := λ c, classify_inv c }

-- @[reducible]
-- def classify (f : sub B) : B ⟶ Ω C := classification

lemma classification_natural {B B' : C} (f : B ⟶ B') (m : sub B') : f ≫ classification.to_fun m = classification.to_fun (sub_map f m) :=
begin
  revert m, apply quotient.ind, intro m,
  dsimp [sub_map],
  apply classify_pullback,
end

lemma classification_natural_symm {B B' : C} (f : B ⟶ B') (c : B' ⟶ Ω C) : classification.inv_fun (f ≫ c) = sub_map f (classification.inv_fun c) :=
begin
  erw classification.symm_apply_eq,
  conv_lhs {rw ← classification.right_inv c},
  rw classification_natural,
  refl
end

def sub_bot {B : C} : sub B := ⟦⟨over.mk (initial.to B), category_theory.initial_mono B⟩⟧
instance {B : C} : order_bot (sub B) :=
{ bot := sub_bot,
  bot_le :=
  begin
    apply quotient.ind, intro a,
    refine ⟨initial.to _, _⟩,
    dsimp,
    apply subsingleton.elim,
  end,
  ..category_theory.sub_partial }

-- lemma inf_eq_intersection :
namespace intersect

def indicators {B : C} (m : B ⟶ Ω C) (n : B ⟶ Ω C) : B ⟶ Ω C :=
classification.to_fun (classification.inv_fun m ⊓ classification.inv_fun n)

def indicators_natural {B B' : C} (f : B' ⟶ B) (m : B ⟶ Ω C) (n : B ⟶ Ω C) :
  f ≫ indicators m n = indicators (f ≫ m) (f ≫ n) :=
begin
  dunfold indicators,
  rw [classification_natural, intersect_prop, ← classification_natural_symm, ← classification_natural_symm],
end

end intersect

variable (C)

def and_arrow : Ω C ⨯ Ω C ⟶ Ω C := intersect.indicators limits.prod.fst limits.prod.snd

lemma property {B : C} (m₁ m₂ : sub B) :
  limits.prod.lift (classification.to_fun m₁) (classification.to_fun m₂) ≫ and_arrow C = classification.to_fun (m₁ ⊓ m₂) :=
by rw [and_arrow, intersect.indicators_natural, prod.lift_fst, prod.lift_snd, intersect.indicators, classification.left_inv, classification.left_inv]

class topology (j : Ω C ⟶ Ω C) :=
(ax1 : truth C ≫ j = truth C)
(ax2 : j ≫ j = j)
(ax3 : and_arrow C ≫ j = limits.prod.map j j ≫ and_arrow C)

variable {C}

lemma classify_self {E : C} : classifier_of (𝟙 E) = default (E ⟶ Ω₀ C) ≫ truth C :=
begin
  symmetry,
  apply has_subobject_classifier.uniquely,
  apply left_iso_has_pullback_top (default (E ⟶ Ω₀ C)),
  rw id_comp
end

lemma classify_top (E : C) : classification.to_fun ⊤ = default (E ⟶ Ω₀ C) ≫ truth C :=
by { dsimp [top_eq_top, classification_to_fun, sub_top], rw classify_self }
-- def pushforward_well_defined {B A A₁ A₂ : C} (n : A ⟶ B) [mono n] (m₁ : A₁ ⟶ A) (m₂ : A₂ ⟶ A) [mono m₁] [mono m₂]
--   (h : classifier_of m₁ = classifier_of m₂) : classifier_of (m₁ ≫ n) = classifier_of (m₂ ≫ n) :=
-- begin
--   let i := how_inj_is_classifier _ _ h,
--   apply class_lift_of_iso i _,
--   rw [← c_very_inj h, assoc],
-- end

-- def c_leq_prop {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂] :
--   (∃ (k : A₁ ⟶ A₂), m₁ = k ≫ m₂) ↔ prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁ :=
-- begin

--   -- have q : ∀ k, m₁ ≫ prod.lift (𝟙 E) (terminal.from E) = k ≫ m₂ ≫ prod.lift (𝟙 E) (terminal.from E) ↔ m₁ = k ≫ m₂,
--   --   intro k,
--   --   refine ⟨λ p, _, _⟩,
--   --   { simpa using p =≫ limits.prod.fst },
--   --   { intro,
--   --     rw ← assoc,
--   --     congr' 1,
--   --     exact a },
--   -- have : (∃ (k : A₁ ⟶ A₂), m₁ ≫ prod.lift (𝟙 E) (terminal.from E) = k ≫ m₂ ≫ prod.lift (𝟙 E) (terminal.from E)) ↔
--   --        limits.prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = prod.lift (classifier_of _) _ ≫ _ := leq_prop _ _ _ _ _ _,
--   --   rw prod.lift_fst at this,
--   --   conv_lhs at this {congr, funext, rw q k},
--   -- exact this,
-- end

-- Heh. Lift the exists from `c_leq_prop` into data.
-- def make_le {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂]
--   (h : prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁) :
--   A₁ ⟶ A₂ :=
-- begin
--   rw ← c_leq_prop at h,
--   have comm : default _ ≫ truth C = m₁ ≫ classifier_of m₂,
--     cases h,
--     rw h_h,
--     rw assoc,
--     rw ← subobj.square.commutes m₂,
--     rw ← assoc,
--     congr,
--   exact (subobj.square.is_pullback m₂).lift (pullback_cone.mk _ _ comm)
-- end

-- def make_mono {A B : C}

-- lemma make_le_comm {E A₁ A₂ : C} (m₁ : A₁ ⟶ E) (m₂ : A₂ ⟶ E) [mono m₁] [mono m₂]
--   (h : prod.lift (classifier_of m₁) (classifier_of m₂) ≫ and_arrow C = classifier_of m₁) :
--   make_le m₁ m₂ h ≫ m₂ = m₁ :=
-- (subobj.square.is_pullback m₂).fac _ walking_cospan.right


-- def classify_intersect

variables (j : Ω C ⟶ Ω C) [topology.{v} C j]

namespace closure

variables {E A : C}

def closure (m : sub E) : sub E := classification.inv_fun (classification.to_fun m ≫ j)
lemma classify (m : sub E) : classification.to_fun (closure j m) = classification.to_fun m ≫ j :=
classification.right_inv _

def comm_pullback (m : sub E) (f : A ⟶ E) : sub_map f (closure j m) = closure j (sub_map f m) :=
begin
  apply classification.left_inv.injective,
  rw [← classification_natural, classify, classify, ← classification_natural, assoc],
end

lemma less_than_closure : ∀ (m : sub E), m ≤ closure j m :=
begin
  apply quotient.ind,
  intro m,
  haveI := m.2,
  refine ⟨pullback.lift (square.k m.1.hom) m.1.hom _, (pullback.lift_snd _ _ _).symm⟩,
  dsimp [classification_to_fun],
  rw [← reassoc_of (subobj.square.commutes m.1.hom), topology.ax1],
end

lemma idem (m : sub E) : closure j (closure j m) = closure j m :=
begin
  apply classification.left_inv.injective,
  rw [closure.classify, closure.classify, assoc, topology.ax2],
end

lemma transfer_le (m n : sub E) :
  m ≤ n ↔ prod.lift (classification.to_fun m) (classification.to_fun n) ≫ and_arrow C = classification.to_fun m :=
begin
  rw [property, function.injective.eq_iff classification.left_inv.injective], simp,
end

lemma monotone (m n : sub E) : m ≤ n → closure j m ≤ closure j n :=
begin
  rw [transfer_le, transfer_le, closure.classify, closure.classify, ← prod.lift_map, assoc, ← topology.ax3],
  intro k, rw reassoc_of k
end

@[reassoc] lemma classify_postcompose' {A' : C} (n : A ⟶ A') (m : A' ⟶ E) [mono n] [mono m] :
  classifier_of n = m ≫ classifier_of (n ≫ m) :=
begin
  symmetry,
  apply has_subobject_classifier.uniquely,
  apply left_right_hpb_to_both_hpb (n ≫ m) (top_iso_has_pullback_top (𝟙 _) _ _ m _) (subobj.classifies _),
  rw id_comp,
end

@[reassoc] lemma classify_postcompose {B E : C} (m : B ⟶ E) [mono m] :
  ∀ (n : sub B), classification.to_fun n = m ≫ classification.to_fun (postcompose m n) :=
begin
  apply quotient.ind,
  intro n,
  dsimp [postcompose],
  apply classify_postcompose',
end

def raise_le {B : C} {m₁ m₂ : sub' B} (h : m₁ ≤ m₂) : m₁.1.left ⟶ m₂.1.left :=
begin
  haveI := m₂.2,
  apply (subobj.square.is_pullback m₂.1.hom).lift (pullback_cone.mk (default _) m₁.1.hom _),
  cases h,
  rw [h_h, assoc, ← subobj.square.commutes m₂.1.hom, ← assoc, cancel_mono (truth C)],
  apply subsingleton.elim
end

@[reassoc] lemma raise_le_prop {B : C} {m₁ m₂ : sub' B} (h : m₁ ≤ m₂) : raise_le h ≫ m₂.1.hom = m₁.1.hom :=
begin
  haveI := m₂.2,
  apply (subobj.square.is_pullback m₂.1.hom).fac _ walking_cospan.right,
end

def mediating_subobject {E : C} {m₁ m₂ : sub' E} (h : m₁ ≤ m₂) : sub' m₂.1.left :=
⟨over.mk (raise_le h), begin haveI := m₁.2, apply mono_of_mono_fac (raise_le_prop h) end⟩

lemma mediating_subobject_prop {E : C} {m₁ m₂ : sub' E} (h : m₁ ≤ m₂) :
  (mediating_subobject h).1.hom ≫ m₂.1.hom = m₁.1.hom :=
raise_le_prop _

-- def obj (m : A ⟶ E) [mono m] : C := pullback (truth C) (classifier_of m ≫ j)

-- def arrow (m : A ⟶ E) [mono m] : closure.obj j m ⟶ E := pullback.snd

-- instance is_sub (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := pullback.snd_of_mono

-- def hat (m : A ⟶ E) [mono m] : classifier_of (arrow j m) = classifier_of m ≫ j :=
-- (has_subobject_classifier.uniquely _ _ ⟨pullback.fst, pullback.condition, cone_is_pullback _ _⟩).symm

-- def less_than_closu
-- def less_than_closure (m : A ⟶ E) [mono m] : A ⟶ closure.obj j m :=
-- pullback.lift (square.k m) m (by rw [← reassoc_of (subobj.square.commutes m), topology.ax1])

-- lemma is_lt (m : A ⟶ E) [mono m] : less_than_closure j m ≫ closure.arrow j m = m :=
-- pullback.lift_snd _ _ _

-- @[reassoc] def classify_subobj {A' : C} (n : A ⟶ A') (m : A' ⟶ E) [mono n] [mono m] :
--   classifier_of n = m ≫ classifier_of (n ≫ m) :=
-- begin
--   symmetry,
--   apply has_subobject_classifier.uniquely,
--   refine ⟨𝟙 _ ≫ square.k (n ≫ m), _, _⟩,
--   { rw [← assoc, ← subobj.square.commutes (n ≫ m)], congr },
--   apply (pasting (𝟙 A) _ n (n ≫ m) (truth C) m (classifier_of (n ≫ m)) _ _ (subobj.square.is_pullback (n ≫ m))).inv
--     (pullback_square_iso' _ _ _ _ _),
--   rw id_comp,
-- end

-- def idem (m : A ⟶ E) [mono m] : obj j (arrow j m) ≅ obj j m :=
-- begin
--   have: classifier_of (arrow j (arrow j m)) = classifier_of (arrow j m),
--     rw [hat, hat, assoc, topology.ax2],
--   exact how_inj_is_classifier _ _ this,
-- end

-- def monotone {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (hk : ∃ (k : A ⟶ B), m = k ≫ n) : obj j m ⟶ obj j n :=
-- begin
--   apply make_le (arrow j m) (arrow j n),
--   rw [hat, hat, ← prod.lift_map, assoc, ← topology.ax3, ← assoc, (c_leq_prop _ _).1 hk]
-- end

-- lemma monotone_comm {B : C} (m : A ⟶ E) (n : B ⟶ E) [mono m] [mono n] (hk : ∃ (k : A ⟶ B), m = k ≫ n) :
--   monotone j m n hk ≫ arrow j n = arrow j m :=
-- make_le_comm _ _ _

class dense (m : sub E) :=
(closure_eq_top : closure j m = ⊤)

def dense_of_classifier_eq (m : sub E) (hm : classification.to_fun m ≫ j = default _ ≫ truth C) : dense j m :=
begin
  rw [← closure.classify, ← classify_top] at hm,
  exact ⟨classification.left_inv.injective hm⟩,
end

instance dense_inclusion (m : sub' E) : dense j ⟦mediating_subobject (less_than_closure j ⟦m⟧)⟧ :=
begin
  apply dense_of_classifier_eq,
  haveI := m.2,
  rw classify_postcompose (get_subobject (classifier_of m.val.hom ≫ j)),
  rw assoc,
  dsimp [postcompose, mediating_subobject],
  slice_lhs 2 2 {congr, erw raise_le_prop},
  convert (subobj.square.commutes (get_subobject (classifier_of m.val.hom ≫ j))).symm,
  rw classify_inv (classifier_of m.val.hom ≫ j),
end

lemma classifier_eq_of_dense (m : sub E) [d : dense j m] : classification.to_fun m ≫ j = default _ ≫ truth C :=
by rw [← classify_top, ← closure.classify, dense.closure_eq_top]

class closed (m : sub E) :=
(closure_eq_self : closure j m = m)

def closed_of_classifier_eq (m : sub E) (hm : classification.to_fun m ≫ j = classification.to_fun m) : closed j m :=
begin
  rw [← closure.classify] at hm,
  refine ⟨classification.left_inv.injective hm⟩,
end

lemma classifier_eq_of_closed (m : sub E) [c : closed j m] : classification.to_fun m ≫ j = classification.to_fun m :=
by rw [← closure.classify, closed.closure_eq_self]

instance is_closed (m : sub E) : closed j (closure j m) := ⟨idem j m⟩

def lifting_square {A B : C} (f : B ⟶ A) (n : sub' B) (m : sub' A) (f' : n.1.left ⟶ m.1.left)
  [c : closed j ⟦m⟧] [d : dense j ⟦n⟧] (comm : f' ≫ m.1.hom = n.1.hom ≫ f) :
  B ⟶ m.1.left :=
begin
  have : ⊤ ≤ sub_map f ⟦m⟧,
    rw [← d.closure_eq_top, ← c.closure_eq_self, comm_pullback],
    apply monotone,
    refine ⟨pullback.lift _ _ comm, (pullback.lift_snd _ _ _).symm⟩,
  apply raise_le this ≫ pullback.fst,
end

def lifting_square_prop {A B : C} {f : B ⟶ A} {n : sub' B} {m : sub' A} {f' : n.1.left ⟶ m.1.left}
  [c : closed j ⟦m⟧] [d : dense j ⟦n⟧] (comm : f' ≫ m.1.hom = n.1.hom ≫ f) :
  lifting_square j _ _ _ _ comm ≫ m.1.hom = f :=
begin
  rw [lifting_square, assoc, pullback.condition, ← assoc],
  erw [raise_le_prop, id_comp],
end

-- def mono_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
--   (lim : is_limit (pullback_cone.mk _ _ comm)) [mono m] : mono l :=
-- begin
--   refine ⟨λ Z g h eq, _⟩,
--   apply lim.hom_ext,
--   apply (pullback_cone.mk t l comm).equalizer_ext,
--   rw ← cancel_mono m,
--   erw [assoc, assoc, comm, reassoc_of eq],
--   exact eq
-- end

-- def dense_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
--   (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j m] : dense j l :=
-- begin
--   haveI := mono_of_pullback comm lim,
--   apply dense_of_classifier_eq,
--   suffices: classifier_of l = f ≫ classifier_of m,
--     rw [this, assoc, classifier_eq_of_dense j m, ← assoc],
--     congr,
--   rw classify_pullback,
--   fapply class_lift_of_both_factor,
--   fapply pullback.lift t l comm,
--   fapply lim.lift (pullback_cone.mk pullback.fst pullback.snd pullback.condition),
--   rw pullback.lift_snd,
--   exact (lim.fac (pullback_cone.mk pullback.fst pullback.snd pullback.condition) walking_cospan.right).symm,
-- end

-- def mono_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
--   (lim : is_limit (pullback_cone.mk _ _ comm)) [mono f] : mono t :=
-- begin
--   refine ⟨λ Z g h eq, _⟩,
--   apply lim.hom_ext,
--   apply (pullback_cone.mk t l comm).equalizer_ext,
--   exact eq,
--   rw ← cancel_mono f,
--   erw [assoc, assoc, ← comm, reassoc_of eq],
-- end

-- def dense_top_of_pullback {E F A B : C} {m : A ⟶ E} {f : F ⟶ E} {l : B ⟶ F} {t : B ⟶ A} (comm : t ≫ m = l ≫ f)
--   (lim : is_limit (pullback_cone.mk _ _ comm)) [dense j f] : dense j t :=
-- begin
--   haveI := mono_top_of_pullback comm lim,
--   apply dense_of_classifier_eq,
--   suffices: classifier_of t = m ≫ classifier_of f,
--     rw [this, assoc, classifier_eq_of_dense j f, ← assoc],
--     congr,
--   rw classify_pullback,
--   apply class_lift_of_both_factor _ _ _ _,
--   apply pullback.lift l t comm.symm,
--   apply lim.lift (pullback_cone.mk _ _ pullback.condition.symm),
--   rw pullback.lift_snd,
--   exact (lim.fac (pullback_cone.mk _ _ pullback.condition.symm) walking_cospan.left).symm,
-- end

-- This proof is a bit trash.
def characterised {m m' : sub' E} (hm : m ≤ m') [d : dense j ⟦mediating_subobject hm⟧] [c : closed j ⟦m'⟧] :
  closure j ⟦m⟧ = ⟦m'⟧ :=
begin
  rw [closure, classification_inv_fun],
  apply quotient.sound,
  resetI,
  refine ⟨_, ⟨_, _⟩⟩,
  cases hm,
  refine ⟨_, _⟩,
  refine lifting_square j (get_subobject _) (mediating_subobject (less_than_closure j ⟦m⟧)) m' hm_w _,
  rw ← hm_h, symmetry, apply mediating_subobject_prop,
  rw lifting_square_prop, refl,
  apply @lifting_square _ _ _ _ _ j _ _ _ m'.1.hom (mediating_subobject hm) _ (raise_le (less_than_closure j ⟦m⟧)) (id _) _ _,
  apply closed_of_classifier_eq, dsimp, rw classify_inv, rw assoc, rw topology.ax2,
  rw raise_le_prop, rw mediating_subobject_prop,
  rw lifting_square_prop,
end

-- def closure_intersection {m m' : sub E} : closure j (m ⊓ m') = closure j m ⊓ closure j m' :=
-- begin
--   obtain ⟨n, rfl⟩ := quotient.exists_rep m,
--   obtain ⟨n', rfl⟩ := quotient.exists_rep m',
--   refine @characterised _ _ _ _ _ j _ E _ _ _ _ (id _),
-- end

-- end closure

variable (C)
-- structure separated :=
-- (A : C)
-- (subsingleton_extend : Π B B' (m : B' ⟶ B) f' [closure.dense j m],
--   subsingleton {f : B ⟶ A // m ≫ f = f'})

-- def exists_lifting (A : C) : Prop := ∀ {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ A) [closure.dense j m],
-- nonempty {f : B ⟶ A // m ≫ f = f'}

-- def make_lifting (A : C) (h : exists_lifting )

structure sheaf' :=
(A : C)
(unique_extend : Π {B} (m : sub' B) f' [closure.dense j ⟦m⟧], unique {f : B ⟶ A // m.1.hom ≫ f = f'})

def forget_sheaf : sheaf'.{v} C j → C := sheaf'.A

def sheaf := induced_category C (forget_sheaf C j)

instance sheaf_category.category : category (sheaf C j) := induced_category.category _
def forget : sheaf C j ⥤ C := induced_functor _

variables {C j}

@[simps]
def sheaf.mk (A : C) (h : Π {B} (m : sub' B) f' [closure.dense j ⟦m⟧], unique {f : B ⟶ A // m.1.hom ≫ f = f'}) : sheaf C j :=
{ A := A,
  unique_extend := λ B m f' d, by exactI h m f' }

@[reducible]
def sheaf.mk' (A : C) (h : Π {B} (m : sub' B) f' [closure.dense j ⟦m⟧], {f : B ⟶ A // m.1.hom ≫ f = f' ∧ ∀ a, m.1.hom ≫ a = f' → a = f}) : sheaf C j :=
sheaf.mk A $ λ B m f' d,
begin
  haveI := d,
  refine ⟨⟨⟨(h m f').1, (h m f').2.1⟩⟩, _⟩,
  rintro ⟨a, ha⟩,
  congr,
  apply (h m f').2.2 _ ha,
end

def sheaf.A (A : sheaf C j) : C := (forget C j).obj A

def sheaf.hom_mk (A B : sheaf C j) (f : A.A ⟶ B.A) : A ⟶ B := f

def extend_map (A : sheaf C j) {B : C} (m : sub' B) [closure.dense j ⟦m⟧] (f' : m.1.left ⟶ A.A) : B ⟶ A.A :=
(A.unique_extend m f').1.1.1

lemma extend_map_prop (A : sheaf C j) {B : C} (m : sub' B) [closure.dense j ⟦m⟧] (f' : m.1.left ⟶ A.A) : m.1.hom ≫ extend_map A m f' = f' :=
(A.unique_extend m f').1.1.2

lemma unique_extension (A : sheaf C j) {B : C} (m : sub' B) (f' : m.1.left ⟶ A.A) [closure.dense j ⟦m⟧]
  (f : B ⟶ A.A) (h : m.1.hom ≫ f = f') :
f = extend_map A m f' :=
congr_arg subtype.val ((A.unique_extend m f').2 ⟨f, h⟩)

def unique_ext (A : sheaf C j) {B : C} (m : sub' B) (f' : m.1.left ⟶ A.A) [closure.dense j ⟦m⟧]
  (f₁ f₂ : B ⟶ A.A) (h₁ : m.1.hom ≫ f₁ = f') (h₂ : m.1.hom ≫ f₂ = f') :
  f₁ = f₂ :=
(unique_extension A m f' f₁ h₁).trans (unique_extension A m f' f₂ h₂).symm

instance sheaf_forget_reflects_limits : reflects_limits (forget C j) :=
forget_reflects_limits (forget_sheaf C j)

attribute [irreducible] sheaf

section biject
variables (j) (m : sub' A) [closure.dense j ⟦m⟧]

def bijection : {n : sub A // closure j n = n} ≃ {n' : sub m.1.left // closure j n' = n'} :=
{ to_fun := λ n,
  { val := sub_map m.1.hom n.val,
    property :=
    begin
      apply classification.left_inv.injective,
      rw [closure.classify, ← classification_natural, assoc, ← closure.classify, n.2],
    end },
  inv_fun := λ n',
  { val :=
    begin
      haveI := m.2,
      apply closure j (postcompose m.1.hom n'.1),
    end,
    property := idem _ _ },
  left_inv :=
  begin
    rintro ⟨N, hN⟩,
    dsimp,
    revert hN,
    apply quotient.induction_on N,
    intros n hn,
    congr' 1,
    apply characterised j _,
    refine ⟨pullback.fst, pullback.condition.symm⟩,
    refine ⟨_⟩,
    rw ← top_le_iff,
    refine ⟨pullback.lift (default _) (𝟙 _) _, _⟩,
    dsimp, rw [id_comp],
    dsimp [mediating_subobject],
    erw classify_postcompose,


    apply quotient.sound,

    sorry,
    refine ⟨hn⟩,
  end,
  right_inv :=
  begin
    rintro ⟨n', hn'⟩,
    dsimp, congr' 1,
    rw comm_pullback,
    haveI := m.2,
    rw ← postcompose_sub_comm (𝟙 _) (𝟙 _) m.val.hom m.val.hom rfl (pullback_square_iso _ _ _ _ _) n',
    rw [postcompose_map_id, sub_map_id, hn'],
  end
  -- { obj := sub_map m.1.hom n.obj,
  --   is_closed :=
  --   begin
  --     apply closed_of_classifier_eq,
  --     rw ← classification_natural,
  --     rw assoc,
  --     haveI := n.is_closed,
  --     rw classifier_eq_of_closed j n.obj,
  --   end },
  -- inv_fun := λ n',
  -- { obj :=
  --   begin
  --     haveI := m.2,
  --     exact closure j (postcompose m.1.hom n'.obj),
  --   end },
  -- left_inv :=
  -- begin
  --   rintro ⟨n, hn⟩,
  --   dsimp,
  --   congr' 1,
  --   sorry,


  -- end

}
-- def pushforward_closed_subobject {B' : C} (n : B' ⟶ B) [mono n] :
--   C :=
-- closure.obj j (n ≫ m)

-- def pushforward_closed_arrow {B' : C} (n : B' ⟶ B) [mono n]:
--   pushforward_closed_subobject j m n ⟶ A :=
-- closure.arrow j (n ≫ m)

-- instance {B' : C} (n : B' ⟶ B) [mono n] :
--   mono (pushforward_closed_arrow j m n) :=
-- closure.is_sub j _

-- instance {B' : C} (n : B' ⟶ B) [mono n] :
--   closure.closed j (pushforward_closed_arrow j m n) :=
-- closure.is_closed j _

-- lemma classify_pushforward_obj {B' : C} (n : B' ⟶ B) [mono n] :
--   classifier_of (pushforward_closed_arrow j m n) = classifier_of (n ≫ m) ≫ j :=
-- closure.hat j _

-- def pullback_closed_subobject {A' : C} (n : A' ⟶ A) [mono n] :
--   C :=
-- pullback n m

-- def pullback_closed_arrow {A' : C} (n : A' ⟶ A) [mono n] :
--   pullback_closed_subobject m n ⟶ B :=
-- pullback.snd

-- instance {A' : C} (n : A' ⟶ A) [mono n] :
--   mono (pullback_closed_arrow m n) :=
-- pullback.snd_of_mono

-- instance {A' : C} (n : A' ⟶ A) [closure.closed j n] :
--   closure.closed j (pullback_closed_arrow m n) :=
-- begin
--   apply closure.closed_of_classifier_eq,
--   erw [← classify_pullback, assoc, closure.classifier_eq_of_closed],
-- end

-- lemma classify_pullback_obj {A' : C} (n : A' ⟶ A) [mono n] :
--   classifier_of (pullback_closed_arrow m n) = m ≫ classifier_of n :=
-- (classify_pullback _ _).symm

-- def classify_pullback_pushout {A' : C} (n : A' ⟶ A) [closure.closed j n] :
--   pushforward_closed_subobject j m (pullback_closed_arrow m n) ≅ A' :=
-- begin
--   apply closure.characterised j _ pullback.fst n pullback.condition,
--   apply closure.dense_top_of_pullback j pullback.condition (cone_is_pullback _ m),
-- end

-- lemma classify_pullback_pushout_comm {A' : C} (n : A' ⟶ A) [closure.closed j n] :
--   (classify_pullback_pushout j m n).hom ≫ n = pushforward_closed_arrow j m (pullback_closed_arrow m n) :=
-- begin
--   rw classify_pullback_pushout,
--   rw closure.characterised,
--   dsimp,
--   rw closure.lifting_square_prop,
--   refl,
-- end

-- lemma classify_pullback_pushforward {A' : C} (n : A' ⟶ A) [closure.closed j n] :
--   classifier_of (pushforward_closed_arrow j m (pullback_closed_arrow m n)) = classifier_of n :=
-- class_lift_of_iso _ (classify_pullback_pushout_comm j m n).symm

-- lemma classify_pushforward_pullback {B' : C} (n : B' ⟶ B) [closure.closed j n] :
--   classifier_of (pullback_closed_arrow m (pushforward_closed_arrow j m n)) = classifier_of n :=
-- begin
--   rw [classify_pullback_obj, classify_pushforward_obj, ← assoc, ← closure.classify_subobj],
--   apply closure.classifier_eq_of_closed
-- end

-- @[simps]
-- def bijection (m : B ⟶ A) [closure.dense j m] : {cm : B ⟶ Ω C // cm ≫ j = cm} ≃ {cm' : A ⟶ Ω C // cm' ≫ j = cm'} :=
-- { to_fun :=
--   begin
--     intro a,
--     let Bsubobj : pullback (truth C) a.1 ⟶ B := pullback.snd,
--     refine ⟨classifier_of (pushforward_closed_arrow j m Bsubobj), closure.classifier_eq_of_closed j _⟩,
--   end,
--   inv_fun :=
--   begin
--     intro a,
--     let Asubobj : pullback (truth C) a.1 ⟶ A := pullback.snd,
--     have : a.1 = classifier_of Asubobj,
--       apply has_subobject_classifier.uniquely _ _ ⟨_, _, cone_is_pullback _ _⟩,
--     have : classifier_of Asubobj ≫ j = classifier_of Asubobj,
--       rw ← this,
--       exact a.2,
--     haveI : closure.closed j Asubobj := closure.closed_of_classifier_eq j _ this,
--     refine ⟨classifier_of (pullback_closed_arrow m Asubobj), closure.classifier_eq_of_closed j _⟩,
--   end,
--   left_inv :=
--   begin
--     rintro ⟨a, ha⟩,
--     dsimp,
--     congr,
--     rwa [classify_pullback_obj, classify_inv, classify_pushforward_obj, ← assoc, ← closure.classify_subobj, classify_inv a],
--   end,
--   right_inv :=
--   begin
--     rintro ⟨a, ha⟩,
--     dsimp,
--     congr,
--     let Asubobj : pullback (truth C) a ⟶ A := pullback.snd,
--     have z : classifier_of Asubobj = a := classify_inv a,
--     have : classifier_of Asubobj ≫ j = classifier_of Asubobj,
--       rw [z, ha],
--     haveI := closure.closed_of_classifier_eq j _ this,
--     conv_rhs {rw ← z},
--     rw classify_pushforward_obj,
--     rw classify_pullback_obj,
--     have z₁ : m ≫ classifier_of Asubobj = classifier_of (pullback.snd : pullback Asubobj m ⟶ B) := classify_pullback Asubobj m,
--     have z₂ : classifier_of (pullback.snd : pullback (truth C) (m ≫ classifier_of Asubobj) ⟶ B) = m ≫ classifier_of Asubobj := classify_inv (m ≫ classifier_of Asubobj),
--     have : classifier_of (pullback.snd : pullback (truth C) (m ≫ classifier_of Asubobj) ⟶ B) = classifier_of (pullback.snd : pullback Asubobj m ⟶ B), cc,
--     have := pushforward_well_defined m _ _ this,
--     rw this,
--     change classifier_of (pullback_closed_arrow m Asubobj ≫ m) ≫ j = _,
--     rw ← classify_pushforward_obj,
--     rw classify_pullback_pushforward j m Asubobj,
--   end
-- }

end biject

namespace construct_limits


variables {C} {J : Type v} [𝒥₁ : small_category J] {K : J ⥤ sheaf C j} {c : cone (K ⋙ forget C j)} (t : is_limit c)
variables {B : C} (m : sub' B) (f' : m.1.left ⟶ c.X)

@[simps]
def alt_cone [closure.dense j ⟦m⟧] : cone (K ⋙ forget C j) :=
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

instance sheaf_forget_creates_limits : creates_limits (forget C j) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X := sheaf.mk' c.X $
          λ B m f' d,
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

instance sheaf_has_finite_limits : has_finite_limits.{v} (sheaf C j) :=
{ has_limits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI
  { has_limit := λ F, has_limit_of_created F (forget C j) } }

set_option pp.beta false
set_option pp.implicit false

variables {C} (j)

-- def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
--   closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
-- closure.dense_of_pullback j _ (pullback_prod' m A)

-- def sheaf_exponential (A : C) (s : sheaf C j) : sheaf C j :=
-- sheaf.mk (exp A ((forget C j).obj s)) $ λ B B' m f' d,
-- begin
--   haveI := d,
--   haveI := dense_prod_map_id j A m,
--   refine ⟨⟨⟨cart_closed.curry _, _⟩⟩, _⟩,
--   { exact extend_map s (limits.prod.map (𝟙 A) m) (cart_closed.uncurry f') },
--   { rw [← curry_natural_left, extend_map_prop s],
--     apply curry_uncurry },
--   { rintro ⟨a, ha⟩,
--     congr,
--     rw eq_curry_iff,
--     apply unique_extension s,
--     rw [← uncurry_natural_left, ha] }
-- end

-- instance : is_cartesian_closed (sheaf C j) :=
-- { cart_closed := λ A,
--   { is_adj :=
--     { right :=
--       { obj := λ s, sheaf_exponential j A.A s,
--         map := λ s₁ s₂ f, post (A.A) f,
--         map_id' := λ s, (exp.functor A.A).map_id _,
--         map_comp' := λ _ _ _ _ _, (exp.functor A.A).map_comp _ _ },
--       adj := adjunction.mk_of_hom_equiv
--       { hom_equiv := sorry,
--         hom_equiv_naturality_left_symm' := sorry,
--         hom_equiv_naturality_right' := sorry }
--     } } }

def subobject_of_closed_sheaf (A : sheaf C j) (m : sub' A.A) [c : closed j ⟦m⟧] : sheaf C j :=
sheaf.mk' m.1.left $
λ B n f' d, by exactI
begin
  haveI := m.2,
  have comm := extend_map_prop A n (f' ≫ m.1.hom),
  refine ⟨closure.lifting_square j comm.symm, _, _⟩,
  { rwa [← cancel_mono m.1.hom, assoc, lifting_square_prop j comm.symm] },
  { rintro a ha,
    rw [← cancel_mono m.1.hom, lifting_square_prop j comm.symm],
    apply unique_extension A n (f' ≫ m.1.hom),
    simp [← ha] }
end

def closed_of_subsheaf (E A : sheaf C j) (m : A ⟶ E) [hm : @mono C 𝒞 _ _ m] : closed j ⟦⟨over.mk m, hm⟩⟧ :=
begin
  -- have hr := extend_map_prop A,
  sorry,
  -- have hr := extend_map_prop A (closure.less_than_closure j m) (𝟙 _),
  -- refine ⟨⟨extend_map A (closure.less_than_closure j m) (𝟙 _), hr, _⟩⟩,
  -- rw [auto_param_eq, ← cancel_mono_id (closure.arrow j m), assoc, closure.is_lt],
  -- apply unique_ext E (closure.less_than_closure j m) m,
  -- rw [← assoc, hr, id_comp],
  -- rw closure.is_lt,
end

def closed_classifier : C := equalizer j (𝟙 _)

def eq_equiv (B : C) : (B ⟶ closed_classifier j) ≃ {cm : B ⟶ Ω C // cm ≫ j = cm} :=
{ to_fun := λ f,
  begin
    refine ⟨f ≫ equalizer.ι _ _, _⟩,
    rw [assoc, equalizer.condition, comp_id],
  end,
  inv_fun := λ f,
  begin
    apply equalizer.lift f.1 _,
    rw [f.2, comp_id]
  end,
  left_inv := λ f,
  begin
    apply equalizer.hom_ext, rw equalizer.lift_ι,
  end,
  right_inv := λ ⟨f, hf⟩,
  begin
    rw subtype.ext,
    apply equalizer.lift_ι,
  end
}

def closed_biject {A B : C} (m : A ⟶ B) [closure.dense j m] : (B ⟶ closed_classifier j) ≃ (A ⟶ closed_classifier j) :=
equiv.trans (eq_equiv j B) (equiv.trans (eq_equiv j A) (bijection j m)).symm

lemma closed_biject_prop {A B : C} (m : A ⟶ B) [closure.dense j m] (f' : B ⟶ closed_classifier j) : (closed_biject j m).to_fun f' = m ≫ f' :=
begin
  dsimp [closed_biject, equiv.trans, equiv.symm, eq_equiv, bijection],
  apply equalizer.hom_ext,
  rw equalizer.lift_ι,
  rw classify_pullback_obj,
  rw ← classify_pullback,
  have : 𝟙 _ = classifier_of (truth C),
    apply has_subobject_classifier.uniquely _ _ ⟨𝟙 _, _, pullback_square_iso' (𝟙 _) (truth C) (truth C) (𝟙 _) _⟩,
    rw [id_comp, comp_id],
  rw [← this, comp_id, assoc],
end
lemma closed_biject_prop' {A B : C} (m : A ⟶ B) [closure.dense j m] (f' : A ⟶ closed_classifier j) : m ≫ (closed_biject j m).inv_fun f' = f' :=
begin
  symmetry,
  rw ← closed_biject_prop,
  rw (closed_biject j m).right_inv,
end

def sheaf_classifier : sheaf C j :=
sheaf.mk (closed_classifier j) $ λ B B' m f' d,
begin
  haveI := d,
  refine ⟨⟨⟨_, closed_biject_prop' j m f'⟩⟩, _⟩,
  rintro ⟨a, ha⟩,
  rw ← closed_biject_prop at ha,
  congr,
  rw [← ha, (closed_biject j m).left_inv],
end

-- -- Define what it means for χ to classify the mono f.
-- structure classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) (f : U ⟶ X) (χ : X ⟶ Ω) :=
-- (k : U ⟶ Ω₀)
-- (commutes : k ≫ true = f ≫ χ)
-- (forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
-- restate_axiom classifying.forms_pullback'

-- variable (C)
-- -- A subobject classifier is a mono which classifies every mono uniquely
-- class has_subobject_classifier :=
-- (Ω Ω₀ : C)
-- (truth : Ω₀ ⟶ Ω)
-- (truth_mono' : @mono C 𝒞 _ _ truth)
-- (classifier_of : ∀ {U X} (f : U ⟶ X) [@mono C 𝒞 _ _ f], X ⟶ Ω)
-- (classifies' : ∀ {U X} (f : U ⟶ X) [mono f], classifying truth f (classifier_of f))
-- (uniquely' : ∀ {U X} (f : U ⟶ X) [@mono C 𝒞 _ _ f] (χ₁ : X ⟶ Ω),
--             classifying truth f χ₁ → χ₁ = classifier_of f)

instance : has_subobject_classifier.{v} (sheaf C j) :=
{ Ω := sheaf_classifier j,


}