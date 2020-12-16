import applications.functor_category
import grothendieck
import sheaf
import category.element
import tactic.equiv_rw
import data.quot
import pullback_colimit
import category.colimits

namespace category_theory

universes v u

variables {C : Type u} [small_category C] (J : sieve_set C) [grothendieck J]

open classifier limits category

noncomputable theory

@[ext]
structure closure_operator (α : Type*) [has_le α] :=
(to_fun : α → α)
(ord' : ∀ {x y : α}, x ≤ y → to_fun x ≤ to_fun y)
(inflate' : ∀ x, x ≤ to_fun x)
(idem' : ∀ x, to_fun (to_fun x) = to_fun x)

instance (α : Type*) [has_le α] : has_coe_to_fun (closure_operator α) :=
⟨_, closure_operator.to_fun⟩

instance (α : Type*) [has_le α] : has_le (closure_operator α) :=
⟨λ c₁ c₂, ∀ x, c₁ x ≤ c₂ x⟩

lemma closure_operator.ord {α : Type*} [has_le α] (c : closure_operator α) {x y : α} (h : x ≤ y) :
  c x ≤ c y :=
c.ord' h

lemma closure_operator.inflate {α : Type*} [has_le α] (c : closure_operator α) (x : α) :
  x ≤ c x := c.inflate' x

lemma closure_operator.idem {α : Type*} [has_le α] (c : closure_operator α) (x : α) :
  c (c x) = c x := c.idem' x

/-- The sieve-set induced by a closure operator on sieves. -/
def grothendieck_from_natural_operator (c : Π (X : C), closure_operator (sieve X)) :
  sieve_set C :=
λ X S, c X S = ⊤

/-- If a closure operator on sieves is natural, it induces a Grothendieck topology. -/
instance natural_operator_is_grothendieck (c : Π (X : C), closure_operator (sieve X))
  (hc : ∀ (X Y : C) (f : X ⟶ Y) (S : sieve Y), (c Y S).pullback f = c _ (S.pullback f)) :
grothendieck (grothendieck_from_natural_operator c) :=
{ max := λ X,
  begin
    apply top_unique,
    apply (c _).inflate,
  end,
  stab := λ X Y S hS f,
  begin
    change _ = _ at hS,
    change _ = _,
    rw [← hc, hS, sieve.pullback_top],
  end,
  trans := λ X S hS T hT,
  begin
    change _ = _,
    rw ← (c X).idem,
    apply top_unique,
    change _ = _ at hS,
    rw ← hS,
    apply (c _).ord,
    intros Y g hg,
    rw sieve.pullback_eq_top_iff_mem,
    rw hc,
    apply hT g hg,
  end }

@[simps]
def close {c : C} (S : sieve c) : sieve c :=
{ arrows := λ g, grothendieck.covers J S g.hom,
  subs := λ d e f h k,
  begin
    change S.pullback (h ≫ f) ∈ J e,
    change S.pullback f ∈ J d at k,
    rw sieve.pullback_comp,
    apply grothendieck.stab (S.pullback f) k h,
  end }


lemma close_preserves_order {c : C} {S T : sieve c} (h : S ≤ T) :
  close J S ≤ close J T :=
begin
  intros d g hg,
  change S.pullback g ∈ J d at hg,
  apply grothendieck.superset_covering (sieve.pullback_le_map h g) hg,
end

lemma close_inflationary {c : C} (S : sieve c) :
  S ≤ close J S :=
begin
  intros d g hg,
  change S.pullback g ∈ J d,
  rw sieve.pullback_eq_top_iff_mem at hg,
  rw hg,
  apply grothendieck.max,
end

lemma close_idem (c : C) (S : sieve c) :
  close J (close J S) = close J S :=
begin
  apply le_antisymm,
    intros d g hg,
    change (close J S).pullback g ∈ J d at hg,
    apply grothendieck.trans _ hg,
    intros e g' hg',
    change (S.pullback g).pullback g' ∈ J e,
    rw ← S.pullback_comp,
    exact hg',
  apply close_preserves_order J (close_inflationary _ _),
end

lemma close_inter (c : C) (S T : sieve c) :
  close J (S ⊓ T) = close J S ⊓ close J T :=
begin
  apply le_antisymm,
  { refine le_inf (close_preserves_order _ inf_le_left) (close_preserves_order _ inf_le_right) },
  rintros d g ⟨hg₁, hg₂⟩,
  change S.pullback g ∈ J d at hg₁,
  change (S ⊓ T).pullback g ∈ J d,
  rw sieve.pullback_inter,
  apply grothendieck.intersection_covering hg₁ hg₂,
end

lemma close_pullback (c d : C) (S : sieve c) (f : d ⟶ c) :
  close J (S.pullback f) = (close J S).pullback f :=
begin
  ext e g,
  change (S.pullback f).pullback g ∈ J e ↔ S.pullback (g ≫ f) ∈ J e,
  rw S.pullback_comp,
end

lemma incl_iff_closure_eq_top (c : C) (S : sieve c) : S ∈ J c ↔ close J S = ⊤ :=
begin
  split,
    intro h,
    ext d f,
    change S.pullback f ∈ J d ↔ true,
    simpa using grothendieck.stab S h f,
  rw [close],
  intro q,
  refine grothendieck.trans ⊤ (grothendieck.max _) _ _,
  intros d g hg,
  rw ← q at hg,
  exact hg,
end

/-- Natural closure operators on the set of sieves are the same thing as Grothendieck topologies. -/
def operators_equiv_topology :
  {c : Π (X : C), closure_operator (sieve X) // ∀ X Y f S, (c Y S).pullback f = c X (S.pullback f)}
≃ {J : sieve_set C // grothendieck J} :=
{ to_fun := λ c, ⟨grothendieck_from_natural_operator c.1, category_theory.natural_operator_is_grothendieck _ c.2⟩,
  inv_fun := λ J, by { haveI := J.2, refine ⟨λ X, ⟨close J.1, λ x y, close_preserves_order _, close_inflationary _, close_idem _ _⟩, λ X Y f S, _⟩, symmetry, apply close_pullback, },
  left_inv :=
  begin
    rintro ⟨c₁, c₂⟩,
    ext x S y f,
    dsimp [close, grothendieck.covers, grothendieck_from_natural_operator],
    change c₁ y (S.pullback f) = ⊤ ↔ over.mk f ∈ (c₁ x S).arrows,
    rw ← c₂,
    rw sieve.pullback_eq_top_iff_mem,
  end,
  right_inv :=
  begin
    rintro ⟨J, _⟩,
    resetI,
    ext c S,
    apply (incl_iff_closure_eq_top J c S).symm,
  end }

@[simps]
def j : Ω (Cᵒᵖ ⥤ Type u) ⟶ Ω (Cᵒᵖ ⥤ Type u) :=
{ app := λ c S, close J S,
  naturality' := λ c c' f,
  begin
    ext1 S,
    change sieve c.unop at S,
    apply close_pullback,
  end }

lemma yoneda_generates (X Y : Cᵒᵖ ⥤ Type u) (f g : X ⟶ Y)
  (h : ∀ (c : Cᵒᵖ) (k : yoneda.obj c.unop ⟶ X), k ≫ f = k ≫ g) :
  f = g :=
begin
  ext c t,
  specialize h c ((yoneda_sections_small c.unop X).inv t),
  have := congr_arg (λ i, nat_trans.app i c) h,
  dsimp [yoneda_lemma, ulift_trivial] at this,
  have z := congr_fun this (has_hom.hom.unop (𝟙 _)),
  dsimp at z,
  rw [X.map_id] at z,
  exact z,
end

def sieve_equiv_arrow (c : C) : sieve c ≃ (yoneda.obj c ⟶ Ω _) :=
(yoneda_sections_small c (Ω _)).to_equiv.symm

lemma equiv_close (c : C) (S : sieve c) :
  sieve_equiv_arrow _ (close J S) = sieve_equiv_arrow _ S ≫ j J :=
begin
  ext d f : 3,
  symmetry,
  apply close_pullback,
end

def sub_repr (c : C) : sieve c ≃ subq (yoneda.obj c) :=
(sieve_equiv_arrow c).trans classification

lemma sub_repr_eq (c : C) (S : sieve c) : sub_repr c S = subq.mk S.functor_inclusion :=
begin
  change classification _ = _,
  rw ← classification.eq_symm_apply,
  ext c' f c'' g,
  change over.mk (g ≫ f) ∈ S.arrows ↔ ∃ (x : {h // over.mk h ∈ S.arrows}), x.1 = g ≫ f,
  rw [subtype.exists],
  simp,
end

def sieve_subq (c : C) :
sieve c ≃o subq (yoneda.obj c) :=
{ to_equiv := sub_repr c,
  map_rel_iff' :=
  begin
    intros S T,
    rw [sub_repr_eq, sub_repr_eq],
    change S ≤ T ↔ nonempty (_ ⟶ _),
    split,
    intro h,
      exact ⟨sub.hom_mk (sieve.le_as_functor h) (sieve.le_as_functor_comm h)⟩,
    rintro ⟨a⟩ d f hf,
    let f' := a.left.app (opposite.op d) ⟨f, hf⟩,
    have := sub.w a,
    dsimp at *,
    have q := congr_arg (λ t, nat_trans.app t (opposite.op d)) this,
    dsimp at q,
    replace q := congr_fun q ⟨f, hf⟩,
    dsimp at q,
    rw ← q,
    apply (a.left.app (opposite.op d) ⟨f, hf⟩).2,
  end }

lemma inclusion_inter (c : C) (S T : sieve c) :
  sieve_subq _ (S ⊓ T) = sieve_subq _ S ⊓ sieve_subq _ T :=
order_iso.map_inf _ _ _

@[reassoc]
lemma and_arrow_sieve (c : C) (S T : sieve c) :
  (prod.lift (sieve_equiv_arrow _ S) (sieve_equiv_arrow _ T) ≫ and_arrow _) = sieve_equiv_arrow _ (S ⊓ T) :=
begin
  have : ∀ (S : sieve _), sieve_equiv_arrow c S = classify (sieve_subq _ S),
    intro S,
    change _ = classify (classification (sieve_equiv_arrow c S)),
    symmetry,
    apply classification.left_inv,
  rw [this, this, this],
  rw and_property,
  rw inclusion_inter,
end

instance : topology (j J) :=
{ ax1 :=
  begin
    ext c ⟨⟩ d f,
    change J d ((⊤ : sieve _).pullback f) ↔ true,
    rw sieve.pullback_top,
    simp only [iff_true],
    exact grothendieck.max d,
  end,
  ax2 :=
  begin
    ext c S : 3,
    apply close_idem,
  end,
  ax3 :=
  begin
    apply yoneda_generates,
    intros c k,
    equiv_rw prod.equiv (yoneda.obj c.unop) (Ω _) (Ω _) at k,
    cases k with k₁ k₂,
    change prod.lift k₁ k₂ ≫ _ = prod.lift k₁ k₂ ≫ _ ≫ _,
    rw prod.lift_map_assoc,
    equiv_rw (sieve_equiv_arrow c.unop).symm at k₁,
    equiv_rw (sieve_equiv_arrow c.unop).symm at k₂,

    rw [← equiv_close, ← equiv_close, and_arrow_sieve, and_arrow_sieve_assoc, ← equiv_close],
    rw (sieve_equiv_arrow _).apply_eq_iff_eq,
    rw close_inter,
  end }.


def dense_inclusion (c : C) (S : sieve c) (h : S ∈ J c) : closure.dense (j J) S.functor_inclusion :=
begin
  constructor,
  change classification (classify (subq.mk _) ≫ _) = _,
  rw ← sub_repr_eq,
  dsimp only [sub_repr, equiv.trans],
  change classification (classification.symm (classification _) ≫ _) = _,
  rw classification.symm_apply_apply,
  erw ← equiv_close,
  change sieve_subq _ _ = _,
  rw ← order_iso.map_top (sieve_subq c),
  congr' 1,
  ext d f,
  change S.pullback f ∈ J d ↔ true,
  simpa using grothendieck.stab S h f,
end

lemma dense_inclusion_iff (c : C) (S : sieve c) (h : closure.dense (j J) S.functor_inclusion) :
  S ∈ J c :=
begin
  have := h.closure_eq_top,
  change classification (classify (subq.mk _) ≫ _) = _ at this,
  rw ← sub_repr_eq at this,
  dsimp only [sub_repr, equiv.trans] at this,
  change classification (classification.symm (classification _) ≫ _) = _ at this,
  rw classification.symm_apply_apply at this,
  erw ← equiv_close at this,
  change sieve_subq _ _ = _ at this,
  rw ← order_iso.map_top (sieve_subq c) at this,
  erw (sieve_subq c).to_equiv.apply_eq_iff_eq at this,
  rw close at this,
  refine grothendieck.trans ⊤ (grothendieck.max _) _ _,
  intros d g hg,
  rw ← this at hg,
  exact hg,
end

def jsheaf_is_Jsheaf (P : Cᵒᵖ ⥤ Type u) (h : sheaf_condition (j J) P) : grothendieck.sheaf_condition J P :=
begin
  intros c S γ hS,
  change S.as_functor ⟶ _ at γ,
  haveI : closure.dense (j J) S.functor_inclusion := dense_inclusion _ _ _ hS,
  apply h S.functor_inclusion γ,
end

-- This can be generalised to show it suffices to check the sheaf condition on a
-- generating set (in the sense of colimits).
def sheaf.yoneda_mk (P : Cᵒᵖ ⥤ Type u)
  (h : Π c S f' (m : S ⟶ yoneda.obj c) [closure.dense (j J) m], {f : yoneda.obj c ⟶ P // m ≫ f = f' ∧ ∀ a, m ≫ a = f' → a = f}) :
  sheaf_condition (j J) P :=
sheaf_condition.mk' _ _
begin
  introsI E A m σ _,
  let A' : (E.elements)ᵒᵖ → (Cᵒᵖ ⥤ Type u) := λ i, pullback ((the_cocone E).ι.app i) m,
  let m' : Π (i : E.elementsᵒᵖ), A' i ⟶ yoneda.obj i.unop.1.unop := λ i, pullback.fst,
  let top_map : Π (i : E.elementsᵒᵖ), A' i ⟶ A := λ i, pullback.snd,
  have pb : ∀ (i : E.elementsᵒᵖ), m' i ≫ _ = top_map i ≫ m := λ i, pullback.condition,
  let A'diagram : E.elementsᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u),
  { refine { functor . obj := A',
             map := λ i j f,
              pullback.lift (m' i ≫ yoneda.map f.unop.1.unop) (top_map i)
                (by erw [← pb i, assoc, (the_cocone E).w f]), map_id' := _, map_comp' := _},
    { intro j,
      apply pullback.hom_ext;
      simp },
    { intros i₁ i₂ i₃ f g,
      apply pullback.hom_ext; simp } },
  let τ : A'diagram ⟶ ((category_of_elements.π E).left_op ⋙ yoneda) :=
    { nat_trans . app := m', naturality' := λ i j f, pullback.lift_fst _ _ _ },
  let A'cocone : cocone A'diagram,
    refine ⟨A, λ i, top_map i, _⟩,
    intros i j f,
    rw pullback.lift_snd,
    apply (comp_id _).symm,
  let A'colimit := pullback_colimit A'cocone (is_a_limit E) τ m pb (λ i, cone_is_pullback _ _),
  let h' : Π (i : E.elementsᵒᵖ), {f // m' i ≫ f = top_map i ≫ σ ∧ ∀ a, m' i ≫ a = top_map i ≫ σ → a = f} :=
    λ i, (h _ _ (top_map i ≫ σ) (m' i)),
  let h'₁ : Π (i : E.elementsᵒᵖ), yoneda.obj i.unop.1.unop ⟶ P := λ i, (h' i).1,
  have h'₂ : ∀ (i : E.elementsᵒᵖ), m' i ≫ h'₁ i = top_map i ≫ σ := λ i, (h' i).2.1,
  have h'₃ : ∀ (i : E.elementsᵒᵖ) a, m' i ≫ a = top_map i ≫ σ → a = h'₁ i := λ i, (h' i).2.2,
  have legs : ∀ (i j : E.elementsᵒᵖ) (f : i ⟶ j), yoneda.map (has_hom.hom.unop f).1.unop ≫ h'₁ j = h'₁ i ≫ 𝟙 P,
  { intros,
    rw comp_id,
    apply h'₃ i,
    let hf : A' i ⟶ A' j := pullback.lift (m' i ≫ yoneda.map f.unop.1.unop) (top_map i)
                              (by erw [← pb i, assoc, (the_cocone E).w f]),
    have : hf ≫ m' j = m' i ≫ yoneda.map _ := pullback.lift_fst _ _ _,
    rw ← reassoc_of this,
    rw h'₂ j,
    apply pullback.lift_snd_assoc },
  refine ⟨(is_a_limit E).desc ⟨P, h'₁, legs⟩, _, _⟩,
  { apply A'colimit.hom_ext,
    intro i,
    rw ← pullback.condition_assoc,
    rw (is_a_limit E).fac,
    apply h'₂ },
  { intros q hq,
    apply (is_a_limit E).hom_ext,
    intro i,
    rw (is_a_limit E).fac,
    apply h'₃ i,
    rw pullback.condition_assoc,
    rw hq }
end.

def Jsheaf_is_jsheaf (P : Cᵒᵖ ⥤ Type u) (h : grothendieck.sheaf_condition J P) : sheaf_condition (j J) P :=
sheaf.yoneda_mk J P
begin
  introsI c S' f' m hm,
  let S := (sub_repr _).symm ⟦sub.mk' m⟧,
  have same_class := sub_repr_eq _ S,
  rw (sub_repr _).apply_symm_apply at same_class,
  have : closure.dense (j J) S.functor_inclusion,
  refine ⟨_⟩,
  change closure.operator _ (subq.mk _) = _,
  rw ← same_class,
  apply hm.closure_eq_top,
  have := dense_inclusion_iff J _ S this,
  have : classifier_of m = classifier_of S.functor_inclusion,
    change classify ⟦sub.mk' m⟧ = classify ⟦sub.mk' S.functor_inclusion⟧,
    rw same_class,
  let i := how_inj_is_classifier m S.functor_inclusion this,
  have hi : i.hom ≫ _ = _ := c_very_inj this,
  refine ⟨(h _ S (i.inv ≫ f') ‹S ∈ J c›).1.1.1, _, _⟩,
  rw [← hi, assoc, (h _ S (i.inv ≫ f') ‹S ∈ J c›).1.1.2], simp,
  intros a ha,
  apply subtype.ext_iff.1 ((h _ S (i.inv ≫ f') ‹S ∈ J c›).2 ⟨a, _⟩),
  rw iso.eq_inv_comp,
  rw reassoc_of hi,
  rw ha,
end

def equivalent_sheaf_conditions (P : Cᵒᵖ ⥤ Type u) :
  grothendieck.sheaf_condition J P ≃ sheaf_condition (j J) P :=
{ to_fun := Jsheaf_is_jsheaf _ _,
  inv_fun := jsheaf_is_Jsheaf _ _,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

end category_theory