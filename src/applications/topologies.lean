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

def one_equiv (X : Cᵒᵖ ⥤ Type u) :
  (one C ⟶ X) ≃ {f : Π (c : Cᵒᵖ), X.obj c // ∀ {c c' : Cᵒᵖ} (g : c ⟶ c'), X.map g (f c) = f c'} :=
{ to_fun := λ f, ⟨λ c, f.app c ⟨⟩, λ c c' g, congr_fun (f.naturality g).symm punit.star⟩,
  inv_fun := λ f,
  { app := λ c _, f.1 c,
    naturality' := λ c c' g,
    begin
      ext1 ⟨⟩,
      exact (f.2 g).symm,
    end },
  left_inv := λ f,
  begin
    ext c ⟨⟩,
    refl,
  end,
  right_inv := λ f,
  begin
    ext,
    refl,
  end }

def one_to_truth :
  (one C ⟶ Ω _) ≃ {J : Π (c : Cᵒᵖ), sieve c.unop // ∀ {c c' : Cᵒᵖ} (g : c ⟶ c'), (J c).pullback g.unop = J c'} :=
one_equiv _

lemma one_equiv_truth : (one_equiv _ (truth (Cᵒᵖ ⥤ Type u))).1 = λ c, (⊤ : sieve c.unop) :=
begin
  ext,
  refl,
end

lemma maps_eq (F : Cᵒᵖ ⥤ Type u) (f g : Ω _ ⟶ F)
  (h : ∀ (c : Cᵒᵖ) (S : sieve c.unop), f.app c S = g.app c S) : f = g :=
begin
  ext,
  apply h,
end

lemma pair_maps_eq (F : Cᵒᵖ ⥤ Type u) (f g : Ω _ ⨯ Ω _ ⟶ F) :
  (∀ {Q} (k₁ k₂ : Q ⟶ Ω _), limits.prod.lift k₁ k₂ ≫ f = limits.prod.lift k₁ k₂ ≫ g) → f = g :=
begin
  intro h,
  apply eq_of_comp_right_eq,
  intros Q pq,
  specialize h (pq ≫ limits.prod.fst) (pq ≫ limits.prod.snd),
  have : limits.prod.lift (pq ≫ limits.prod.fst) (pq ≫ limits.prod.snd) = pq,
    apply limits.prod.hom_ext; simp,
  simp_rw this at h,
  exact h,
end


@[simps]
def close (J : sieve_set C) [grothendieck J] {c : Cᵒᵖ} (S : sieve c.unop) : sieve c.unop :=
{ arrows := λ g, S.pullback g.hom ∈ J g.left,
  subs := λ d e f h k,
  begin
    change S.pullback (h ≫ f) ∈ J e,
    change S.pullback f ∈ J d at k,
    rw sieve.pullback_comp,
    apply grothendieck.stab (S.pullback f) k h,
  end }

lemma close_preserves_order {c : Cᵒᵖ} {S T : sieve c.unop} (h : S ≤ T) :
  close J S ≤ close J T :=
begin
  intros d g hg,
  change S.pullback g ∈ J d at hg,
  apply grothendieck.superset_covering (sieve.pullback_le_map h g) hg,
end

lemma close_inflationary {c : Cᵒᵖ} (S : sieve c.unop) :
  S ≤ close J S :=
begin
  intros d g hg,
  change S.pullback g ∈ J d,
  rw sieve.pullback_eq_top_iff_mem at hg,
  rw hg,
  apply grothendieck.max,
end

lemma close_idem (c : Cᵒᵖ) (S : sieve c.unop) :
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

lemma close_inter (c : Cᵒᵖ) (S T : sieve c.unop) :
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

lemma close_pullback (c d : Cᵒᵖ) (S : sieve c.unop) (f : d.unop ⟶ c.unop) :
  close J (S.pullback f) = (close J S).pullback f :=
begin
  ext e g,
  change (S.pullback f).pullback g ∈ J e ↔ S.pullback (g ≫ f) ∈ J e,
  rw S.pullback_comp,
end

@[simps]
def j : Ω (Cᵒᵖ ⥤ Type u) ⟶ Ω (Cᵒᵖ ⥤ Type u) :=
{ app := λ c S, close J S,
  naturality' := λ c c' f,
  begin
    ext1 S,
    change sieve c.unop at S,
    apply close_pullback,
  end }


-- lemma one_generating (X Y : Cᵒᵖ ⥤ Type u) (f g : X ⟶ Y) :
--   (∀ (i : one C ⟶ X), i ≫ f = i ≫ g) ↔ f = g :=
-- ⟨begin
--   intro k,
--   ext c x,
--   have q := k ((one_equiv _).symm ⟨_, _⟩),
--   apply_fun nat_trans.app at q,
--   replace q := congr_fun q c,
--   replace q := congr_fun q ⟨⟩,
--   dsimp [one_equiv] at q,
-- end
-- , λ k, by simp [k]⟩

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

def sieve_equiv_arrow (c : Cᵒᵖ) : sieve c.unop ≃ (yoneda.obj c.unop ⟶ Ω _) :=
(yoneda_sections_small c.unop (Ω _)).to_equiv.symm
def equiv_close (c : Cᵒᵖ) (S : sieve c.unop) :
  sieve_equiv_arrow _ (close J S) = sieve_equiv_arrow _ S ≫ j J :=
begin
  ext d f : 3,
  symmetry,
  apply close_pullback,
end

def sub_repr (c : C) : sieve c ≃ subq (yoneda.obj c) :=
(sieve_equiv_arrow (opposite.op c)).trans classification

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
  ((≤) : sieve c → sieve c → Prop) ≃o ((≤) : subq (yoneda.obj c) → subq (yoneda.obj c) → Prop) :=
{ to_equiv := sub_repr c,
  ord' :=
  begin
    intros S T,
    rw [sub_repr_eq, sub_repr_eq],
    change S ≤ T ↔ nonempty (_ ⟶ _),
    split,
    intro h,
      exact ⟨sub.hom_mk (sieve.le_as_functor h) (sieve.le_as_functor_comm h)⟩,
    rintro ⟨_⟩ d f hf,
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
order_iso.map_inf _

@[reassoc]
lemma and_arrow_sieve (c : Cᵒᵖ) (S T : sieve c.unop) :
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
    equiv_rw (sieve_equiv_arrow c).symm at k₁,
    equiv_rw (sieve_equiv_arrow c).symm at k₂,

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

def jsheaf_is_Jsheaf (P : sheaf (j J)) : grothendieck.sheaf J P.A :=
begin
  intros c S γ hS,
  change S.as_functor ⟶ _ at γ,
  haveI : closure.dense (j J) S.functor_inclusion := dense_inclusion _ _ _ hS,
  apply unique_extend P S.functor_inclusion γ,
end

-- This can be generalised to show it suffices to check the sheaf condition on a
-- generating set (in the sense of colimits).
def sheaf.yoneda_mk (P : Cᵒᵖ ⥤ Type u)
  (h : Π c S f' (m : S ⟶ yoneda.obj c) [closure.dense (j J) m], {f : yoneda.obj c ⟶ P // m ≫ f = f' ∧ ∀ a, m ≫ a = f' → a = f}) :
  sheaf (j J) :=
sheaf.mk' P
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

def Jsheaf_is_jsheaf (P : Cᵒᵖ ⥤ Type u) (h : grothendieck.sheaf J P) : sheaf (j J) :=
sheaf.yoneda_mk J P
begin
  introsI c S' f' m hm,
  let S := (sub_repr _).symm ⟦sub.mk' m⟧,
  have := sub_repr_eq _ S,
  -- change (sub_repr _) ((sub_repr _).symm _) = _ at this,
  rw (sub_repr _).apply_symm_apply at this,
  have : closure.dense (j J) S.functor_inclusion,
  refine ⟨_⟩,
  change closure.operator _ (subq.mk _) = _,
  rw ← this,
  apply hm.closure_eq_top,
  have : classifier_of m = classifier_of S.functor_inclusion,
    rw ← classification.apply_eq_iff_eq,
    change ⟦sub.mk' _⟧ = ⟦sub.mk' _⟧,

    --  ⟦sub.mk' (get_subobject k)⟧,
  let i := how_inj_is_classifier S.functor_inclusion m _,
  -- have := c_very_inj _,
  -- have := dense_inclusion_iff J _ S this,
  -- have := h _ S _ ‹S ∈ J c›,
  -- swap,
end

-- lemma dense_property {A E : Cᵒᵖ ⥤ Type u} (m : A ⟶ E) [closure.dense (j J) m] :
--   ∀ (c : Cᵒᵖ) (e : E.obj c), (classify (subq.mk m)).app c e ∈ J c.unop :=
-- sorry

-- lemma sieve_is {A E : Cᵒᵖ ⥤ Type u} (m : A ⟶ E) [closure.dense (j J) m] (c : Cᵒᵖ) (e : E.obj c)
--   (d : C) (f : d ⟶ _) :
--   over.mk f ∈ sieve.arrows ((classify (subq.mk m)).app c e) ↔ ∃ (x : A.obj _), m.app _ x = E.map f.op e :=
-- iff.rfl

-- lemma aux {A E P : Cᵒᵖ ⥤ Type u} (m : A ⟶ E) [mono m] (σ : A ⟶ P) {c : Cᵒᵖ} (e : E.obj c) {d d' : C}
--   (f : d ⟶ c.unop) (g : d' ⟶ d) (f₁ : _) (hf₁ : m.app (opposite.op d') f₁ = E.map (f.op ≫ g.op) e)
--   (f₂) (hf₂ : m.app (opposite.op d) f₂ = E.map f.op e) :
--   σ.app (opposite.op d') f₁ = σ.app (opposite.op d') (A.map g.op f₂) :=
-- begin
--   rw [E.map_comp, types_comp_apply] at hf₁,
--   have := congr_arg (E.map g.op) hf₂,
--   change (m.app (opposite.op d) ≫ E.map g.op) f₂ = _ at this,
--   rw ← m.naturality at this,
--   rw ← hf₁ at this,
--   dsimp at this,
--   have : mono (m.app (opposite.op d')) := preserves_mono_of_preserves_pullback ((evaluation Cᵒᵖ (Type u)).obj (opposite.op d')) A E m,
--   rw mono_iff_injective at this,
--   have : A.map g.op f₂ = f₁,
--     apply this, assumption,
--   rw this,
-- end


-- c: Cᵒᵖ
-- e: E.obj c
-- dd': C
-- f: d ⟶ opposite.unop c
-- g: d' ⟶ d
-- hf: over.mk f ∈ ((classify (subq.mk m)).app c e).arrows
-- hf₁: m.app (opposite.op d') (classical.some (sieve.downward_closed ((classify (subq.mk m)).app c e) hf g)) = E.map (f.op ≫ g.op) e
-- hf₂: m.app (opposite.op d) (classical.some hf) = E.map f.op e
-- ⊢ σ.app (opposite.op d') (classical.some (sieve.downward_closed ((classify (subq.mk m)).app c e) hf g)) = σ.app (opposite.op d') (A.map g.op (classical.some hf))


-- def Jsheaf_is_jsheaf (P : Cᵒᵖ ⥤ Type u) (h : grothendieck.sheaf J P) : sheaf (j J) :=
-- sheaf.mk' P
-- begin
--   replace h := (grothendieck.sheaf'_equiv_sheaf J P).hom h,
--   introsI E A m σ _,
--   rw grothendieck.sheaf' at h,
--   let special_sieve : Π (c : Cᵒᵖ) (e : E.obj c), sieve c.unop := λ c e, ((classify (subq.mk m)).app c e),
--   let family : Π c e, grothendieck.matching_family' P (special_sieve c e),
--   { intros c e,
--     refine ⟨λ d f hf, σ.app (opposite.op d) (classical.some hf), _⟩,
--     intros d d' f g hf,
--     change σ.app _ (classical.some (sieve.downward_closed _ hf g)) = (σ.app (opposite.op d) ≫ P.map _) (classical.some hf),
--     rw ← σ.naturality,
--     have hf₁ := classical.some_spec ((sieve.downward_closed (special_sieve c e) hf g)),
--     have hf₂ := classical.some_spec hf,
--     exact aux m _ e f _ _ hf₁ _ (classical.some_spec hf) },
--   let p : Π (c : Cᵒᵖ) (e : E.obj c), P.obj c,
--     intros, apply (h c.unop _ (family c e) (dense_property J m _ e)).1.1.1,
--   have hp : ∀ (c) (e : E.obj c) (d : C) (f : d ⟶ c.unop) (hf), P.map f.op (p _ e) = (family c e).val f hf,
--     intros,
--     apply (h c.unop _ (family c e) (dense_property J m _ e)).1.1.2 f hf,
--   have hp' : ∀ (c) (e : E.obj c) (d : C) (f : d ⟶ c.unop) (hf), P.map f.op (p _ e) = σ.app (opposite.op d) (classical.some hf),
--     intros,
--     rw hp,
--   refine ⟨_, _, _⟩,
--   { refine ⟨p, _⟩,
--     intros c c' f,
--     ext e,
--     dsimp,
--     rw hp',

--   },
  -- { refine ⟨λ c e, (h c.unop _ (family c e) (dense_property J m _ e)).1.1.1, _⟩,
  --   intros c c' f,
  --   ext e,
  --   dsimp only [types_comp_apply],
  --   have := (h c.unop _ (family c e) (dense_property J m _ e)).1.1.2,
  --   have : ∀ {d} (f : d ⟶ c.unop) (hf : over.mk f ∈ sieve.arrows ((classify (subq.mk m)).app c e)),
  --     P.map _ (h c.unop _ (family c e) (dense_property J m _ e)).1.1.1 = sorry,

    -- refine ⟨λ c e, _, _⟩,
    -- { apply (h c.unop _ _ (dense_property J m _ e)).1.1.1,
    --   refine ⟨λ d f hf, _, _⟩,
    --   apply σ.app (opposite.op d),
    --   apply classical.some hf,
    --   intros d d' f g hf,
    --   change σ.app _ (classical.some (sieve.downward_closed _ hf g)) = (σ.app (opposite.op d) ≫ P.map _) (classical.some hf),
    --   rw ← σ.naturality,
    --   have hf₁ := classical.some_spec ((sieve.downward_closed ((classify (subq.mk m)).app c e) hf g)),
    --   have hf₂ := classical.some_spec hf,
    --   exact aux m _ e f _ _ hf₁ _ (classical.some_spec hf) },
    -- { intros c c' f,
    --   ext1 e,
    --   dsimp only [types_comp_apply],
    --   have z : P.map f _ = _ := (h c.unop _ _ (dense_property J m _ e)).1.1.2 f.unop _,
    --   rw z,
    --   dsimp,

    -- }
    -- },
--   { sorry },
--   { sorry },
-- end

-- def Jsheaf_is_jsheaf (P : Cᵒᵖ ⥤ Type u) (h : grothendieck.sheaf J P) : sheaf (j J) :=
-- sheaf.mk' P
-- begin
--   replace h := (grothendieck.sheaf'_equiv_sheaf J P).hom h,
--   introsI E A m σ _,
--   refine ⟨_, _, _⟩,
--   refine ⟨_, _⟩,
--   intros c e,
--   let S : sieve c.unop := ⟨λ f, ∃ (t : A.obj _), m.app _ t = E.map f.hom.op e, _⟩,
--   have : S ∈ J c.unop,
--     sorry,
--   sorry,
--   intros,
--   change ∃ (x : A.obj (opposite.op Y)), m.app _ _ = E.map f.op e at a,
--   change ∃ (x : A.obj (opposite.op Z)), m.app (opposite.op Z) _ = E.map (f.op ≫ g.op) e,
--   cases a,
--   refine ⟨A.map g.op a_w, _⟩,
--   change (A.map g.op ≫ m.app _) _ = _,
--   rw m.naturality,
--   dsimp,
--   rw [a_h, E.map_comp],
--   refl,
--   -- specialize h c.unop,
-- end

end category_theory