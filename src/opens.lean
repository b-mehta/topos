import topology.category.Top.opens
import grothendieck
import tactic.equiv_rw

universes u

open category_theory topological_space category_theory.limits

namespace topological_space.opens

section
variables (X : Type u) [topological_space X]

section
variables {X} (U V : opens X)

structure opens_sieve :=
(collection : set (opens X))
(all_under : ∀ V ∈ collection, V ≤ U)
(down_closed : ∀ (V ∈ collection) {W}, W ≤ V → W ∈ collection)

@[ext]
lemma opens_sieve.ext {U : opens X} {s₁ s₂ : opens_sieve U} :
  s₁.collection = s₂.collection → s₁ = s₂ :=
begin
  intro h,
  cases s₁,
  cases s₂,
  congr,
  exact h,
end

instance sieve_order : partial_order (opens_sieve U) :=
partial_order.lift opens_sieve.collection (λ x y, opens_sieve.ext)

instance opens_sieve_top : has_top (opens_sieve U) :=
{ top :=
  { collection := λ V, V ≤ U,
    all_under := λ V hV, hV,
    down_closed := λ V hV W hW, le_trans hW hV } }

def is_covering (s : opens_sieve U) : Prop := Sup s.collection = U

@[simps]
def restrict {U V : opens X} (h : V ≤ U) (s : opens_sieve U) : opens_sieve V :=
{ collection := (λ W, V ⊓ W) '' s.collection,
  all_under := by { rintro _ ⟨W, hW, rfl⟩, exact inf_le_left },
  down_closed :=
  begin
    rintro _ ⟨W, hW, rfl⟩ W' hW',
    refine ⟨W ⊓ W', s.down_closed _ hW inf_le_left, _⟩,
    dsimp,
    rw ← inf_assoc,
    apply inf_of_le_right hW',
  end }

def equivalence : sieve U ≃ opens_sieve U :=
{ to_fun := λ s,
  { collection := λ V, ∃ (a : V ⟶ U), s.arrows (over.mk a),
    all_under := λ _ ⟨hV, _⟩, hV.1.1,
    down_closed := λ _ q _ hW, exists.elim q (λ _ q, ⟨_, s.subs ⟨⟨hW⟩⟩ q⟩) },
  inv_fun := λ s,
  { arrows := λ V, s.collection V.1,
    subs := λ Y Z f g hf, s.down_closed Y hf g.down.down },
  left_inv := λ s,
  begin
    ext V,
    split,
    { rintro ⟨p, q⟩,
      convert q },
    { intro p,
      refine ⟨f, _⟩,
      convert p },
  end,
  right_inv :=
  begin
    rintro ⟨s, s₁, s₂⟩,
    ext V,
    split,
    { rintro ⟨_, q⟩, apply q },
    { intro hV, exact ⟨⟨⟨s₁ _ hV⟩⟩, hV⟩ },
  end }

lemma opens_sieve_top_eq_top : equivalence U ⊤ = ⊤ :=
begin
  ext W,
  split,
  { rintro ⟨h, _⟩,
    exact h.down.down },
  { intro _,
    exact ⟨⟨⟨a⟩⟩, trivial⟩ }
end

lemma covering_trans (r s : opens_sieve U) (hs : is_covering U s)
  (hr : ∀ {Y : opens X} (a : Y ≤ U), s.collection Y → is_covering _ (restrict a r)) :
  is_covering U r :=
begin
  ext _ x,
  simp only [set.mem_Union, set.sUnion_image, opens.Sup_s],
  split,
  { rintro ⟨V, hV, hx⟩,
    apply r.all_under V hV hx },
  { intro hx,
    rw [is_covering, subtype.ext, set.ext_iff] at hs,
    simp only [set.mem_Union, set.sUnion_image, opens.Sup_s] at hs,
    obtain ⟨V, hV, hxV⟩ := (hs x).2 hx,
    specialize hr (inf_le_left : U ⊓ V ≤ U) (s.down_closed _ hV inf_le_right),
    rw [is_covering, subtype.ext, set.ext_iff] at hr,
    simp only [set.mem_Union, set.sUnion_image, opens.Sup_s] at hr,
    obtain ⟨_, ⟨W, hW, rfl⟩, _, hxW⟩ := (hr x).2 ⟨hx, hxV⟩,
    exact ⟨_, hW, hxW⟩ },
end

lemma restrict_is_pullback (s : sieve U) (h : V ≤ U) :
  restrict h (equivalence _ s) = equivalence _ (s.pullback ⟨⟨h⟩⟩) :=
begin
  ext W,
  split,
  { rintro ⟨W, ⟨hW, hW₂⟩, rfl⟩,
    refine ⟨⟨⟨inf_le_left⟩⟩, _⟩,
    change over.mk (_ ≫ _) ∈ _,
    dsimp,
    have : s.arrows (over.mk (⟨⟨(inf_le_right : V ⊓ W ≤ W)⟩⟩ ≫ hW)),
      apply sieve.downward_closed _ hW₂,
    convert this },
  { rintro ⟨hW, q⟩,
    refine ⟨W, ⟨_, q⟩, inf_of_le_right hW.down.down⟩ },
end

lemma restrict_is_pullback_symm (s : opens_sieve U) (h : V ≤ U) :
  (equivalence _).symm (restrict h s) = ((equivalence _).symm s).pullback ⟨⟨h⟩⟩ :=
begin
  rw [equiv.symm_apply_eq, ← restrict_is_pullback, equiv.apply_symm_apply],
end

end

def covering : sieve_set (opens X) := λ U S, is_covering _ (equivalence _ S)

instance : grothendieck (covering X) :=
{ max := λ U,
  begin
    change is_covering _ _,
    rw opens_sieve_top_eq_top,
    exact cSup_Iic,
  end,
  stab := λ U V s hs,
  begin
    rintro ⟨⟨h⟩⟩,
    equiv_rw (equivalence U) at s,
    change is_covering _ _ at hs,
    change is_covering _ _,
    rw [← restrict_is_pullback, restrict],
    rw [equiv.apply_symm_apply, is_covering, subtype.ext, set.ext_iff] at *,
    simp only [set.mem_Union, set.sUnion_image, opens.Sup_s, exists_prop, set.mem_image, exists_and_distrib_left] at *,
    intro x,
    split,
    { rintro ⟨_, ⟨_, _, rfl⟩, hx, _⟩,
      exact hx },
    { intro hx,
      obtain ⟨W, hW, hxV⟩ := (hs x).2 (h hx),
      exact ⟨_, ⟨W, hW, rfl⟩, hx, hxV⟩ }
  end,
  trans := λ U s hs r h,
  begin
    equiv_rw (equivalence U) at s,
    equiv_rw (equivalence U) at r,
    change is_covering _ _ at hs,
    rw [equiv.apply_symm_apply] at hs,
    apply covering_trans _ _ s hs,
    intros Y a hY,
    rw equiv.apply_symm_apply,
    specialize h ⟨⟨a⟩⟩ hY,
    rw [← restrict_is_pullback_symm] at h,
    change is_covering _ _ at h,
    rw equiv.apply_symm_apply at h, exact h,
  end }

end

end topological_space.opens
