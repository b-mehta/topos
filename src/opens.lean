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

@[derive partial_order]
def opens_sieve' := {s : set (opens X) // ∀ V ∈ s, V ≤ U ∧ ∀ W ≤ V, W ∈ s }

@[simps]
def equivalence' :
  ((≤) : opens_sieve' U → opens_sieve' U → Prop) ≃o ((≤) : sieve U → sieve U → Prop) :=
{ inv_fun := λ S,
  { val := λ V, ∃ (h : V ≤ U), S.arrows (over.mk (hom_of_le h)),
    property := by { rintro V ⟨VU, hVU⟩, exact ⟨VU, λ W WV, ⟨_, S.downward_closed hVU (hom_of_le WV)⟩⟩ } },
  to_fun := λ S,
  { arrows := λ f, f.left ∈ S.1,
    subs := λ V W VU WV hVU, ((S.2 V) hVU).2 W (le_of_hom WV) },
  right_inv := λ S, sieve.ext_iff $ λ V VU,
    ⟨by { rintro ⟨_, q⟩, convert q }, by { rintro hf, refine ⟨le_of_hom VU, _⟩, convert hf }⟩,
  left_inv := λ S, subtype.ext_val $ funext $ λ V,
    propext ⟨by {rintro ⟨_, q⟩, exact q}, λ hV, ⟨(S.2 V hV).1, hV⟩⟩,
  ord' := λ a b, ⟨λ h V VU hVU, h hVU, λ h V hV, h _ (hom_of_le (a.2 _ hV).1) hV⟩ }

instance : order_top (opens_sieve' U) :=
{ top := ⟨λ V, V ≤ U, by tidy⟩,
  le_top := λ S V hV, (S.2 V hV).1,
  ..topological_space.opens.opens_sieve'.partial_order _ }

def is_covering' (s : opens_sieve' U) : Prop := ∀ x ∈ U, ∃ V, V ∈ s.1 ∧ x ∈ V

def restrict' {U : opens X} (V : opens X) (s : opens_sieve' U) : opens_sieve' V :=
begin
  refine subtype.map (set.image (⊓ V)) _ s,
  rintros S hS _ ⟨W', hW', rfl⟩,
  refine ⟨lattice.inf_le_right _ _, λ V' hV', ⟨V' ⊓ W', _, _⟩⟩,
  apply (hS _ hW').2,
  refine lattice.inf_le_right _ _,
  simp only [],
  rw inf_assoc,
  apply inf_of_le_left hV',
end

lemma restrict_equivalence {U V : opens X} (VU : V ⟶ U) (s : opens_sieve' U) :
  equivalence' _ (restrict' V s) = sieve.pullback (equivalence' _ s) VU :=
sieve.ext_iff $ λ W WV,
  ⟨ by {rintro ⟨W, h, q⟩, cases q, exact (s.2 _ h).2 _ (lattice.inf_le_left _ _)},
    λ hW, ⟨_, hW, inf_of_le_left (le_of_hom WV)⟩⟩

lemma covering'_trans (r s : opens_sieve' U) (hs : is_covering' U s)
  (hr : ∀ {Y : opens X} (a : Y ≤ U), s.1 Y → is_covering' _ (restrict' Y r)) :
  is_covering' U r :=
begin
  intros x hx,
  obtain ⟨V, Vs, xV⟩ := hs x hx,
  obtain ⟨_, ⟨W, Wr, rfl⟩, xW⟩ :=
    hr (lattice.inf_le_left U V) ((s.2 _ Vs).2 _ (lattice.inf_le_right _ _)) x ⟨hx, xV⟩,
  exact ⟨_, Wr, xW.1⟩,
end

end

def covering : sieve_set (opens X) := λ U S, is_covering' _ ((equivalence' _).symm S)

lemma covering_sieve (U : opens X) (S : sieve U) :
  S ∈ covering X U ↔ ∀ x ∈ U, ∃ V, x ∈ V ∧ ∃ (f : V ≤ U), over.mk (hom_of_le f) ∈ S.arrows :=
ball_congr (λ x hx, exists_congr (λ V, and_comm _ _))

instance : grothendieck (covering X) :=
{ max := λ U,
  begin
    change U.is_covering' _,
    rw order_iso.map_top (equivalence' U).symm,
    intros x hx,
    exact ⟨U, le_refl _, hx⟩,
  end,
  stab := λ U V s hs f x hx,
  begin
    equiv_rw (equivalence' U).to_equiv.symm at s,
    change ∀ (x ∈ U), _ at hs,
    simp only [order_iso.coe_fn_to_equiv, equiv.symm_symm, order_iso.symm_apply_apply] at hs,
    simp only [order_iso.coe_fn_to_equiv],
    rw ← restrict_equivalence,
    simp only [order_iso.symm_apply_apply],
    dsimp [restrict', subtype.map],
    obtain ⟨W, hW₁, hW₂⟩ := hs x (le_of_hom f hx),
    refine ⟨_ ⊓ _, ⟨W, hW₁, rfl⟩, hW₂, hx⟩,
  end,
  trans := λ U s hs r h,
  begin
    equiv_rw (equivalence' U).to_equiv.symm at s,
    equiv_rw (equivalence' U).to_equiv.symm at r,
    change is_covering' _ _,
    change is_covering' _ _ at hs,
    simp only [order_iso.coe_fn_to_equiv, order_iso.symm_apply_apply, equiv.symm_symm] at ⊢ hs h,
    refine U.covering'_trans r s hs _,
    intros V VU Vs,
    specialize h (hom_of_le VU) _,
    rw ← restrict_equivalence at h,
    change is_covering' _ _ at h,
    simp only [order_iso.coe_fn_to_equiv, order_iso.symm_apply_apply, equiv.symm_symm] at h,
    apply h,
    apply Vs,
  end }

end

end topological_space.opens
