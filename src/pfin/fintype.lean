import data.fintype
import pfin.lemmas

universe u

namespace fintype
open finset

def equiv_pfin_of_forall_mem_list {α : Type u} [fintype α] [decidable_eq α]
  {l : list α} (h : ∀ x:α, x ∈ l) (nd : l.nodup) : α ≃ pfin (l.length) :=
{ to_fun := λ a, ⟨_, list.index_of_lt_length.2 (h a)⟩,
  inv_fun := λ i, l.nth_le i.val i.is_lt,
  left_inv := λ a, begin unfold pfin.val, simp *, end,
  right_inv := λ ⟨i, h⟩, begin
    apply pfin.eq_of_veq, simp [pfin.val],
    apply list.nodup_iff_nth_le_inj.mp nd _ _ (list.index_of_lt_length.mpr (list.nth_le_mem _ _ _)) h,
    simp,
  end }

def equiv_pfin (α: Type u) [fintype α] [decidable_eq α] : trunc (α ≃ pfin (fintype.card α)) :=
begin
  unfold card finset.card,
  exact quot.rec_on_subsingleton (@univ α _).1
    (λ l (h : ∀ x:α, x ∈ l) (nd : l.nodup), trunc.mk (equiv_pfin_of_forall_mem_list h nd))
    mem_univ_val univ.2
end

end fintype

namespace list

def pfin_range (n : ℕ) : list (pfin n) :=
(list.range n).pmap pfin.mk (λ _, list.mem_range.1)

@[simp] lemma mem_pfin_range {n : ℕ} (a : pfin n) : a ∈ list.pfin_range n :=
mem_pmap.2 ⟨a.val, mem_range.2 a.is_lt, pfin.eta _ _⟩

lemma nodup_pfin_range (n : ℕ) : (pfin_range n).nodup :=
nodup_pmap (λ _ _ _ _, pfin.veq_of_eq) (nodup_range _)

end list

instance (n : ℕ) : fintype (pfin n) :=
⟨⟨quot.mk _ (list.pfin_range n), list.nodup_pfin_range n⟩, list.mem_pfin_range⟩
