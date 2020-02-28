open nat

universe u

inductive pfin (n : nat) : Type u
| mk (val : nat) (is_lt : val < n) : pfin

namespace pfin

@[reducible]
def val {n} : pfin n → nat
| ⟨v, _⟩ := v

@[reducible]
def is_lt {n} : ∀ (a : pfin n), a.val < n
| ⟨_, h⟩ := h

protected def lt {n} (a b : pfin n) : Prop :=
a.val < b.val

protected def le {n} (a b : pfin n) : Prop :=
a.val ≤ b.val

instance {n} : has_lt (pfin n)  := ⟨pfin.lt⟩
instance {n} : has_le (pfin n)  := ⟨pfin.le⟩

instance decidable_lt {n} (a b : pfin n) :  decidable (a < b) :=
nat.decidable_lt _ _

instance decidable_le {n} (a b : pfin n) : decidable (a ≤ b) :=
nat.decidable_le _ _

def {w} elim0 {α : Sort w} : pfin 0 → α
| ⟨_, h⟩ := absurd h (nat.not_lt_zero _)

variable {n : nat}

lemma eq_of_veq : ∀ {i j : pfin n}, (val i) = (val j) → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : pfin n}, i = j → (val i) = (val j)
| ⟨iv, ilt⟩ .(_) rfl := rfl

lemma ne_of_vne {i j : pfin n} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {i j : pfin n} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eq_of_veq h') h

end pfin

open pfin

instance (n : nat) : decidable_eq (pfin n) :=
λ i j, decidable_of_decidable_of_iff
  (nat.decidable_eq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩
