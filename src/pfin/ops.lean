import pfin.basic

namespace pfin
open nat
variable {n : nat}

protected def succ : pfin n → pfin (succ n)
| ⟨a, h⟩ := ⟨nat.succ a, succ_lt_succ h⟩

def of_nat {n : nat} (a : nat) : pfin (succ n) :=
⟨a % succ n, nat.mod_lt _ (nat.zero_lt_succ _)⟩

private lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

protected def add : pfin n → pfin n → pfin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a + b) % n, mlt h⟩

protected def mul : pfin n → pfin n → pfin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨(a * b) % n, mlt h⟩

private lemma sublt {a b n : nat} (h : a < n) : a - b < n :=
lt_of_le_of_lt (nat.sub_le a b) h

protected def sub : pfin n → pfin n → pfin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a - b, sublt h⟩

private lemma modlt {a b n : nat} (h₁ : a < n) (h₂ : b < n) : a % b < n :=
begin
  cases b with b,
  {simp [mod_zero], assumption},
  {have h : a % (succ b) < succ b,
   apply nat.mod_lt _ (nat.zero_lt_succ _),
   exact lt.trans h h₂}
end

protected def mod : pfin n → pfin n → pfin n
| ⟨a, h₁⟩ ⟨b, h₂⟩ := ⟨a % b, modlt h₁ h₂⟩

private lemma divlt {a b n : nat} (h : a < n) : a / b < n :=
lt_of_le_of_lt (nat.div_le_self a b) h

protected def div : pfin n → pfin n → pfin n
| ⟨a, h⟩ ⟨b, _⟩ := ⟨a / b, divlt h⟩

instance : has_zero (pfin (succ n)) := ⟨⟨0, succ_pos n⟩⟩
instance : has_one (pfin (succ n))  := ⟨of_nat 1⟩
instance : has_add (pfin n)         := ⟨pfin.add⟩
instance : has_sub (pfin n)         := ⟨pfin.sub⟩
instance : has_mul (pfin n)         := ⟨pfin.mul⟩
instance : has_mod (pfin n)         := ⟨pfin.mod⟩
instance : has_div (pfin n)         := ⟨pfin.div⟩

lemma of_nat_zero : @of_nat n 0 = 0 := rfl

lemma add_def (a b : pfin n) : (a + b).val = (a.val + b.val) % n :=
show (pfin.add a b).val = (a.val + b.val) % n, from
by cases a; cases b; simp [pfin.add]

lemma mul_def (a b : pfin n) : (a * b).val = (a.val * b.val) % n :=
show (pfin.mul a b).val = (a.val * b.val) % n, from
by cases a; cases b; simp [pfin.mul]

lemma sub_def (a b : pfin n) : (a - b).val = a.val - b.val :=
show (pfin.sub a b).val = a.val - b.val, from
by cases a; cases b; simp [pfin.sub]

lemma mod_def (a b : pfin n) : (a % b).val = a.val % b.val :=
show (pfin.mod a b).val = a.val % b.val, from
by cases a; cases b; simp [pfin.mod]

lemma div_def (a b : pfin n) : (a / b).val = a.val / b.val :=
show (pfin.div a b).val = a.val / b.val, from
by cases a; cases b; simp [pfin.div]

lemma lt_def (a b : pfin n) : (a < b) = (a.val < b.val) :=
show (pfin.lt a b) = (a.val < b.val), from
by cases a; cases b; simp [pfin.lt]

lemma le_def (a b : pfin n) : (a ≤ b) = (a.val ≤ b.val) :=
show (pfin.le a b) = (a.val ≤ b.val), from
by cases a; cases b; simp [pfin.le]

lemma val_zero : (0 : pfin (succ n)).val = 0 := rfl

def pred {n : nat} : ∀ i : pfin (succ n), i ≠ 0 → pfin n
| ⟨a, h₁⟩ h₂ := ⟨a.pred,
  begin
    have this : a ≠ 0,
    { have aux₁ := vne_of_ne h₂,
      dsimp at aux₁, rw val_zero at aux₁, exact aux₁ },
    exact nat.pred_lt_pred this h₁
  end⟩

end pfin
