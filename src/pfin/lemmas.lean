import data.nat.basic
import pfin.basic pfin.ops

universe u
open pfin nat function

/-- `pfin 0` is empty -/
def pfin_zero_elim {C : Sort*} : pfin 0 → C :=
λ x, false.elim $ nat.not_lt_zero x.val x.is_lt

def pfin_zero_elim' {α : pfin 0 → Sort u} : ∀(x : pfin 0), α x
| ⟨n, hn⟩ := false.elim (nat.not_lt_zero n hn)

namespace pfin
variables {n m : ℕ} {a b : pfin.{u} n}

@[simp] protected lemma eta (a : pfin n) (h : a.val < n) : (⟨a.val, h⟩ : pfin n) = a :=
by cases a; refl

protected lemma ext_iff (a b : pfin n) : a = b ↔ a.val = b.val :=
iff.intro (congr_arg _) pfin.eq_of_veq

lemma injective_val {n : ℕ} : injective (val : pfin n → ℕ) := λ _ _, pfin.eq_of_veq

lemma eq_iff_veq (a b : pfin n) : a = b ↔ a.val = b.val :=
⟨veq_of_eq, eq_of_veq⟩

@[simp] protected lemma mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
  pfin.mk a ha = pfin.mk b hb ↔ a = b :=
⟨pfin.mk.inj, λ h, by subst h⟩

instance pfin_to_nat (n : ℕ) : has_coe (pfin n) nat := ⟨pfin.val⟩

@[simp] lemma mk_val {m n : ℕ} (h : m < n) : (⟨m, h⟩ : pfin n).val = m := rfl

@[simp] lemma coe_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : pfin n) : ℕ) = m := rfl

lemma coe_eq_val (a : pfin n) : (a : ℕ) = a.val := rfl

@[simp] lemma val_one  {n : ℕ} : (1 : pfin (n+2)).val = 1 := rfl
@[simp] lemma val_two  {n : ℕ} : (2 : pfin (n+3)).val = 2 := rfl
@[simp] lemma coe_zero {n : ℕ} : ((0 : pfin (n+1)) : ℕ) = 0 := rfl
@[simp] lemma coe_one  {n : ℕ} : ((1 : pfin (n+2)) : ℕ) = 1 := rfl
@[simp] lemma coe_two  {n : ℕ} : ((2 : pfin (n+3)) : ℕ) = 2 := rfl

instance {n : ℕ} : decidable_linear_order (pfin n) :=
decidable_linear_order.lift pfin.val (@pfin.eq_of_veq _) (by apply_instance)

lemma exists_iff {p : pfin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
⟨λ h, exists.elim h (λ ⟨i, hi⟩ hpi, ⟨i, hi, hpi⟩),
  λ h, exists.elim h (λ i hi, ⟨⟨i, hi.fst⟩, hi.snd⟩)⟩

lemma forall_iff {p : pfin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
⟨λ h i hi, h ⟨i, hi⟩, λ h ⟨i, hi⟩, h i hi⟩

lemma zero_le (a : pfin (n + 1)) : 0 ≤ a := zero_le a.val

lemma lt_iff_val_lt_val : a < b ↔ a.val < b.val := iff.rfl

lemma le_iff_val_le_val : a ≤ b ↔ a.val ≤ b.val := iff.rfl

@[simp] lemma succ_val (j : pfin n) : j.succ.val = j.val.succ :=
by cases j; simp [pfin.succ]

protected theorem succ.inj (p : pfin.succ a = pfin.succ b) : a = b :=
by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

@[simp] lemma succ_inj {a b : pfin n} : a.succ = b.succ ↔ a = b :=
⟨λh, succ.inj h, λh, by rw h⟩

lemma injective_succ (n : ℕ) : injective (@pfin.succ n) :=
λa b, succ.inj

lemma succ_ne_zero {n} : ∀ k : pfin n, pfin.succ k ≠ 0
| ⟨k, hk⟩ heq := nat.succ_ne_zero k $ (pfin.ext_iff _ _).1 heq

@[simp] lemma pred_val (j : pfin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [pfin.pred]

@[simp] lemma succ_pred : ∀(i : pfin (n+1)) (h : i ≠ 0), (i.pred h).succ = i
| ⟨0,     h⟩ hi := by contradiction
| ⟨n + 1, h⟩ hi := rfl

@[simp] lemma pred_succ (i : pfin n) {h : i.succ ≠ 0} : i.succ.pred h = i :=
by cases i; refl

@[simp] lemma pred_inj :
  ∀ {a b : pfin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
| ⟨0,   _⟩  b         ha hb := by contradiction
| ⟨i+1, _⟩  ⟨0,   _⟩  ha hb := by contradiction
| ⟨i+1, hi⟩ ⟨j+1, hj⟩ ha hb := by simp [pfin.eq_iff_veq]

/-- The greatest value of `pfin (n+1)` -/
def last (n : ℕ) : pfin (n+1) := ⟨_, n.lt_succ_self⟩

/-- `cast_lt i h` embeds `i` into a `pfin` where `h` proves it belongs into.  -/
def cast_lt (i : pfin m) (h : i.val < n) : pfin n := ⟨i.val, h⟩

/-- `cast_le h i` embeds `i` into a larger `pfin` type.  -/
def cast_le (h : n ≤ m) (a : pfin n) : pfin m := cast_lt a (lt_of_lt_of_le a.is_lt h)

/-- `cast eq i` embeds `i` into a equal `pfin` type. -/
def cast (eq : n = m) : pfin n → pfin m := cast_le $ le_of_eq eq

/-- `cast_add m i` embeds `i : pfin n` in `pfin (n+m)`. -/
def cast_add (m) : pfin n → pfin (n + m) := cast_le $ le_add_right n m

/-- `cast_succ i` embeds `i : pfin n` in `pfin (n+1)`. -/
def cast_succ : pfin n → pfin (n + 1) := cast_add 1

/-- `succ_above p i` embeds `pfin n` into `pfin (n + 1)` with a hole around `p`. -/
def succ_above (p : pfin (n+1)) (i : pfin n) : pfin (n+1) :=
if i.val < p.val then i.cast_succ else i.succ

/-- `pred_above p i h` embeds `i : pfin (n+1)` into `pfin n` by ignoring `p`. -/
def pred_above (p : pfin (n+1)) (i : pfin (n+1)) (hi : i ≠ p) : pfin n :=
if h : i < p
then i.cast_lt (lt_of_lt_of_le h $ nat.le_of_lt_succ p.is_lt)
else i.pred $
  have p < i, from lt_of_le_of_ne (le_of_not_gt h) hi.symm,
  ne_of_gt (lt_of_le_of_lt (zero_le p) this)

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `pfin.pred`. -/
def sub_nat (m) (i : pfin (n + m)) (h : m ≤ i.val) : pfin n :=
⟨i.val - m, by simp [nat.sub_lt_right_iff_lt_add h, i.is_lt]⟩

/-- `add_nat i h` adds `m` on `i`, generalizes `pfin.succ`. -/
def add_nat (m) (i : pfin n) : pfin (n + m) :=
⟨i.val + m, add_lt_add_right i.is_lt _⟩

/-- `nat_add i h` adds `n` on `i` -/
def nat_add (n) {m} (i : pfin m) : pfin (n + m) :=
⟨n + i.val, add_lt_add_left i.is_lt _⟩

theorem le_last (i : pfin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

@[simp] lemma cast_val (k : pfin n) (h : n = m) : (pfin.cast h k).val = k.val := rfl

@[simp] lemma cast_succ_val (k : pfin n) : k.cast_succ.val = k.val := rfl

@[simp] lemma cast_lt_val (k : pfin m) (h : k.val < n) : (k.cast_lt h).val = k.val := rfl

@[simp] lemma cast_le_val (k : pfin m) (h : m ≤ n) : (k.cast_le h).val = k.val := rfl

@[simp] lemma cast_add_val (k : pfin m) : (k.cast_add n).val = k.val := rfl

@[simp] lemma last_val (n : ℕ) : (last n).val = n := rfl

@[simp] lemma succ_last (n : ℕ) : (last n).succ = last (n.succ) := rfl

@[simp] lemma cast_succ_cast_lt (i : pfin (n + 1)) (h : i.val < n) : cast_succ (cast_lt i h) = i :=
pfin.eq_of_veq rfl

@[simp] lemma cast_lt_cast_succ {n : ℕ} (a : pfin n) (h : a.val < n) : cast_lt (cast_succ a) h = a :=
by cases a; refl

@[simp] lemma sub_nat_val (i : pfin (n + m)) (h : m ≤ i.val) : (i.sub_nat m h).val = i.val - m :=
rfl

@[simp] lemma add_nat_val (i : pfin (n + m)) (h : m ≤ i.val) : (i.add_nat m).val = i.val + m :=
rfl

@[simp] lemma cast_succ_inj {a b : pfin n} : a.cast_succ = b.cast_succ ↔ a = b :=
by simp [eq_iff_veq]

lemma cast_succ_ne_last (a : pfin n) : cast_succ a ≠ last n :=
by simp [eq_iff_veq, ne_of_lt a.is_lt]

lemma eq_last_of_not_lt {i : pfin (n+1)} (h : ¬ i.val < n) : i = last n :=
le_antisymm (le_last i) (not_lt.1 h)

lemma cast_succ_pfin_succ (n : ℕ) (j : pfin n) :
  cast_succ (pfin.succ j) = pfin.succ (cast_succ j) :=
by simp [pfin.ext_iff]

def clamp (n m : ℕ) : pfin (m + 1) := pfin.of_nat $ min n m

@[simp] lemma clamp_val (n m : ℕ) : (clamp n m).val = min n m :=
nat.mod_eq_of_lt $ nat.lt_succ_iff.mpr $ min_le_right _ _

lemma injective_cast_le {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : injective (pfin.cast_le h)
| ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ eq := pfin.eq_of_veq $ show i₁ = i₂, from pfin.veq_of_eq eq

lemma injective_cast_succ (n : ℕ) : injective (@pfin.cast_succ n) :=
injective_cast_le (le_add_right n 1)

theorem succ_above_ne (p : pfin (n+1)) (i : pfin n) : p.succ_above i ≠ p :=
begin
  assume eq,
  unfold pfin.succ_above at eq,
  split_ifs at eq with h;
    simpa [lt_irrefl, nat.lt_succ_self, eq.symm] using h
end

@[simp] lemma succ_above_descend : ∀(p i : pfin (n+1)) (h : i ≠ p), p.succ_above (p.pred_above i h) = i
| ⟨p, hp⟩ ⟨0,   hi⟩ h := pfin.eq_of_veq $ by simp [succ_above, pred_above]; split_ifs; simp * at *
| ⟨p, hp⟩ ⟨i+1, hi⟩ h := pfin.eq_of_veq
  begin
    have : i + 1 ≠ p, by rwa [(≠), pfin.ext_iff] at h,
    unfold succ_above pred_above,
    split_ifs with h1 h2;
      simp only [pfin.cast_succ_cast_lt, add_right_inj, pred_val, ne.def, cast_succ_val,
                 nat.pred_succ, pfin.succ_pred, add_right_inj] at *,
    exact (this (le_antisymm h2 (le_of_not_gt h1))).elim
  end

@[simp] lemma pred_above_succ_above (p : pfin (n+1)) (i : pfin n) (h : p.succ_above i ≠ p) :
  p.pred_above (p.succ_above i) h = i :=
begin
  unfold pfin.succ_above,
  apply eq_of_veq,
  split_ifs with h₀,
  { simp [pred_above, h₀, lt_iff_val_lt_val], },
  { unfold pred_above,
    split_ifs with h₁,
    { exfalso,
      rw [lt_iff_val_lt_val, succ_val] at h₁,
      exact h₀ (lt_trans (nat.lt_succ_self _) h₁) },
    { rw [pred_succ] } }
end

section rec

@[elab_as_eliminator] def succ_rec
  {C : ∀ n, pfin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : ∀ {n : ℕ} (i : pfin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

@[elab_as_eliminator] def succ_rec_on {n : ℕ} (i : pfin n)
  {C : ∀ n, pfin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem succ_rec_on_zero {C : ∀ n, pfin n → Sort*} {H0 Hs} (n) :
  @pfin.succ_rec_on (succ n) 0 C H0 Hs = H0 n :=
rfl

@[simp] theorem succ_rec_on_succ {C : ∀ n, pfin n → Sort*} {H0 Hs} {n} (i : pfin n) :
  @pfin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (pfin.succ_rec_on i H0 Hs) :=
by cases i; refl

@[elab_as_eliminator] def cases
  {C : pfin (succ n) → Sort*} (H0 : C 0) (Hs : ∀ i : pfin n, C (i.succ)) :
  ∀ (i : pfin (succ n)), C i
| ⟨0, h⟩ := H0
| ⟨succ i, h⟩ := Hs ⟨i, lt_of_succ_lt_succ h⟩

@[simp] theorem cases_zero {n} {C : pfin (succ n) → Sort*} {H0 Hs} : @pfin.cases n C H0 Hs 0 = H0 :=
rfl

@[simp] theorem cases_succ {n} {C : pfin (succ n) → Sort*} {H0 Hs} (i : pfin n) :
  @pfin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

lemma forall_pfin_succ {P : pfin (n+1) → Prop} :
  (∀ i, P i) ↔ P 0 ∧ (∀ i:pfin n, P i.succ) :=
⟨λ H, ⟨H 0, λ i, H _⟩, λ ⟨H0, H1⟩ i, pfin.cases H0 H1 i⟩

lemma exists_pfin_succ {P : pfin (n+1) → Prop} :
  (∃ i, P i) ↔ P 0 ∨ (∃i:pfin n, P i.succ) :=
⟨λ ⟨i, h⟩, pfin.cases or.inl (λ i hi, or.inr ⟨i, hi⟩) i h,
  λ h, or.elim h (λ h, ⟨0, h⟩) $ λ⟨i, hi⟩, ⟨i.succ, hi⟩⟩

end rec

end pfin
