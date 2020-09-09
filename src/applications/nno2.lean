import equiv
import applications.nno

universes v u

namespace category_theory
open category limits limits.prod

local attribute [instance] has_finite_products_of_has_finite_limits

variables {C : Type u} [category.{v} C] [topos C] (N : natural_number_object C)

namespace natural_number_object

variable {Q : C}

lemma zero_compl_succ : is_compl (subq.mk N.o) (subq.mk N.succ) :=
disjoint.compl_coproj N.coprod_cofan

lemma zero_decidable : ⊤ ≤ (subq.mk N.o) ⊔ (subq.mk N.o)ᶜ :=
begin
  rw sup_comm,
  rw ← is_compl.right_le_iff N.zero_compl_succ,
  rw le_compl_iff,
  rw inf_comm,
  apply N.zero_compl_succ.inf_eq_bot,
end

lemma compl_zero : (subq.mk N.o)ᶜ = subq.mk N.succ :=
begin
  apply is_compl.right_unique _ N.zero_compl_succ,
  refine ⟨inf_compl (subq.mk N.o) ▸ le_refl _, N.zero_decidable⟩,
end

def le : sub (N.N ⨯ N.N) := (sub.pullback N.subtract).obj (sub.mk' N.o)

def is_le (n m : Q ⟶ N.N) : Prop := factors_through ❲n, m❳ N.le.arrow

lemma is_le_iff_sub_eq_zero {n m : Q ⟶ N.N} : N.is_le n m ↔ N.subtract ❲n, m❳ = N.zero :=
{ mp :=
  begin
    rintro ⟨h⟩,
    let : Q ⟶ pullback N.o N.subtract := h.left,
    have : h.left ≫ pullback.snd = ❲n, m❳ := over.w h,
    rw [← this, expand_apply, assoc, ← pullback.condition],
    change _ ≫ _ ≫ N.o = unit ≫ N.o,
    rw ← assoc, congr' 1,
  end,
  mpr := λ h, ⟨over.hom_mk (pullback.lift (terminal.from _) ❲n, m❳ h.symm) (pullback.lift_snd _ _ _)⟩ }

end natural_number_object

end category_theory