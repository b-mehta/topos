import category_theory.limits.shapes
import category_theory.limits.types
import pullbacks
import test

universes v v₂ u

open category_theory category_theory.category category_theory.limits

instance types_has_pullbacks: has_pullbacks.{u} (Type u) := ⟨limits.has_limits_of_shape_of_has_limits⟩

lemma set_classifier {U X : Type} {f : U ⟶ X} (h : mono f) {χ₁ : X ⟶ Prop} (q : @classifies Type _ Prop unit U X (λ _, true) f h χ₁) :
  ∀ x, χ₁ x ↔ ∃ a, f a = x :=
begin
  obtain ⟨ka, la, ma⟩ := q,
  intro x,
  split, intro,
    have: ((𝟙 _ : unit ⟶ unit) ≫ λ (_ : unit), true) = (λ (_ : unit), x) ≫ χ₁,
      ext y, simp, show true ↔ χ₁ x, simpa,
    set new_cone := pullback_cone.mk (𝟙 unit) (λ _, x) this,
    set g := ma.lift new_cone,
    use g (),
    have := ma.fac new_cone walking_cospan.right, simp at this,
    have := congr_fun this (), simp at this,
    exact this,
  rintro ⟨t, rfl⟩, have := congr_fun la t, simp at this, exact this,
end

-- TODO: can we make this computable?
noncomputable instance types_has_subobj_classifier : has_subobject_classifier Type :=
{ Ω := Prop,
  Ω₀ := unit,
  truth := λ _, true,
  truth_mono' := ⟨λ A f g _, begin ext i, apply subsingleton.elim end⟩,
  classifies' := λ A B f mon, ⟨λ b, ∃ (a : A), f a = b, -- is this the right prop to use? I (BM) think so
  begin
    refine ⟨λ _, (), _, _⟩,
    funext, simp, use x,
    refine ⟨λ c i, _, _, _⟩,
    show A,
    have: pullback_cone.fst c ≫ _ = pullback_cone.snd c ≫ _ := pullback_cone.condition c,
    have: (pullback_cone.snd c ≫ (λ (b : B), ∃ (a : A), f a = b)) i,
      rw ← this, dsimp, trivial,
    dsimp at this,
    exact classical.some this_1,
    intros c, apply pi_app_left,
    ext, apply subsingleton.elim,
    ext, dunfold pullback_cone.snd pullback_cone.mk, simp,
    have: (pullback_cone.snd c ≫ (λ (b : B), ∃ (a : A), f a = b)) x,
      rw ← pullback_cone.condition c, trivial,
    apply classical.some_spec this,
    intros c m J,
    resetI,
    rw ← cancel_mono f,
    ext, simp,
    have: (pullback_cone.snd c ≫ (λ (b : B), ∃ (a : A), f a = b)) x,
      rw ← pullback_cone.condition c, trivial,
    erw classical.some_spec this,
    simp at J, have Jl := congr_fun (J walking_cospan.right) x,
    simp at Jl, exact Jl,
  end
⟩, uniquely' :=
  begin
    introv fst snd, ext x,
    show χ₁ x ↔ χ₂ x,
    rw set_classifier h fst x,
    rw set_classifier h snd x,
  end
}