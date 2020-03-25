import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.types
import pullbacks
import subobject_classifier
import locally_cartesian_closed

universes v v₂ u

/-!
# Types

Show that Type has a subobject classifier (assuming choice).
-/

open category_theory category_theory.category category_theory.limits

instance types_has_pullbacks: has_pullbacks.{u} (Type u) := ⟨limits.has_limits_of_shape_of_has_limits⟩

lemma set_classifier {U X : Type} {f : U ⟶ X} {χ₁ : X ⟶ Prop} (q : @classifying _ category_theory.types _ unit _ _ (λ _, true) f χ₁) :
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

-- -- TODO: can we make this computable?
noncomputable instance types_has_subobj_classifier : @has_subobject_classifier Type category_theory.types :=
{ Ω := Prop,
  Ω₀ := unit,
  truth := λ _, true,
  truth_mono' := ⟨λ A f g _, begin ext i, apply subsingleton.elim end⟩,
  classifier_of := λ A B f mon, λ b, ∃ (a : A), f a = b,
  classifies' :=
  begin
    intros A B f mon,
    refine {k := λ _, (), commutes := _, forms_pullback' := _},
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
  end,
  uniquely' :=
  begin
    introv _ fst, ext x,
    rw set_classifier fst x
  end
}

@[simps]
def currying_equiv (A X Y : Type u) : ((prodinl A).obj X ⟶ Y) ≃ (X ⟶ A → Y) :=
{ to_fun := λ f b a,
  begin
    refine f ⟨λ j, walking_pair.cases_on j a b, λ j₁ j₂, _⟩,
    rintros ⟨⟨rfl⟩⟩, refl
  end,
  inv_fun := λ g ab, g (ab.1 walking_pair.right) (ab.1 walking_pair.left),
  left_inv := λ f, by { ext ⟨ba⟩, dsimp, congr, ext ⟨j⟩, simp },
  right_inv := λ _, rfl }

instance type_exponentials (A : Type u) : exponentiable A :=
{ exponentiable :=
  { right := adjunction.right_adjoint_of_equiv (currying_equiv _) (
    begin
      intros X X' Y f g, ext, dsimp [currying_equiv], congr,
      show lim.map (@map_pair (Type u) _ _ _ _ _ id f) _ = _,
      rw types.types_limit_map,
      congr, ext ⟨j⟩, simp, simp
    end),
    adj := adjunction.adjunction_of_equiv_right _ _ } }

instance type_cc : is_cartesian_closed (Type u) :=
begin
  split,
  intro A,
  apply_instance
end
