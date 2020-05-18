import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.types
import category_theory.limits.shapes.binary_products
import pullbacks
import subobject_classifier
import cartesian_closed

universes v v₂ u

/-!
# Types

Show that Type has a subobject classifier (assuming unique choice).
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

-- Note this is obviously implied by full choice.
axiom unique_choice {α : Sort u} [subsingleton α] : nonempty α → α

noncomputable def get_unique {α : Sort u} (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a b, p a → p b → a = b) : {a // p a} :=
begin
  haveI: subsingleton {a // p a} := _,
  apply unique_choice,
    cases h₁,
    split, exact ⟨h₁_w, h₁_h⟩,
  split,
    rintros ⟨a, ha⟩ ⟨b, hb⟩,
    congr,
    apply h₂ a b ha hb,
end

noncomputable def get_unique_value {α : Sort u} (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a b, p a → p b → a = b) : α := (get_unique p h₁ h₂).val
lemma get_unique_property {α : Sort u} (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a b, p a → p b → a = b) : p (get_unique_value p h₁ h₂) := (get_unique p h₁ h₂).property

noncomputable instance types_has_subobj_classifier : @has_subobject_classifier Type category_theory.types :=
{ Ω := Prop,
  Ω₀ := unit,
  truth := λ _, true,
  truth_mono' := ⟨λ A f g _, begin ext i, apply subsingleton.elim end⟩,
  classifier_of := λ A B f mon b, ∃ (a : A), f a = b,
  classifies' :=
  begin
    intros A B f mon,
    refine {top := λ _, (), comm := _, is_pb := _},
    funext, simp, use x,
    refine pullback_cone.is_limit.mk _ _ _ _ _,
    intros c i,
    show A,
    have: pullback_cone.fst c ≫ _ = pullback_cone.snd c ≫ _ := pullback_cone.condition c,
    have: (pullback_cone.snd c ≫ (λ (b : B), ∃ (a : A), f a = b)) i,
      rw ← this, dsimp, trivial,
    dsimp at this,
    apply get_unique_value _ this_1 _,
    intros,
    rw ← a_2 at a_1,
    rw mono_iff_injective at mon,
    apply mon a_1,
    intros c,
    dsimp,
    apply subsingleton.elim,
    intros c,
    ext, dunfold pullback_cone.snd pullback_cone.mk, simp,
    exact get_unique_property (λ (a : A), f a = c.π.app walking_cospan.right x) _ _,
    intros c m J,
    dsimp,
    resetI,
    rw ← cancel_mono f,
    ext,
    simp,
    have := get_unique_property (λ (a : A), f a = c.π.app walking_cospan.right x) _ _,
    rw this,
    erw ← congr_fun (J walking_cospan.right) x,
    refl
  end,
  uniquely' :=
  begin
    introv _ fst, ext x,
    rw set_classifier fst x
  end }

noncomputable def invert_mono {U X : Type u} (m : U ⟶ X) [mon : mono m] (t : X) (h : ∃ i, m i = t) : {i : U // m i = t} :=
begin
  apply get_unique _ h _,
  intros,
  rw mono_iff_injective at mon,
  apply mon,
  rw [a_1, a_2]
end

-- instance types_has_subobj_classifier : @has_subobject_classifier (Type u) category_theory.types :=
-- { Ω := ulift Prop,
--   Ω₀ := punit,
--   truth := λ _, ulift.up true,
--   truth_mono' := ⟨λ A f g h, by { ext i, apply subsingleton.elim }⟩,
--   classifier_of := λ A B f mon b, ulift.up (∃ (a : A), f a = b),
--   classifies' := λ U X m hm,
--   { top := λ _, punit.star,
--     comm :=
--     begin
--       ext1,
--       dsimp,
--       congr' 1,
--       rw [eq_iff_iff, true_iff],
--       exact ⟨x, rfl⟩,
--     end,
--     is_pb :=
--     begin
--       haveI := hm,
--       refine is_limit.mk' _ _,
--       intro s,
--       refine ⟨_, subsingleton.elim _ _, _, _⟩,
--       { change s.X ⟶ U,
--         intro i,
--         refine (invert_mono m (s.snd i) _).1,
--         have a := congr_fun s.condition i,
--         dsimp at a,
--         replace a : true = ∃ (a : U), m a = s.snd i := congr_arg ulift.down a,
--         rw ← a,
--         trivial },
--       { dsimp,
--         ext i,
--         dsimp,
--         have := (invert_mono m (s.snd i) _).2,
--       },




--     end
--   }
-- }

@[simps]
def currying_equiv (A X Y : Type u) : ((prod_functor.obj A).obj X ⟶ Y) ≃ (X ⟶ A → Y) :=
{ to_fun := λ f b a,
  begin
    refine f ⟨λ j, walking_pair.cases_on j a b, λ j₁ j₂, _⟩,
    rintros ⟨⟨rfl⟩⟩, refl
  end,
  inv_fun := λ g ab, g (ab.1 walking_pair.right) (ab.1 walking_pair.left),
  left_inv := λ f, by { ext ⟨ba⟩, dsimp, congr, ext ⟨j⟩, simp },
  right_inv := λ _, rfl }

instance type_exponentiable (A : Type u) : exponentiable A :=
{ is_adj :=
  { right := adjunction.right_adjoint_of_equiv (currying_equiv A) (
    begin
      intros X X' Y f g,
      dsimp [currying_equiv],
      ext,
      congr,
      dunfold limits.prod.map,
      rw types.types_limit_map,
      congr, ext ⟨j⟩,
      simp,
      simp,
    end),
    adj := adjunction.adjunction_of_equiv_right _ _ } }

instance type_cc : is_cartesian_closed (Type u) :=
begin
  split,
  intro A,
  apply_instance
end
