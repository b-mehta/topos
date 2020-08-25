import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.types
import category_theory.limits.shapes.binary_products
import subobject_classifier

universes v v₂ u

/-!
# Types

Show that Type has a subobject classifier (assuming unique choice).
-/

open category_theory category_theory.category category_theory.limits

local attribute [instance] has_finite_limits_of_has_limits
local attribute [instance] has_finite_products_of_has_finite_limits

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

noncomputable def invert_mono {U X : Type u} (m : U ⟶ X) [mon : mono m] (t : X) (h : ∃ i, m i = t) : {i : U // m i = t} :=
begin
  apply get_unique _ h _,
  intros,
  rw mono_iff_injective at mon,
  apply mon,
  rw [a_1, a_2]
end

def truth : punit ⟶ ulift Prop := λ _, ulift.up true
instance : mono truth := ⟨λ A f g _, by ext⟩

lemma set_classifier_u {U X : Type u} {f : U ⟶ X} {χ₁ : X ⟶ ulift Prop} (q : classifying truth f χ₁) :
  ∀ x, (χ₁ x).down ↔ ∃ (a : U), f a = x :=
begin
  obtain ⟨ka, la, ma⟩ := q,
  intro x,
  split, rintro,
  { let g := ma.lift (pullback_cone.mk (𝟙 _) (λ _, x) (by simp [ulift.ext_iff, function.funext_iff, a, truth])),
    refine ⟨g punit.star, _⟩,
    have : (g ≫ f) _ = (λ _, x) _ := congr_fun (ma.fac _ walking_cospan.right) punit.star,
    exact this },
  rintro ⟨t, rfl⟩, have : _ = _ := congr_fun la t, simp at this, rw ← this, trivial,
end

noncomputable instance types_has_subobj_classifier : @has_subobject_classifier (Type u) category_theory.types :=
{ Ω := ulift Prop,
  Ω₀ := punit,
  truth := truth,
  is_subobj_classifier :=
  { classifier_of := λ A B f mon b, ulift.up (∃ (a : A), f a = b),
    classifies' :=
    begin
      introsI A B f mon,
      refine ⟨λ _, punit.star, _, _⟩,
      funext, ext1, dsimp [truth], rw [eq_iff_iff, true_iff], use x,
      refine is_limit.mk''' _ mon _,
      intro s,
      refine ⟨λ i, (invert_mono f (s.snd i) _).1, _⟩,
      have z : _ = _ := congr_fun s.condition i,
      rw ← ulift.up.inj z, trivial,
      ext i,
      apply (invert_mono f (s.snd i) _).2,
    end,
    uniquely' :=
    begin
      introv _ fst, ext x,
      rw set_classifier_u fst x,
    end } }

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

-- instance type_exponentiable (A : Type u) : exponentiable A :=
-- { is_adj :=
--   { right := adjunction.right_adjoint_of_equiv (currying_equiv A) (
--     begin
--       intros X X' Y f g,
--       dsimp [currying_equiv],
--       ext,
--       congr,
--       dunfold limits.prod.map,

--       -- rw types.types_limit_map,
--       -- congr, ext ⟨j⟩,
--       -- simp,
--       -- simp,
--     end),
--     adj := adjunction.adjunction_of_equiv_right _ _ } }

-- instance type_cc : cartesian_closed (Type u) :=
-- begin
--   split,
--   intro A,
--   apply_instance
-- end
