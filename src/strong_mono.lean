import category_theory.comma
import category_theory.limits.shapes.regular_mono
import category_theory.limits.shapes.equalizers
import data.erased

universes v u

-- Note this is obviously implied by full choice.
axiom unique_choice {α : Sort u} [subsingleton α] : nonempty α → α

def thing {α : Sort 0} [subsingleton α] : nonempty α → α :=
begin
  intro i,
  cases i,
  exact i
end

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

namespace category_theory

open limits

variables {C : Type u} [category.{v} C]

variables {P Q : C}

/-- A strong epimorphism `f` is an epimorphism such that every commutative square with `f` at the
    top and a monomorphism at the bottom has a lift. -/
class strong_mono (f : P ⟶ Q) :=
[mono : mono f]
(has_lift : Π {X Y : C} {u : X ⟶ P} {v : Y ⟶ Q} {z : X ⟶ Y} [epi z] (h : z ≫ v = u ≫ f),
  arrow.has_lift $ arrow.hom_mk' h)

attribute [instance] strong_mono.has_lift

noncomputable def invert_mono {U X : Type u} (m : U ⟶ X) [mon : mono m] (t : X) (h : ∃ i, m i = t) : {i : U // m i = t} :=
begin
  apply get_unique _ h _,
  intros,
  rw mono_iff_injective at mon,
  apply mon,
  rw [a_1, a_2]
end


-- #print mono_of_strong_mono
--
-- @[priority 100]
-- instance mono_of_strong_mono (f : P ⟶ Q) [strong_mono f] : mono f := strong_mono.mono

noncomputable instance every_mono_is_regular {X Y : Type u} (f : X ⟶ Y) [mono f] : regular_mono f :=
{ Z := ulift Prop,
  left := λ _, ⟨true⟩,
  right := λ y, ⟨y ∈ set.range f⟩,
  w := begin ext x, dsimp, simp [set.mem_range_self] end,
  is_limit :=
  begin
    apply fork.is_limit.mk _ _ _ _,
    { intros s i,
      apply (invert_mono f (fork.ι s i) _).1,
      rw ← set.mem_range,
      have : ulift.up true = ulift.up (fork.ι s i ∈ set.range f) := congr_fun (fork.condition s) i,
      simpa only [ulift.ext_iff, true_iff, eq_iff_iff] using this },
    { intro s,
      ext i,
      apply (invert_mono f (fork.ι s i) _).2 },
    { intros s m w,
      erw [← cancel_mono f, w walking_parallel_pair.zero],
      symmetry,
      ext i,
      apply (invert_mono f (fork.ι s i) _).2 },
  end }

def unique_choice_of_every_mono_is_regular (h : Π {X Y : Type u} (f : X ⟶ Y) (m : mono.{u} f), regular_mono f) {α : Type u} [subsingleton α] [ne : nonempty α] : α :=
begin
  let f : α ⟶ _ := (λ (_ : α), punit.star),
  haveI : epi f := (epi_iff_surjective f).2 (λ i, ne.elim (λ a, ⟨a, subsingleton.elim _ _⟩)),
  obtain ⟨_, _, _, _, _⟩ := h (λ (_ : α), punit.star) _,
  rw cancel_epi f at w,
  apply is_limit.lift (fork.of_ι (𝟙 _) (by simp [w])) ⟨⟩,
  rw mono_iff_injective,
  intros x y h,
  apply subsingleton.elim,
end

def erased_unique_choice {α} [subsingleton α] (h : nonempty α) : erased α :=
⟨λ _, true, let ⟨a⟩ := h in ⟨a, funext $ λ b, eq_true_intro (subsingleton.elim _ _)⟩⟩

noncomputable def unique_choice' {α : Type u} : nonempty α → trunc α :=
begin
  haveI : subsingleton (trunc α) := by apply_instance,
  intro i,
  apply unique_choice,
  rcases i,
  refine ⟨trunc.mk i⟩,
end

noncomputable def get_erased {α : Type u} : erased α → α :=
begin
  rintro ⟨p, _⟩,
  apply (get_unique p _ _).1,
  cases a_snd with t ht,
  refine ⟨t, _⟩,
  rw ← ht,
  cases a_snd with t ht,
  intros,
  rw ← ht at a_1 a_2,
  rw ← a_1, rw ← a_2,
end
-- subsingleton A -> nonempty A -> A
-- unique A -> A
-- nonempty A -> trunc A
-- erased A -> A

-- section
-- variables {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

-- /-- The composition of two strong epimorphisms is a strong epimorphism. -/
-- def strong_epi_comp [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) :=
-- { epi := epi_comp _ _,
--   has_lift :=
--   begin
--     introsI,
--     have h₀ : u ≫ z = f ≫ g ≫ v, by simpa [category.assoc] using h,
--     let w : Q ⟶ X := arrow.lift (arrow.hom_mk' h₀),
--     have h₁ : w ≫ z = g ≫ v, by rw arrow.lift_mk'_right,
--     exact ⟨(arrow.lift (arrow.hom_mk' h₁) : R ⟶ X), by simp, by simp⟩
--   end }

-- /-- If `f ≫ g` is a strong epimorphism, then so is g. -/
-- def strong_epi_of_strong_epi [strong_epi (f ≫ g)] : strong_epi g :=
-- { epi := epi_of_epi f g,
--   has_lift :=
--   begin
--     introsI,
--     have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v, by simp only [category.assoc, h],
--     exact ⟨(arrow.lift (arrow.hom_mk' h₀) : R ⟶ X), (cancel_mono z).1 (by simp [h]), by simp⟩,
--   end }

-- end

-- /-- A strong epimorphism that is a monomorphism is an isomorphism. -/
-- def mono_strong_epi_is_iso (f : P ⟶ Q) [strong_epi f] [mono f] : is_iso f :=
-- { inv := arrow.lift $ arrow.hom_mk' $ show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp }

end category_theory
