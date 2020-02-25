/- Author: E.W.Ayers
   This should be in mathlib. Some simp and extensionality lemmas for comma and over. -/
import category_theory.comma

namespace category_theory

section

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation
variables {A : Type u₁} [𝒜 : category.{v₁} A]
variables {B : Type u₂} [ℬ : category.{v₂} B]
variables {T : Type u₃} [𝒯 : category.{v₃} T]
include 𝒜 ℬ 𝒯

variables {L : A ⥤ T} {R : B ⥤ T}

lemma comma.ext : Π {l₁ l₂ : comma L R} (pl : l₁.left = l₂.left) (pr : l₁.right = l₂.right) (pf : l₁.hom == l₂.hom), l₁ = l₂ :=
begin
  rintros ⟨_,_,_⟩ ⟨_,_,_⟩ pl pr pf, cases pl, cases pr, cases pf, refl,
end

end

section

open over

universes u v
variables  {C : Type u} [𝒞 : category.{v} C] {X : C}
include 𝒞

@[ext] lemma over.ext : Π {o₁ o₂ : over X} (px : o₁.left = o₂.left) (p : o₁.hom == o₂.hom), o₁ = o₂ :=
begin
  intros _ _ _ _,
  apply comma.ext,
  assumption,
  rw over.over_right, rw over.over_right,
  assumption
end

@[simp] lemma over.mk_hom_id {f : over X} : over.mk(f.hom) = f :=
begin ext, refl, refl, end

end
end category_theory