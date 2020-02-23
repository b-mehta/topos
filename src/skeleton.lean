/- Author: E.W.Ayers
   Skeleton category.
   This should probably live in full_subcategory.lean
   -/
import .pullbacks
import category_theory.full_subcategory

namespace category_theory

universes u v
variables {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} {i : X ≅ Y}
include 𝒞

def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)

lemma are_iso.refl : are_iso X X := ⟨iso.refl X⟩

lemma are_iso.symm : are_iso X Y → are_iso Y X
| ⟨i⟩ := ⟨i.symm⟩

lemma are_iso.trans : are_iso X Y → are_iso Y Z → are_iso X Z
| ⟨a⟩ ⟨b⟩ := ⟨iso.trans a b⟩

variable (C)

def skeleton.setoid : setoid C :=
{ r := are_iso,
  iseqv :=⟨λ _, are_iso.refl, λ _ _, are_iso.symm, λ _ _ _, are_iso.trans⟩
}

local attribute [instance] skeleton.setoid

/-- Quotient the given category on isomorphisms.
    Instead of defining this to be the category, we use this to construct a
    canonical set of representatives using choice and then define the skeleton
    as the full subcategory on these representatives. -/
def skeleton.q := quotient (skeleton.setoid C)

variable {C}

def skeleton.q.mk (X : C) : skeleton.q C := ⟦X⟧

noncomputable def skeleton.repr : C → C := quotient.out ∘ skeleton.q.mk

noncomputable def skeleton.repr_iso (X : C) : X ≅ skeleton.repr X := iso.symm $ classical.choice $ @quotient.mk_out C (skeleton.setoid C) $ X

-- [TODO] should we use the definition of essentially surjective given in mathlib?
/-- A skeleton is an essentially surjective subset of objects in C such that none of them are iso to each other.  -/
structure is_skeleton (D : set C) : Prop :=
(eq_of_iso : ∀ {X Y} (hx : X ∈ D) (hy : Y ∈ D), (X ≅ Y) → X = Y )
(ess_surj : ∀ (X : C), ∃ {Y:C}, Y ∈ D ∧ nonempty (X ≅ Y))

instance {D : set C} : category { X : C // X ∈ D } := by apply_instance

variable (C)

def skeleton.canonical : set C := set.image (skeleton.repr) (set.univ)

def skeleton : Type u := {X : C // X ∈ skeleton.canonical C}

variable {C}

lemma skeleton.canonical.is_skel : @is_skeleton C 𝒞 (skeleton.canonical C) :=
begin
  refine ⟨_,_⟩,
  { rintros X Y ⟨XX,⟨⟩,rfl⟩ ⟨YY,⟨⟩,rfl⟩ i,
    suffices : skeleton.q.mk XX = skeleton.q.mk YY, rw [skeleton.repr], simp, rw this,
    apply quotient.sound',
    have h1, refine (skeleton.repr_iso XX),
    have h2, refine (skeleton.repr_iso YY),
    refine ⟨calc XX ≅ _ : h1 ... ≅ _ : i ... ≅ YY : h2.symm⟩ },
  { rintros X,
    refine ⟨skeleton.repr X,⟨X,⟨⟩,rfl⟩,⟨skeleton.repr_iso X⟩⟩}
end

lemma skeleton.canonical_has_repr (X : C) : skeleton.repr X ∈ skeleton.canonical C :=
⟨X,⟨⟩,rfl⟩

instance skeleton.is_category : category.{v} (skeleton C) := show category.{v} {X : C // _}, by apply_instance

lemma skeleton.ess_surj : ∀ (X : C), ∃ (Y : skeleton C), are_iso X Y.1 :=
begin rintros X, refine ⟨⟨skeleton.repr X, skeleton.canonical_has_repr X⟩,⟨skeleton.repr_iso X⟩⟩  end

lemma skeleton.eq_of_iso : ∀ (X Y : skeleton C), (X ≅ Y) → X = Y :=
begin
  rintros ⟨_,⟨X,⟨⟩,rfl⟩⟩ ⟨_,⟨Y,⟨⟩,rfl⟩⟩ i,
  apply subtype.ext.2,
  apply (skeleton.canonical.is_skel).eq_of_iso,
  apply skeleton.canonical_has_repr,
  apply skeleton.canonical_has_repr,
  cases i,
  refine ⟨i_hom,i_inv,_,_⟩, assumption, assumption
end

end category_theory