/- Author: E.W.Ayers
   Skeleton category.
   This should probably live in full_subcategory.lean
   -/
import category_theory.full_subcategory
import category_theory.comma

def logic.equivalence := @equivalence

namespace category_theory

universes v u

def is_thin (C : Type u) [category.{v} C] := ∀ {X Y : C}, subsingleton (X ⟶ Y)

section arrows
def arrows (C : Type u) [category.{v} C] := comma (𝟭 C) (𝟭 C)
variables {C : Type u} [category.{v} C] {X Y Z : C} {i : X ≅ Y}

def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)

lemma are_iso.refl : are_iso X X := ⟨iso.refl X⟩

lemma are_iso.symm : are_iso X Y → are_iso Y X
| ⟨i⟩ := ⟨i.symm⟩

lemma are_iso.trans : are_iso X Y → are_iso Y Z → are_iso X Z
| ⟨a⟩ ⟨b⟩ := ⟨iso.trans a b⟩

lemma are_iso.equiv : logic.equivalence (are_iso : C → C → Prop) :=
⟨λ _, are_iso.refl, λ _ _, are_iso.symm, λ _ _ _, are_iso.trans⟩

instance : category (arrows C) := show category (comma _ _), by apply_instance

def crush.setoid : setoid (arrows C) :=
{ r := λ f g, nonempty (f ≅ g),
  iseqv := are_iso.equiv
}

variable (C)

def crush := @quotient (arrows C) crush.setoid

end arrows

variables {C : Type u} [category.{v} C] {X Y Z : C} {i : X ≅ Y}

/-- A map `r` induces a skeleton category. -/
structure skeleton_map (r : C → C) :=
(repr_iso : ∀ (X : C), r X ≅ X)
(eq_of_iso : ∀ {X Y : C}, (X ≅ Y) → r X = r Y)

open skeleton_map

def skeleton {r : C → C} (sr : skeleton_map.{v} r) : Type u := {X : C // ∃ (Y : C), r(Y) = X}

namespace skeleton
variables {r : C → C} (sr : skeleton_map.{v} r)
instance skel_cat : category.{v} (skeleton sr) := category_theory.full_subcategory _

def forget : skeleton sr ⥤ C := full_subcategory_inclusion _
instance : full (forget sr) := full_subcategory.full _
instance : faithful (forget sr) := full_subcategory.faithful _

@[simps]
def to_skeleton : C ⥤ skeleton sr :=
{ obj := λ X, ⟨r X, X, rfl⟩,
  map := λ X Y f, (forget sr).preimage ((sr.repr_iso X).hom ≫ f ≫ (sr.repr_iso Y).inv),
  map_comp' := λ X Y Z f g, by simp [← preimage_comp] }

-- @[simp] lemma to_skeleton_map_def {X Y : C} {f : X ⟶ Y} : @functor.map _ _ _ _ (@to_skeleton _ _ r _) X Y f = ((@repr_iso C 𝒞 r _ X).hom ≫ f ≫ (@repr_iso C 𝒞 r _ Y).inv : r X ⟶ r Y) := rfl
-- @[simp] lemma to_skeleton_obj_def {X : C}  : @functor.obj _ _ _ _ (@to_skeleton _ _ r _) X = ⟨r X, X, rfl⟩ := rfl
-- @[simp] lemma forget_map_def {X Y : skeleton r} {f : X ⟶ Y} : @functor.map _ _ _ _ (@forget _ _ r _) X Y f = f := rfl
@[simp] lemma forget_obj_def {X : skeleton sr} : (forget sr).obj X = X.val := rfl

def isequiv : C ≌ skeleton sr :=
{ functor := to_skeleton sr,
  inverse := forget sr,
  unit_iso := nat_iso.of_components (λ X, (sr.repr_iso X).symm) (by tidy),
  counit_iso :=
  begin
    refine nat_iso.of_components _ _,
    intro X,
    { refine @preimage_iso _ _ _ _ (forget sr) _ _ _ _ _,
      refine sr.repr_iso X.val },
    { intros,
      apply (forget sr).map_injective,
      dsimp, simp },
  end,
  functor_unit_iso_comp' := λ X,
  begin
    apply (forget sr).map_injective,
    dsimp,
    simp,
  end }

/- Define a noncomputable skeleton using quotients. -/
namespace canonical

variable (C)

def q.setoid : setoid C :=
{ r := are_iso,
  iseqv := are_iso.equiv
}

local attribute [instance] q.setoid

/-- Quotient the given category on isomorphisms.
    Instead of defining this to be the category, we use this to construct a
    canonical set of representatives using choice and then define the skeleton
    as the full subcategory on these representatives. -/
def q := quotient (q.setoid C)

variable {C}

def q.mk (X : C) : q C := ⟦X⟧

noncomputable def re : C → C := quotient.out ∘ q.mk
noncomputable def re_iso (X : C) : re X ≅ X := @classical.choice _ $ @quotient.mk_out C (q.setoid C) $ X

noncomputable def r_is_skeleton_map : skeleton_map.{v} (canonical.re : C → C) :=
{ repr_iso := λ X, re_iso X,
  eq_of_iso := λ X Y xy,
  begin
    show quotient.out (q.mk X) = quotient.out (q.mk Y),
    congr' 1,
    apply quotient.sound,
    refine ⟨xy⟩,
  end,
}

end canonical

/-- For all categories, a skeleton exists but you might need choice to get it. -/
lemma has_skeleton : ∃ (r : C → C), nonempty (skeleton_map.{v} r) := ⟨canonical.re, ⟨canonical.r_is_skeleton_map⟩⟩

end skeleton

end category_theory
