/- Author: E.W.Ayers
   Skeleton category.
   This should probably live in full_subcategory.lean
   -/
import .pullbacks
import category_theory.full_subcategory

def logic.equivalence := @equivalence

namespace category_theory

universes u v

def is_thin (C : Type u) [𝒞 : category.{v} C] := ∀ {X Y : C}, subsingleton (X ⟶ Y)

section arrows
def arrows (C : Type u) [𝒞 : category.{v} C] := comma (𝟭 C) (𝟭 C)
variables {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} {i : X ≅ Y}
include 𝒞

def are_iso (X Y : C) : Prop := nonempty (X ≅ Y)

lemma are_iso.refl : are_iso X X := ⟨iso.refl X⟩

lemma are_iso.symm : are_iso X Y → are_iso Y X
| ⟨i⟩ := ⟨i.symm⟩

lemma are_iso.trans : are_iso X Y → are_iso Y Z → are_iso X Z
| ⟨a⟩ ⟨b⟩ := ⟨iso.trans a b⟩

lemma are_iso.equiv : logic.equivalence (@are_iso C 𝒞) := 
⟨λ _, are_iso.refl, λ _ _, are_iso.symm, λ _ _ _, are_iso.trans⟩

instance : category (arrows C) := show category (comma _ _), by apply_instance

def crush.setoid : setoid (arrows C) :=
{ r := λ f g, nonempty (f ≅ g),
  iseqv := are_iso.equiv
}

variable (C)

def crush := @quotient (arrows C) crush.setoid

end arrows

variables {C : Type u} [𝒞 : category.{v} C] {X Y Z : C} {i : X ≅ Y}
include 𝒞

/-- A map `r` induces a skeleton category. -/
class skeleton_map (r : C → C) :=
(repr_iso : ∀ (X : C), r(X) ≅ X)
(eq_of_iso : ∀ {X Y : C}, (X ≅ Y) → r(X) = r(Y))

open skeleton_map

def skeleton (r : C → C) [@skeleton_map C 𝒞 r] : Type u := {X : C // ∃ (Y : C), r(Y) = X}

namespace skeleton
variables {r : C → C} [@skeleton_map C 𝒞 r]
instance skel_cat : category.{v} (skeleton r) := show category {X : C // _}, by apply_instance

def forget : (skeleton r) ⥤ C := full_subcategory_inclusion _

def to_skeleton : C ⥤ (skeleton r) :=
{ obj := λ X, ⟨r X,X,rfl⟩,
  map := λ X Y f, show r X ⟶ r Y, from (@repr_iso C 𝒞 r _ X).hom ≫ f ≫ (@repr_iso C 𝒞 r _ Y).inv,
  map_id' := begin intros, simp, refl end,
  map_comp' := begin
    intros, dsimp,
    refine calc (@repr_iso C 𝒞 r _ X).hom ≫ (f ≫ g) ≫ (@repr_iso C 𝒞 r _ Z).inv
                = (@repr_iso C 𝒞 r _ X).hom ≫ f ≫ ((@repr_iso C 𝒞 r _ Y).inv ≫ (@repr_iso C 𝒞 r _ Y).hom) ≫ g ≫ (@repr_iso C 𝒞 r _ Z).inv : _
            ... = ((@repr_iso C 𝒞 r _ X).hom ≫ f ≫ (@repr_iso C 𝒞 r _ Y).inv) ≫ ((@repr_iso C 𝒞 r _ Y).hom ≫ g ≫ (@repr_iso C 𝒞 r _ Z).inv) : _,
    rw [iso.inv_hom_id], simp,
    simp,
  end
}

@[simp] lemma to_skeleton_map_def {X Y : C} {f : X ⟶ Y} : @functor.map _ _ _ _ (@to_skeleton _ _ r _) X Y f = ((@repr_iso C 𝒞 r _ X).hom ≫ f ≫ (@repr_iso C 𝒞 r _ Y).inv : r X ⟶ r Y) := rfl
@[simp] lemma to_skeleton_obj_def {X : C}  : @functor.obj _ _ _ _ (@to_skeleton _ _ r _) X = ⟨r X, X, rfl⟩ := rfl
@[simp] lemma forget_map_def {X Y : skeleton r} {f : X ⟶ Y} : @functor.map _ _ _ _ (@forget _ _ r _) X Y f = f := rfl
@[simp] lemma forget_obj_def {X : skeleton r}: @functor.obj _ _ _ _ (@forget _ _ r _) X = X.val := rfl

def isequiv : C ≌ skeleton r :=
{ functor := to_skeleton,
  inverse := forget,
  unit_iso := begin refine nat_iso.of_components (λ X, (@repr_iso C 𝒞 r _ X).symm) _, intros, simp, end,
  counit_iso := begin
    refine nat_iso.of_components _ _,
    { rintro X,
      dsimp,
      let x := (@repr_iso _ 𝒞 r _ X.val),
      refine iso.mk x.hom x.inv _ _,
      simp, apply iso.hom_inv_id,
      apply iso.inv_hom_id,
    },
    intros, simp,
    show ((repr_iso r X.val).hom ≫ f ≫ (repr_iso r Y.val).inv) ≫ (repr_iso r Y.val).hom =
    (repr_iso r X.val).hom ≫ f,
    repeat {rw [category.assoc]},
    rw [iso.inv_hom_id], simp,
 end
}
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

noncomputable instance r_is_skeleton_map : @skeleton_map C 𝒞 re :=
{ repr_iso := λ X, re_iso X,
  eq_of_iso := λ X Y xy, begin have : q.mk X = q.mk Y, refine quotient.sound ⟨xy⟩, show quotient.out (q.mk X) = quotient.out (q.mk Y), rw this  end,
}

end canonical

/-- For all categories, a skeleton exists but you might need choice to get it. -/
lemma has_skeleton : ∃ (r : C → C), nonempty(@skeleton_map C 𝒞 r) := ⟨canonical.re, ⟨canonical.r_is_skeleton_map⟩⟩

end skeleton

end category_theory