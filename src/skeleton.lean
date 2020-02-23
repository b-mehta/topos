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

namespace skeleton

lemma canonical.is_skel : @is_skeleton C 𝒞 (canonical C) :=
begin
  refine ⟨_,_⟩,
  { rintros X Y ⟨XX,⟨⟩,rfl⟩ ⟨YY,⟨⟩,rfl⟩ i,
    suffices : q.mk XX = q.mk YY, rw [repr], simp, rw this,
    apply quotient.sound',
    have h1, refine (repr_iso XX),
    have h2, refine (repr_iso YY),
    refine ⟨calc XX ≅ _ : h1 ... ≅ _ : i ... ≅ YY : h2.symm⟩ },
  { rintros X,
    refine ⟨repr X,⟨X,⟨⟩,rfl⟩,⟨repr_iso X⟩⟩}
end

lemma canonical_has_repr (X : C) : repr X ∈ canonical C :=
⟨X,⟨⟩,rfl⟩

instance is_category : category.{v} (skeleton C) := show category.{v} {X : C // _}, by apply_instance

lemma ess_surj : ∀ (X : C), ∃ (Y : skeleton C), are_iso X Y.1 :=
begin rintros X, refine ⟨⟨repr X, canonical_has_repr X⟩,⟨repr_iso X⟩⟩  end

lemma eq_of_iso : ∀ (X Y : skeleton C), (X ≅ Y) → X = Y :=
begin
  rintros ⟨_,⟨X,⟨⟩,rfl⟩⟩ ⟨_,⟨Y,⟨⟩,rfl⟩⟩ i,
  apply subtype.ext.2,
  apply (canonical.is_skel).eq_of_iso,
  apply canonical_has_repr,
  apply canonical_has_repr,
  cases i,
  refine ⟨i_hom,i_inv,_,_⟩, assumption, assumption
end

noncomputable def mk (X : C) : skeleton C := ⟨repr X, canonical_has_repr _⟩

noncomputable def mk_hom {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y :=
  show repr X ⟶ repr Y,
  from (repr_iso X).inv ≫ f ≫ (repr_iso Y).hom

@[simp] lemma mk_hom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : mk_hom (f ≫ g) = mk_hom f ≫ mk_hom g :=
begin
  let x := repr_iso X,
  let y := repr_iso Y,
  let z := repr_iso Z,
  refine calc mk_hom (f ≫ g) = (x.inv ≫ f ≫ g ≫ z.hom : repr X ⟶ repr Z) : _
     ... = (x.inv ≫ f ≫ (y.hom ≫ y.inv) ≫ g ≫ z.hom : repr X ⟶ repr Z) : _
     ... = ((x.inv ≫ f ≫ y.hom) ≫ (y.inv ≫ g ≫ z.hom) : repr X ⟶ repr Z) : _
    ...= mk_hom f ≫ mk_hom g : _,
    rw [mk_hom], simp,
    simp, simp, rw [mk_hom], rw [mk_hom], refl,
end

@[simp] lemma mk_hom_id {X  : C} : mk_hom (𝟙 X) = 𝟙 (mk X) :=
begin rw [mk_hom], simp, refl, end

noncomputable def to_repr : C ⥤ (skeleton C) :=
{ obj := mk, map := λ X Y f, mk_hom f}

def forget : (skeleton C) ⥤ C := full_subcategory_inclusion _

@[simp] lemma to_repr_map_def {X Y : C} {f : X ⟶ Y} : to_repr.map f = mk_hom f := rfl
@[simp] lemma to_repr_obj_def {X : C} : to_repr.obj X = mk X := rfl
@[simp] lemma forget_obj_def {X : skeleton C} : forget.obj X = X.1 := rfl
@[simp] lemma forget_map_def {X Y : skeleton C} {f :  X ⟶ Y} : forget.map f = f := rfl
@[simp] lemma mk_hom_def {X Y : C} {f : X ⟶ Y} : mk_hom f = ((repr_iso X).inv ≫ f ≫ (repr_iso Y).hom : repr X ⟶ repr Y) := rfl

noncomputable def isequiv : C ≌ skeleton C :=
{ functor := to_repr,
  inverse := forget,
  unit_iso := begin refine nat_iso.of_components repr_iso _, intros, simp end,
  counit_iso := begin
    refine nat_iso.of_components _ _,
    { rintro X,
      dsimp,
      let x := (repr_iso X.val),
      refine iso.mk x.inv x.hom _ _,
      simp, apply iso.hom_inv_id, apply iso.inv_hom_id,
    },
    intros, simp,
    show ((repr_iso X.val).inv ≫ f ≫ (repr_iso Y.val).hom) ≫ (repr_iso Y.val).inv = (repr_iso X.val).inv ≫ f,
    repeat {rw [category.assoc]},
    rw [iso.hom_inv_id (repr_iso Y.val)], simp,
 end
}

end skeleton
end category_theory