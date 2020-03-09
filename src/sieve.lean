/- Author: E.W.Ayers -/

import category_theory.comma
import category_theory.limits.shapes.finite_limits
import category_theory.yoneda
import order.complete_lattice
import data.set.lattice
import .comma

universes u v
namespace category_theory

/-- A sieve on X is a set of morphisms to X that is closed under left composition. -/
structure sieve {C : Type u} [𝒞 : category.{v} C] (X : C) :=
(arrows : set (over X))
(subs : ∀ (f : over X) (_ : f ∈ arrows) (Z : C) (g : Z ⟶ f.left), (over.mk (g ≫ f.hom)) ∈ arrows)

namespace sieve

variables {C : Type u}
variables [𝒞 : category.{v} C]
include 𝒞
variables {X Y Z : C} {S R : sieve X}

instance mem_hom  : has_mem (Y ⟶ X) (sieve X) := ⟨λ f S, over.mk f ∈ S.arrows⟩
instance mem_over : has_mem (over X)  (sieve X) := ⟨λ f S, f ∈ S.arrows⟩

instance : has_subset (sieve X) := ⟨λ S R, S.arrows ⊆ R.arrows⟩

@[ext] def extensionality : Π {R S : sieve X}, R.arrows = S.arrows → R = S
|⟨Ra,_⟩ ⟨Sa, _⟩ rfl := rfl

open lattice

protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := ⋃ (S : {S : sieve X // S ∈ 𝒮}), sieve.arrows S.1
, subs :=
  begin
    rintros f ⟨R,⟨S,e⟩,h₁⟩ Z g,
    refine    ⟨R,⟨S,e⟩,_ ⟩,
    cases e,
    apply sieve.subs,
    assumption
  end
}

protected def Inf (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := ⋂ (S : {S // S ∈ 𝒮}), sieve.arrows S.1,
  subs :=
  begin
    rintros f h₁ Z g R h₂,
    have h₃, apply h₁, apply h₂,
    rcases h₂ with ⟨SS,rfl⟩,
    apply sieve.subs, assumption,
  end
}

protected def union (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∪ R.arrows,
  subs :=
  begin
    rintros ⟨Z,f⟩ c Y g,cases c,
      left, apply sieve.subs, assumption,
      right, apply sieve.subs, assumption
  end
}

protected def inter (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∩ R.arrows,
  subs := begin
    rintros f ⟨fS,fR⟩ Z g,
    split,
      apply sieve.subs, assumption,
      apply sieve.subs, assumption,
  end
}

instance : complete_lattice (sieve X) :=
{ le           := λ S R, S ⊆ R,
  le_refl      := λ S, set.subset.refl _,
  le_trans     := λ S R T, set.subset.trans,
  le_antisymm  := begin intros S R p q, apply sieve.extensionality, apply set.subset.antisymm; assumption end,
  top          := { arrows := set.univ, subs := λ a aa Z g, ⟨⟩ },
  bot          := { arrows := ∅, subs := λ a aa Z g, false.rec_on _ aa },
  sup          := sieve.union,
  inf          := sieve.inter,
  Sup          := sieve.Sup,
  Inf          := sieve.Inf,
  le_Sup       := begin intros 𝒮 S SS f fS, refine ⟨_,⟨⟨_,SS⟩,rfl⟩,fS⟩ end,
  Sup_le       := begin rintros 𝒮 S h f ⟨F,⟨⟨R,hR⟩,rfl⟩,fF⟩, apply h _ hR fF end,
  Inf_le       := begin intros 𝒮 S hS f hf, apply hf, refine ⟨⟨_,hS⟩,rfl⟩ end,
  le_Inf       := begin rintros 𝒮 S h f hf fs ⟨⟨R,hR⟩,rfl⟩, apply h _ hR hf  end,
  le_sup_left  := begin intros _ _ _ _, apply set.subset_union_left, assumption end,
  le_sup_right := begin intros _ _ _ _, apply set.subset_union_right, assumption end,
  sup_le       := begin intros _ _ _ _ _, apply set.union_subset; assumption  end,
  inf_le_left  := begin intros _ _ _ _, apply set.inter_subset_left, assumption end,
  inf_le_right := begin intros _ _ _ _, apply set.inter_subset_right, assumption end,
  le_inf       := begin intros _ _ _ _ _, apply set.subset_inter; assumption  end,
  le_top       := begin intros _ _ _, trivial end,
  bot_le       := begin intros _ _ h, exfalso, apply h end
}
instance : preorder      (sieve X) := by apply_instance
instance : partial_order (sieve X) := by apply_instance

inductive generate_sets (𝒢 : set (over X)) : over X → Prop
|basic : Π {f : over X}, f ∈ 𝒢 → generate_sets f
|subs  : Π {f : over X} {Y} (g : Y ⟶ f.1), generate_sets f → generate_sets (over.mk $ g ≫ f.hom)

def generate (𝒢 : set (over X)) : sieve X :=
{ arrows := generate_sets 𝒢,
  subs   := λ f h Z g, generate_sets.subs _ h
}

open order lattice

lemma sets_iff_generate {𝒢 : set (over X)}: generate 𝒢 ≤ S ↔ 𝒢 ⊆ S.arrows :=
iff.intro
    (λ H _ H2, H $ generate_sets.basic H2 )
    (λ ss g f, begin induction f, apply ss f_a, apply sieve.subs, apply f_ih end)

/-- Show that there is a galois insertion (generate, .arrows).
    -/
def gi_generate :
  @galois_insertion (set (over X)) (sieve X) (by apply_instance) _ generate sieve.arrows :=
  { gc        := λ s f, sets_iff_generate,
    choice    := λ 𝒢 f, generate 𝒢,
    choice_eq := λ 𝒢 h, rfl,
    le_l_u    := λ S _, generate_sets.basic
  }

/-- Given a morhpism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
def pullback (S : sieve X) (h : Y ⟶ X) :  sieve Y :=
{ arrows := {sl | (over.mk $ sl.hom ≫ h) ∈ S },
  subs :=
  begin
    intros, suffices : over.mk ((g ≫ f.hom) ≫ h) ∈ S, by assumption,
    let j := over.mk (f.hom ≫ h),
    have jS : j ∈ S, by assumption,
    suffices : over.mk (g ≫ j.hom) ∈ S, by simpa,
    apply sieve.subs S j jS,
  end
}

def comp (R : sieve Y) (f : Y ⟶ X) : sieve X :=
{ arrows := λ gf, ∃ (g : gf.1 ⟶ Y) (_ : over.mk g ∈ R), gf.hom = g ≫ f
, subs :=
  begin
    rintros ⟨Z,g⟩ ⟨j,ir,e⟩ W h, refine ⟨h ≫ j,_,_⟩,
    refine sieve.subs R _ ir _ _,
    simp, simp at e, rw e
  end
}

def comps
  (R : Π (f : over X), sieve f.left)
  (S : sieve X) : sieve X :=
  ⨆ (f ∈ S), comp (R f) f.hom

@[simp] lemma pullback_def (h : Y ⟶ X) {f : Z ⟶ Y}
: ((over.mk f) ∈ (pullback S h)) = ((over.mk $ f ≫ h) ∈ S) := rfl

@[simp] lemma pullback_def2 (h : Y ⟶ X)  {f : over Y}
: (f ∈ (pullback S h)) = ((over.mk $ f.hom ≫ h) ∈ S) := rfl

lemma pullback_le_map {S R : sieve X} (Hss : S ≤ R) (f : Y ⟶ X) : pullback S f ≤ pullback R f :=
begin rintros ⟨Z,g⟩ H, apply Hss, apply H end

lemma pullback_top {f : Y ⟶ X} : pullback ⊤ f = ⊤ :=
begin apply top_unique, rintros g Hg, trivial end

lemma le_pullback_comp {R : sieve Y} {f : Y ⟶ X} :
  R ≤ pullback (comp R f) f :=
begin rintros g b, refine ⟨_,_,rfl⟩, simp, assumption end

lemma top_of_has_id : over.mk (𝟙 X) ∈ S → S = ⊤ :=
begin
  intro h,
  apply top_unique,
  rintros f ⟨⟩,
  suffices : over.mk (f.hom ≫ (𝟙 _)) ∈ S,
    simp at this, exact this,
  refine @sieve.subs _ _ _ S (over.mk (𝟙 _)) _ _ _,
  apply h,
end

lemma comp_le_comps
  (R : Π (f : over X), sieve f.1)
  (S : sieve X)
  (f : over X)
  (H : f ∈ S) :
  comp (R f) f.hom ≤ comps R S  :=
calc comp (R f) f.hom ≤  ⨆ (_ : f ∈ S), comp (R f) f.hom : lattice.le_supr _ H
                  ... ≤  comps R S                        : lattice.le_supr _ f

lemma comps_le
  (R : Π (f : over X), sieve f.left)
  (S : sieve X) :
  comps R S ≤ S :=
begin
  apply lattice.supr_le _,
  rintros f,
  apply lattice.supr_le _,
  rintros H g ⟨a,b,e⟩,
  suffices : over.mk (g.hom) ∈ S, simp at this, apply this,
  rw e,
  apply sieve.subs,
  apply H,
end

def as_functor (S : sieve X) : Cᵒᵖ ⥤ Type v :=
{ obj := λ Y, {g : Y.unop ⟶ X // over.mk g ∈ S},
  map := λ Y Z f g, subtype.mk (f.unop ≫ g.1) (begin
    cases g with g gS, 
    apply sieve.subs S (over.mk g) gS _ f.unop,
  end)
}

def functor_inclusion (S : sieve X) : S.as_functor ⟶ yoneda.obj X :=
nat_trans.mk (λ Y f, f.1) (λ Y Z g, rfl)

-- [todo] show functor_inclusion is monic.

end sieve
end category_theory