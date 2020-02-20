/- Author: E.W.Ayers -/

import category_theory.comma
import category_theory.limits.shapes.finite_limits
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

instance : partial_order (sieve X) :=
{ partial_order .
  le := λ S R, S ⊆ R,
  le_refl := λ S, set.subset.refl _,
  le_trans := λ S R T, set.subset.trans,
  le_antisymm := begin intros S R p q, apply sieve.extensionality, apply set.subset.antisymm; assumption end
}

lemma subset_def : S.arrows ⊆ R.arrows → S ≤ R := λ h, h

instance : preorder (sieve X) := by apply_instance

open lattice

protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := ⋃ (S : {S : sieve X // S ∈ 𝒮}), sieve.arrows S.1
, subs :=
  begin
    rintros f ⟨R,⟨⟨S,S𝒮⟩,e⟩,h₁⟩ Z g,
    refine ⟨R,⟨⟨S,S𝒮⟩,e⟩,_⟩,
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

def union (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∪ R.arrows,
  subs :=
  begin
    rintros ⟨Z,f⟩ c Y g,cases c,
      left, apply sieve.subs, assumption,
      right, apply sieve.subs, assumption
  end
}

def inter (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∩ R.arrows,
  subs := begin
    rintros f ⟨fS,fR⟩ Z g,
    split,
      apply sieve.subs, assumption,
      apply sieve.subs, assumption,
  end
}

instance : complete_lattice (sieve X) :=
{ top := { arrows := set.univ, subs := λ a aa Z g, ⟨⟩ },
  bot := { arrows := ∅, subs := λ a aa Z g, false.rec_on _ aa },
  sup := union,
  inf := inter,
  Sup := sieve.Sup,
  Inf := sieve.Inf,
  le_Sup := begin intros 𝒮 S SS f fS, refine ⟨_,⟨⟨_,SS⟩,rfl⟩,fS⟩ end,
  Sup_le := begin rintros 𝒮 S h f ⟨F,⟨⟨R,hR⟩,rfl⟩,fF⟩, apply h _ hR fF end,
  Inf_le := begin intros 𝒮 S hS f hf, apply hf, refine ⟨⟨_,hS⟩,rfl⟩ end,
  le_Inf := begin rintros 𝒮 S h f hf fs ⟨⟨R,hR⟩,rfl⟩, apply h _ hR hf  end,
  le_sup_left := begin intros _ _ _ _, apply set.subset_union_left, assumption end,
  le_sup_right := begin intros _ _ _ _, apply set.subset_union_right, assumption end,
  sup_le := begin intros _ _ _ _ _, apply set.union_subset, assumption, assumption  end,
  inf_le_left := begin intros _ _ _ _, apply set.inter_subset_left, assumption end,
  inf_le_right := begin intros _ _ _ _, apply set.inter_subset_right, assumption end,
  le_inf := begin intros _ _ _ _ _, apply set.subset_inter, assumption, assumption  end,
  le_top := begin intros _ _ _, trivial end,
  bot_le := begin intros _ _ h, exfalso, apply h end,
  ..sieve.partial_order
}

inductive generate_sets (𝒢 : set (over X)) : over X → Prop
|basic : Π {f : over X}, f ∈ 𝒢 → generate_sets f
|subs  : Π {f : over X} {Y} (g : Y ⟶ f.1), generate_sets f → generate_sets (over.mk $ g ≫ f.hom)

def generate (𝒢 : set (over X)) : sieve X :=
{ arrows := generate_sets 𝒢,
  subs := λ f h Z g, generate_sets.subs _ h
}

open order lattice

lemma sets_iff_generate {𝒢 : set (over X)}: generate 𝒢 ≤ S ↔ 𝒢 ⊆ S.arrows
:= iff.intro
    (λ H _ H2, H $ generate_sets.basic H2 )
    (λ ss g f, begin induction f, apply ss f_a, apply sieve.subs, apply f_ih end)

/-- Show that there is a galois insertion (generate, .arrows).
    -/
def gi_generate :
  @galois_insertion (set (over X)) (sieve X) (by apply_instance) _ generate sieve.arrows :=
  { gc := λ s f, sets_iff_generate,
    choice := λ 𝒢 f, generate 𝒢,
    choice_eq := λ 𝒢 h, rfl,
    le_l_u := λ S _, generate_sets.basic
  }

-- [TODO] what is the established name for this? Notation is h* S
/-- Given a morhpism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `yank S h := (≫ h) '⁻¹ S`. -/
def yank (S : sieve X) (h : Y ⟶ X) :  sieve Y :=
{ arrows := {sl | (over.mk $ sl.hom ≫ h) ∈ S },
  subs :=
  begin
    intros, suffices : over.mk ((g ≫ f.hom) ≫ h) ∈ S, by apply this,
    let j := over.mk (f.hom ≫ h),
    have jS : j ∈ S, from _x,
    suffices : over.mk (g ≫ j.hom) ∈ S, simp, apply this,
    apply sieve.subs S j jS,
  end
}

@[simp] lemma yank_def (h : Y ⟶ X) {f : Z ⟶ Y}
: ((over.mk f) ∈ (yank S h)) = ((over.mk $ f ≫ h) ∈ S) := rfl

@[simp] lemma yank_def2 (h : Y ⟶ X)  {f : over Y}
: (f ∈ (yank S h)) = ((over.mk $ f.hom ≫ h) ∈ S) := rfl


def yank_le_map {S R : sieve X} (Hss : S ≤ R) (f : Y ⟶ X) : yank S f ≤ yank R f
:= begin rintros ⟨Z,g⟩ H, apply Hss, apply H end

lemma yank_top {f : Y ⟶ X} : yank ⊤ f = ⊤ :=
begin apply top_unique, rintros g Hg, trivial end

def comp (R : sieve Y) (f : Y ⟶ X) : sieve X :=
{ arrows := λ gf, ∃ (g : gf.1 ⟶ Y) (_ : over.mk g ∈ R), gf.hom = g ≫ f
, subs :=
  begin
    rintros ⟨Z,g⟩ ⟨j,ir,e⟩ W h, refine ⟨h ≫ j,_,_⟩,
    refine sieve.subs R _ ir _ _,
    simp, simp at e, rw e
  end
}

def le_yank_comp {R : sieve Y} {f : Y ⟶ X} :
  R ≤ yank (comp R f) f :=
begin rintros g b, refine ⟨_,_,rfl⟩, simp, assumption end

def has_id_max : over.mk (𝟙 X) ∈ S → S = ⊤ :=
begin
  intro h,
  apply top_unique,
  rintros f ⟨⟩,
  suffices : over.mk (f.hom ≫ (𝟙 _)) ∈ S,
    simp at this, exact this,
  refine @sieve.subs _ _ _ S (over.mk (𝟙 _)) _ _ _,
  apply h,
end

def comps
  (R : Π (f : over X), sieve f.left)
  (S : sieve X) : sieve X :=
  ⨆ (f ∈ S), comp (R f) f.hom

def comp_le_comps
  (R : Π (f : over X), sieve f.1)
  (S : sieve X)
  (f ∈ S) :
  comp (R f) f.hom ≤ comps R S
  :=
  begin
    refine calc comp (R f) f.hom = _ : _ ... ≤  ⨆ (H : f ∈ S), comp (R f) f.hom : _
      ... ≤  ⨆ (f ∈ S), comp (R f) f.hom : _,
      rotate 2,
      refine lattice.le_supr _ H,
      refine lattice.le_supr _ f,
      reflexivity
   end

def comps_ss_S
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

end sieve
end category_theory