/- Author: E.W.Ayers.
   This section roughly follows Chapter 3, §1, §2 of Sheaves in Geology and Logic by Saunders Maclane and Ieke M.
 -/

import category_theory.whiskering
import .sieve

universes u v w
namespace category_theory
variables {C : Type u}
variables [𝒞 : category.{v} C]
variables {X : C}
include 𝒞

open order lattice

def sieve_set (C : Type u) [𝒞 : category.{v} C] :=  Π (X : C), set (@sieve C 𝒞 X)

open sieve category

/-- Definition of a Grothendiek Topology. -/
class grothendieck (J : sieve_set C) :=
(max : ∀ X, ⊤ ∈ J(X))
(stab : ∀ (X Y : C) (S ∈ J(X)) (h : Y ⟶ X), yank S h ∈ J(Y))
(trans :
  ∀ ⦃X : C⦄
    (S ∈ J(X))
    (R : sieve X)
    (_ : ∀ (f : over X)
           (_ : f ∈ @sieve.arrows C 𝒞 X S),
         yank R f.hom ∈ J(f.left)),
    R ∈ J(X)
)
variables {J : sieve_set C} [grothendieck J]

namespace grothendieck

def superset_covers {C : Type u} [𝒞 : category.{v} C]
    {J : sieve_set C} [grothendieck J]
    {X} {S R : @sieve C 𝒞 X} (Hss : S ⊆ R) (sjx : S ∈ J(X)) : (R ∈ J(X)) :=
begin
  apply grothendieck.trans,
  apply sjx,
  rintros h H2,
  have : over.mk (𝟙 h.left) ∈ (yank R h.hom).arrows,
    apply Hss,
    simp, rw [@category.id_comp _ _ h.left _ h.hom], simp,
    apply H2,
  have : yank R h.hom = ⊤,  apply has_id_max this,
  rw this,
  apply grothendieck.max
end

def trans2
  (X : C)
  (S : @sieve C 𝒞 X)
  (sjx : S ∈ J(X))
  (R : Π (f : over X), @sieve C 𝒞 f.left)
  (hR : Π f (H:f ∈ S.arrows), (R f) ∈ J(f.left))
  : comps R S ∈ J(X) :=
  begin
    apply grothendieck.trans,
    apply sjx,
    rintros f Hf,
    apply superset_covers,
    apply yank_le_map,
    apply comp_le_comps,
    apply Hf,
    apply superset_covers,
    apply le_yank_comp,
    apply hR,
    apply Hf,
  end

structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : sieve_set C)
[g : @grothendieck C 𝒞 J]

def covers {Y:C} (J : sieve_set C) (S : @sieve C 𝒞 X) (f : Y ⟶ X) := yank S f ∈ J(Y)

variables {R S : @sieve C 𝒞 X}
lemma intersection_covers (rj : R ∈ J(X)) (sj : S ∈ J(X)) : R ⊓ S ∈ J(X) :=
begin
  apply grothendieck.trans R, assumption,
  intros f Hf,
  apply superset_covers,
  show yank S (f.hom) ⊆ yank (R ⊓ S) (f.hom),
    intros g gys, refine ⟨_,gys⟩,
    apply sieve.subs,
    assumption,
  apply grothendieck.stab, assumption, apply_instance
end

def sieve_set.trivial (C : Type u) [𝒞 : category.{v} C] : sieve_set C := λ X, {⊤}
instance trivial.grothendieck : grothendieck (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _
, stab := λ X Y S HS h , begin have : S = ⊤, apply set.eq_of_mem_singleton, assumption, rw [this, yank_top], apply set.mem_singleton end
, trans := λ X S HS R HR, begin
  have : S = ⊤, apply set.eq_of_mem_singleton, assumption, subst this,
  apply set.mem_singleton_of_eq,
  apply lattice.top_unique,
  rintros g Hg,
  have H, refine (ge_of_eq (set.eq_of_mem_singleton (HR _ Hg))),
  have H₂, refine H _, apply over.mk (𝟙 _),
  trivial,
  simp at H₂, rw [@category.id_comp _ _ _ _ g.hom ] at H₂, simp at H₂,
  assumption,
  end
}

/-- An example Grothendieck topology. -/
def dense (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S| ∀ {Y : C} (f : Y ⟶ X), ∃ (Z) (g : Z ⟶ Y), (over.mk (g ≫ f)) ∈ S.arrows }

instance dense.grothendieck : grothendieck (dense C) :=
{ max := λ X Y f, ⟨Y,𝟙 Y, ⟨⟩⟩
, stab :=
    begin
      intros X Y S H h Z f,
      rcases H (f ≫ h) with ⟨W,g,H⟩,
      refine ⟨W,g,_⟩,
      simp, apply H
    end
, trans :=
    begin intros X S H₁ R H₂ Y f,
      rcases H₁ f with ⟨Z,g,H₃⟩,
      rcases H₂ _ H₃ (𝟙 Z) with ⟨W,h,H₄⟩,
      refine ⟨W,(h ≫ (𝟙 Z) ≫ g), _⟩,
      simp [dense] at *,
      apply H₄
    end
}

/-- The atomic sieveset just contains all of the non-empty sieves. -/
def atomic (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S | ∃ x, x ∈ S.arrows}

/-- The atomic sieveset is a grothendieck topology when it is inhabited and
    satisfies the 'square' property. Which says that every span `Y ⟶ X ⟵ Z` forms a commuting
    diagram. -/
instance atomic.grothendieck
  (square :
    ∀ {X Y Z : C}
      (yx : Y ⟶ X)
      (zx : Z ⟶ X),
      ∃ (W : C) (wy : W ⟶ Y) (wz : W ⟶ Z),
      wy ≫ yx = wz ≫ zx)
    (inh : ∀ (X : C), inhabited (over X))
      : grothendieck (atomic C)
       :=
{ max := λ X, begin
    refine ⟨_,_⟩,
    apply inhabited.default,
    trivial
  end
, stab := begin
    rintros X Y S HS h,
    cases HS with f HS,
    rcases square h f.hom with ⟨a,b,c,d⟩,
    refine ⟨over.mk b,_⟩,
    simp, rw d,
    apply sieve.subs, assumption
   end
, trans := begin
    rintros _ _ ⟨f,fS⟩ _ Ra,
    rcases Ra f fS with ⟨g,h₁⟩,
    refine ⟨_,h₁⟩
  end
}

-- [todo] a basis for a topology
-- [TODO] sheaves on a topology
-- [TODO] the topological site

end grothendieck

end category_theory
