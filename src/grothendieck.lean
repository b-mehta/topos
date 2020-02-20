/- Author: E.W.Ayers.
   This section roughly follows Chapter 3, §1, §2 of Sheaves in Geology and Logic by Saunders Maclane and Ieke M.
 -/

import category_theory.whiskering
import .sieve
import .pullbacks

universes u v w
namespace category_theory

open order lattice

def sieve_set (C : Type u) [𝒞 : category.{v} C] :=  Π (X : C), set (sieve X)

def arrow_set (C : Type u) [𝒞 : category.{v} C] :=  Π (X : C), set (set (over X))

def sieve_set.trivial (C : Type u) [𝒞 : category.{v} C] : sieve_set C := λ X, {⊤}

def sieve_set.dense (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S| ∀ {Y : C} (f : Y ⟶ X), ∃ (Z) (g : Z ⟶ Y), (over.mk (g ≫ f)) ∈ S }

/-- The atomic sieve_set just contains all of the non-empty sieves. -/
def sieve_set.atomic (C : Type u) [𝒞 : category.{v} C] : sieve_set C :=
λ X, {S | ∃ x, x ∈ S}

def sieve_set.generate {C : Type u} [𝒞 : category.{v} C] (K : arrow_set C) : sieve_set C :=
λ X, {S | ∃ R ∈ K(X), R ⊆ S.arrows}

open sieve category

/-- Definition of a Grothendiek Topology. -/
class grothendieck {C : Type u} [𝒞 : category.{v} C] (J : sieve_set C) :=
(max : ∀ X, ⊤ ∈ J(X))
(stab : ∀ (X Y : C) (S ∈ J(X)) (h : Y ⟶ X), yank S h ∈ J(Y))
(trans :
  ∀ ⦃X : C⦄,
  ∀ (S ∈ J(X)),
  ∀ (R : sieve X),
  ∀ (_ : ∀ (f : over X),
         ∀ (_ : f ∈ S),
           yank R f.hom ∈ J(f.left)),
    R ∈ J(X)
)

structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : sieve_set C)
[g : @grothendieck C 𝒞 J]

namespace grothendieck

variables {C : Type u} [𝒞 : category.{v} C]  {X Y : C} {S R : sieve X} {J : sieve_set C} [grothendieck J]
include 𝒞

class basis [@category_theory.limits.has_pullbacks C 𝒞] (K : arrow_set C) :=
(i  : ∀ {X Y : C} (e : X ≅ Y), {over.mk e.hom} ∈ K(Y))
(ii : ∀ {X Y : C} {ℱ : set (over X)} (h₁ : ℱ ∈ K(X)) (g : Y ⟶ X), set.image (over.pullback g) ℱ ∈ K(Y))
(iii : ∀ {X} {ℱ : set (over X)},
       ∀ (h₁ : ℱ ∈ K(X)),
       ∀ (𝒢 : ∀ {f : over X} (hf :f ∈ ℱ), set (over f.left)),
       ∀ (h₃ : ∀ {f : over X} (hf : f ∈ ℱ), 𝒢 hf ∈ K(f.left)),
         (⋃ (f : over X) (hf : f ∈ ℱ) (g : over f.left) (hg : g ∈ 𝒢 hf), {over.mk (g.hom ≫ f.hom)}) ∈ K(X))

instance of_basis [@category_theory.limits.has_pullbacks C 𝒞] {K : arrow_set C} [basis K] : grothendieck (sieve_set.generate K) :=
{ max := λ X, ⟨{over.mk (𝟙 X)}, basis.i K (iso.refl X), λ f h, ⟨⟩⟩,
  stab := begin
    rintros X Y S ⟨ℱ,h₁,h₂⟩ f,
    refine ⟨_,basis.ii h₁ f,_⟩,
    rintros g ⟨h,h₃,rfl⟩,
    show over.mk (_ ≫ f) ∈ S,
    simp,
    rw limits.pullback.condition,
    apply sieve.subs,
    apply h₂,
    apply h₃
  end,
  trans := begin
    rintros X S ⟨ℱ,h₁,h₂⟩ R h₃,
    have h₄ :  ∀ (f : over X), f ∈ S → ∃ T, T ∈ K f.left ∧ T ⊆ {sl : over f.left | (over.mk $ sl.hom ≫ f.hom) ∈ R },
      rw [sieve_set.generate] at h₃, simp at h₃,
      exact h₃,
    rw [sieve_set.generate],
    show ∃ (T : set (over X)) (H : T ∈ K X), T ⊆ R.arrows,
    refine ⟨_,basis.iii h₁ _ _,_⟩,
    -- [TODO] tidy up, find a more readable way to invoke choice.
    { intros f hf, apply (classical.some (h₄ f (h₂ hf)))},
    { intros f hf, rcases classical.some_spec (h₄ f (h₂ hf)) with ⟨h10,h11⟩, apply h10 },
    { -- This is pulling apart the `f ∈ ⋃ _ _ _ _, _` hypothesis. Probably a nicer way of doing it.
      rintros f ⟨T,⟨g,⟨h1,h2,rfl⟩,h3⟩, ⟨h4,⟨h5,rfl⟩,⟨h6,⟨h7,rfl⟩,⟨h8,⟨h9,rfl⟩,h10⟩⟩⟩⟩,
      simp at h10,
      cases a_h_w_h,
      rcases classical.some_spec (h₄ g (h₂ h5)) with ⟨h11,h12⟩,
      cases h10,
      apply h12,
      assumption
    }
  end,
}

def superset_covers (Hss : S ⊆ R) (sjx : S ∈ J(X)) : (R ∈ J(X)) :=
begin
  apply grothendieck.trans,
  apply sjx,
  rintros h H2,
  have : over.mk (𝟙 h.left) ∈ (yank R h.hom),
    apply Hss,
    simp, rw [@category.id_comp _ _ h.left _ h.hom], simp,
    apply H2,
  have : yank R h.hom = ⊤, apply top_of_has_id, apply this,
  rw this,
  apply grothendieck.max
end

def trans2
  (sjx : S ∈ J(X))
  (R : Π (f : over X), sieve f.left)
  (hR : Π f (H:f ∈ S), (R f) ∈ J(f.left))
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

def covers (J : sieve_set C) (S : sieve X) (f : Y ⟶ X) := yank S f ∈ J(Y)

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


open sieve_set

instance trivial.grothendieck : grothendieck (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _
, stab := λ X Y S HS h , begin have : S = ⊤, apply set.eq_of_mem_singleton, assumption, rw [this, yank_top], apply set.mem_singleton end
, trans := λ X S HS R HR, begin
  have : S = ⊤, apply set.eq_of_mem_singleton, assumption, subst this,
  apply set.mem_singleton_of_eq,
  apply lattice.top_unique,
  rintros g Hg,
  have : yank R (g.hom) ≥ ⊤, refine (ge_of_eq (set.eq_of_mem_singleton (HR g Hg))),
  have : over.mk (𝟙 g.left) ∈ yank R (g.hom), refine this _, trivial,
  have : over.mk (𝟙 (g.left) ≫ g.hom) ∈ R, apply this,
  simpa,
  end
}

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
      simp [sieve_set.dense] at *,
      apply H₄
    end
}

/-- The atomic sieveset is a grothendieck topology when it
    satisfies the 'square' property. Which says that every span `Y ⟶ X ⟵ Z` forms a commuting
    diagram. -/
instance atomic.grothendieck
  (square :
    ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X),
    ∃ (W : C)     (wy : W ⟶ Y) (wz : W ⟶ Z),
      wy ≫ yx = wz ≫ zx)
  : grothendieck (atomic C) :=
{ max := λ X, begin
    refine ⟨_,_⟩,
    apply over.mk (𝟙 _),
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

-- [TODO] sheaves on a topology
-- [TODO] the topological site

end grothendieck

end category_theory
