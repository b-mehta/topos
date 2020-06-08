/- Author: E.W.Ayers.
   This section roughly follows Chapter 3, §1, §2 of Sheaves in Geology and Logic by Saunders Maclane and Ieke M.
 -/

import category_theory.whiskering
import sieve
import pullbacks

universes u v w
namespace category_theory

open category_theory limits order lattice

/-- A set of sieves for every object in the category: a candidate to be a Grothendieck topology. -/
def sieve_set (C : Type u) [category.{v} C] := Π (X : C), set (sieve X)

def arrow_set (C : Type u) [category.{v} C] := Π (X : C), set (set (over X))

def sieve_set.trivial (C : Type u) [category.{v} C] : sieve_set C := λ X, {⊤}

def sieve_set.dense (C : Type u) [category.{v} C] : sieve_set C :=
λ X, {S | ∀ {Y : C} (f : Y ⟶ X), ∃ Z (g : Z ⟶ Y), over.mk (g ≫ f) ∈ S.arrows }

/-- The atomic sieve_set just contains all of the non-empty sieves. -/
def sieve_set.atomic (C : Type u) [category.{v} C] : sieve_set C :=
λ X, {S | ∃ x, x ∈ S.arrows}

/-- The smallest sieve set containing the given arrow set. -/
def sieve_set.generate {C : Type u} [category.{v} C] (K : arrow_set C) : sieve_set C :=
λ X, {S | ∃ R ∈ K X, R ⊆ S.arrows}

open sieve category

/--
Definition of a Grothendieck Topology: a set of sieves `J X` on each object `X` satisfying three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.
-/
class grothendieck {C : Type u} [category.{v} C] (J : sieve_set C) :=
(max : ∀ X, ⊤ ∈ J X)
(stab : ∀ (X Y : C) (S ∈ J X) (h : Y ⟶ X), sieve.pullback S h ∈ J(Y))
(trans : ∀ ⦃X : C⦄ (S ∈ J X) (R : sieve X), (∀ (f : over X), f ∈ S → sieve.pullback R f.hom ∈ J f.left) → R ∈ J(X))

/-- A site is a category equipped with a grothendieck topology. -/
structure Site :=
(C : Type u)
[𝒞 : category.{v} C]
(J : sieve_set C)
[g : grothendieck J]

namespace grothendieck

variables {C : Type u} [category.{v} C]
variables {X Y : C} {S R : sieve X}
variables {J : sieve_set C} [grothendieck J]

def over.pullback [has_pullbacks.{v} C] {X Y : C} (f : X ⟶ Y) (g : over Y) : over X :=
over.mk (@pullback.fst _ _ _ _ _ f g.hom _)

@[simp] lemma over_pullback_def [has_pullbacks.{v} C] {X Y : C} (f : X ⟶ Y) (g : over Y) :
  (over.pullback f g).hom = pullback.fst := rfl

class basis [has_pullbacks.{v} C] (K : arrow_set C) :=
(has_isos      : ∀ {X Y : C} (e : X ≅ Y), {over.mk e.hom} ∈ K(Y))
(has_pullbacks : ∀ {X Y : C} {ℱ : set (over X)} (h₁ : ℱ ∈ K(X)) (g : Y ⟶ X), set.image (over.pullback g) ℱ ∈ K(Y))
(trans : ∀ {X} {ℱ : set (over X)},
         ∀ (h₁ : ℱ ∈ K(X)),
         ∀ (𝒢 : ∀ {f : over X} (hf :f ∈ ℱ), set (over f.left)),
         ∀ (h₃ : ∀ {f : over X} (hf : f ∈ ℱ), 𝒢 hf ∈ K(f.left)),
           {h : over X | ∃ (f : over X) (hf : f ∈ ℱ) (g : over f.left) (hg : g ∈ 𝒢 hf), h = over.mk (g.hom ≫ f.hom)} ∈ K(X))

instance of_basis [has_pullbacks.{v} C] {K : arrow_set C} [basis K] : grothendieck (sieve_set.generate K) :=
{ max := λ X, ⟨{over.mk (𝟙 X)}, basis.has_isos (iso.refl X), λ f h, ⟨⟩⟩,
  stab := begin
    rintros X Y S ⟨ℱ,h₁,h₂⟩ f,
    refine ⟨_,basis.has_pullbacks h₁ f,_⟩,
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
    refine ⟨_,basis.trans h₁ _ _,_⟩,
    { intros f hf, apply (classical.some (h₄ f (h₂ hf)))},
    { intros f hf, rcases classical.some_spec (h₄ f (h₂ hf)) with ⟨h10,h11⟩, apply h10 },
    {
      rintros f ⟨g,h₅,h,h₆,rfl⟩,
      rcases classical.some_spec (h₄ g (h₂ h₅)) with ⟨h11,h12⟩,
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
  have : over.mk (𝟙 h.left) ∈ (sieve.pullback R h.hom),
    apply Hss,
    simp, rw [@category.id_comp _ _ h.left _ h.hom], simp,
    apply H2,
  have : sieve.pullback R h.hom = ⊤,
    apply top_of_has_id this,
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
      apply sieve.pullback_le_map,
      apply comp_le_comps,
      apply Hf,
    apply superset_covers,
      apply le_pullback_comp,
    apply hR,
    apply Hf,
  end

def covers (J : sieve_set C) (S : sieve X) (f : Y ⟶ X) :=
sieve.pullback S f ∈ J(Y)

lemma intersection_covers (rj : R ∈ J(X)) (sj : S ∈ J(X)) : R ⊓ S ∈ J(X) :=
begin
  apply grothendieck.trans R, assumption,
  intros f Hf,
  apply superset_covers,
  show sieve.pullback S (f.hom) ⊆ sieve.pullback (R ⊓ S) (f.hom),
    intros g gys, refine ⟨_,gys⟩,
    apply sieve.subs,
    assumption,
  apply grothendieck.stab, assumption, apply_instance
end

open sieve_set

instance trivial.grothendieck : grothendieck (sieve_set.trivial C) :=
{ max := λ X, set.mem_singleton _,
  stab := λ X Y S HS h,
  begin
    have : S = ⊤,
      apply set.eq_of_mem_singleton, assumption,
    rw [this, sieve.pullback_top],
    apply set.mem_singleton
  end,
  trans := λ X S HS R HR, begin
    have : S = ⊤, apply set.eq_of_mem_singleton, assumption, subst this,
    apply set.mem_singleton_of_eq,
    apply top_unique,
    rintros g Hg,
    have : sieve.pullback R (g.hom) ≥ ⊤ := (ge_of_eq (set.eq_of_mem_singleton (HR g Hg))),
    have : over.mk (𝟙 g.left) ∈ sieve.pullback R (g.hom), refine this _, trivial,
    have : over.mk (𝟙 (g.left) ≫ g.hom) ∈ R, apply this,
    simpa,
  end }

instance dense.grothendieck : grothendieck (dense C) :=
{ max := λ X Y f, ⟨Y, 𝟙 Y, ⟨⟩⟩,
  stab :=
    begin
      intros X Y S H h Z f,
      rcases H (f ≫ h) with ⟨W,g,H⟩,
      refine ⟨W,g,_⟩,
      simpa,
    end,
  trans :=
    begin
      intros X S H₁ R H₂ Y f,
      rcases H₁ f with ⟨Z,g,H₃⟩,
      rcases H₂ _ H₃ (𝟙 Z) with ⟨W,h,H₄⟩,
      refine ⟨W, (h ≫ (𝟙 Z) ≫ g), _⟩,
      simpa using H₄,
    end }

/--
A category satisfies the right Ore condition if any span can be completed to a
commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition.
-/
def right_ore_condition (C : Type u) [category.{v} C] : Prop :=
∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ W (wy : W ⟶ Y) (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

/--
The atomic sieveset is a grothendieck topology when it
satisfies the 'square' property. Which says that every span `Y ⟶ X ⟵ Z` forms a commuting
diagram.
-/
instance atomic.grothendieck
  (hro : right_ore_condition C)
  : grothendieck (atomic C) :=
{ max := λ X, ⟨over.mk (𝟙 _), ⟨⟩⟩,
  stab :=
  begin
    intros X Y S HS h,
    cases HS with f HS,
    rcases hro h f.hom with ⟨Z, zy, zf, comm⟩,
    refine ⟨over.mk zy, _⟩,
    erw [mem_pullback, comm],
    apply downward_closed,
    exact HS
  end,
   trans :=
   begin
     rintros _ _ ⟨f, fS⟩ _ Ra,
     rcases Ra f fS with ⟨g, h₁⟩,
     refine ⟨_, h₁⟩
   end }

open opposite

def matching_family (P : Cᵒᵖ ⥤ Type v) (S : sieve X) :=
S.as_functor ⟶ P

def amalgamation {P : Cᵒᵖ ⥤ Type v} {S : sieve X} (γ : matching_family P S) :=
{α : yoneda.obj X ⟶ P // sieve.functor_inclusion S ≫ α = γ}

def sheaf (J : sieve_set C) [grothendieck J] (P : Cᵒᵖ ⥤ Type v) :=
∀ (X : C) (S : sieve X) (γ : matching_family P S), S ∈ J(X) → unique (amalgamation γ)

end grothendieck

end category_theory
