import .grothendieck
import topology.category.Top
import category_theory.limits.shapes.pullbacks

open topological_space
open lattice
open category_theory
open category_theory.limits

universes u v

def cover (X : Top) : arrow_set (opens X) := λ U ℱ, ∀ (x ∈ U), ∃ V : over U, (V ∈ ℱ) ∧  x ∈ V.left

def subset_inclusion {X : Top} (U : opens X) : (opens.to_Top _).obj U ⟶ X :=
begin split, apply continuous_induced_dom end

/-- This is just the pullback of f with the inclusion function for U. opens.map gives the other one.  -/
def restrict {X Y : Top} (f : Y ⟶ X) (U : opens X) : (opens.to_Top _).obj ((opens.map f).obj U) ⟶ (opens.to_Top _).obj U :=
begin
  refine ⟨λ y, ⟨f.1 y.1, y.2⟩,_⟩,
  apply (embedding.continuous_iff embedding_subtype_val).2,
  simp [function.comp],
  show continuous (f.val ∘ subtype.val),
  apply continuous.comp f.2 continuous_subtype_val
end

@[simp] lemma ctns_comp_simp {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} : (f ≫ g).val x = g.val (f.val x) :=
begin refl, end

def subset_inclusion_natural {X Y : Top} {V : opens X} {f : Y ⟶ X} :
  subset_inclusion ((opens.map f).obj V) ≫ f = restrict f _  ≫ subset_inclusion V
  := begin apply subtype.ext.2, funext, cases f, simp [restrict, subset_inclusion] end

def over.is_open {X : Top} (U : over X) := is_open {x : X | ∃ (u : U.left), U.hom u = x}
def are_open {X : Top} (ℱ : set (over X)) := ∀ {U : over X}, U ∈ ℱ →  over.is_open U

def covers : arrow_set Top :=
λ (X : Top) (ℱ : set (over X)), (are_open ℱ) ∧ ∀ (x : X), ∃ (U : over X) (u : U.left), U ∈ ℱ ∧ (U.hom : { f : _ // _}) u = x

-- [todo] remove these instances
def Top_is_category : category Top := by apply_instance
def Top_has_limits : @has_limits Top Top_is_category := by apply_instance
def Top_has_pullbacks : @has_pullbacks Top Top_is_category :=
⟨@has_limits.has_limits_of_shape _ _ Top_has_limits _ _⟩

instance : topological_space unit :=
{ is_open := λ U, true,
  is_open_univ := ⟨⟩,
  is_open_inter := λ _ _ _ _, ⟨⟩,
  is_open_sUnion := λ _ _, ⟨⟩
}

def pt_hom {X : Top} (x : X) : (Top.of unit) ⟶ X :=
subtype.mk (λ _, x) (λ U oU, ⟨⟩)

@[simp] lemma pt_hom_simp {X Y : Top} {x : X} {g : X ⟶ Y}: pt_hom x ≫ g = pt_hom (g x) :=
begin apply subtype.ext.2, funext, refl end

instance covers_is_grothendieck_basis : @grothendieck.basis Top Top_is_category Top_has_pullbacks covers :=
begin
  refine {..},
  { rintros X Y e, split,
    {sorry},
    {intro y, refine ⟨over.mk e.hom,e.inv y,_,_⟩,
      simp,
    dsimp, simp}
  },
  { -- idea: the pullback of `g` with the `U : over X` containing `x` gives the new cover.
    -- finding the point in `pullback g U` is found by lifting the cone with the point topology `Y ⟵ unit ⟶ U.left`.
    refine λ X Y ℱ h₁ (g : Y ⟶ X), _,
    rcases h₁ with ⟨o,h₁⟩,
    split,
    { sorry
    },
    {intro y,
    rcases h₁ (g y) with ⟨U,u,h₂,h₃⟩,
    refine ⟨over.mk (pullback.fst : pullback g U.hom ⟶ _),_,_,_⟩,
    refine (pullback.lift (pt_hom y) (pt_hom u) (by simp [h₃]) : (Top.of unit) ⟶ pullback g U.hom).1 ⟨⟩,
    simp [over.pullback],
    refine ⟨U,h₂,rfl⟩,
    simp, dsimp,
    suffices : ((pullback.lift (pt_hom y) (pt_hom u) (by simp [h₃]) : (Top.of unit) ⟶ pullback g U.hom) ≫ (pullback.fst : pullback g U.hom ⟶ Y)).val punit.star = y,
      apply this,
    erw pullback.fac_fst,
    simp [pt_hom]}
  },
  { intros X ℱ h₁ _ _,
    rcases h₁ with ⟨oℱ,h₁⟩,
    split,
    {sorry},
    {    intro x,
    rcases h₁ x with ⟨U,u,h₄,h₅⟩,
    rcases (h₃ h₄) with ⟨oo,h₃⟩,
    rcases h₃ u with  ⟨V,v,h₆,h₇⟩,
    refine ⟨over.mk (V.hom ≫ U.hom), v, ⟨U,h₄,V,h₆,rfl⟩, _⟩,
    show U.hom (V.hom v) = x,
    rw [h₇, h₅],}
  }
end

instance Top_is_grothendieck : grothendieck _ :=
@grothendieck.of_basis Top Top_is_category Top_has_pullbacks covers covers_is_grothendieck_basis