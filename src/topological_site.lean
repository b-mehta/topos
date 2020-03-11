/- Author: E.W.Ayers
-/

import .grothendieck
import topology.category.Top
import category_theory.limits.shapes.pullbacks

open topological_space
open lattice
open category_theory
open category_theory.limits

universes u v

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

def are_open {X : Top} (ℱ : set (over X)) := ∀ {U : over X}, U ∈ ℱ →  is_open_map U.hom

def covers : arrow_set Top :=
λ (X : Top) (ℱ : set (over X)), (are_open ℱ) ∧ ∀ (x : X), ∃ (U : over X) (u : U.left), U ∈ ℱ ∧ (U.hom : { f : _ // _}) u = x

-- [todo] remove these instances?
def Top_is_category : category Top := by apply_instance
def Top_has_limits : @has_limits Top Top_is_category := by apply_instance
instance Top_has_pullbacks : @has_pullbacks Top Top_is_category :=
⟨@has_limits.has_limits_of_shape _ _ Top_has_limits _ _⟩

-- instance : topological_space unit :=
-- { is_open := λ U, true,
--   is_open_univ := ⟨⟩,
--   is_open_inter := λ _ _ _ _, ⟨⟩,
--   is_open_sUnion := λ _ _, ⟨⟩
-- }

def pt_hom {X : Top} (x : X) : (Top.of unit) ⟶ X := -- [todo] should be punit
subtype.mk (λ _, x) (λ U oU, ⟨⟩)

@[simp] lemma pt_hom_simp {X Y : Top} {x : X} {g : X ⟶ Y}: pt_hom x ≫ g = pt_hom (g x) :=
begin apply subtype.ext.2, funext, refl end

variables {X Y : Top.{0}}

lemma ctns_hom {g : X ⟶ Y} : ∀ U : set Y, is_open U → is_open (g ⁻¹' U) :=
begin intros, cases g, apply g_property, assumption  end

lemma iso_is_open {e : Y ≅ X} : @are_open X {over.mk e.hom} :=
begin
  rintros U (rfl|wtf),
  show is_open_map e.hom,
  intros V o,
  have  : e.hom '' V = e.inv ⁻¹' V,
    ext, split, rintros ⟨y,yV,rfl⟩, simpa, intros, refine ⟨e.inv x,a,_⟩, simp,
  rw this,
  apply ctns_hom, assumption,
  cases wtf,
end

lemma iso_covers {e : Y ≅ X} :

def pullback_mk_pt {X Y Z : Top} {f : X ⟶ Z} {g : Y ⟶ Z} (x : X) (y : Y) (e : f(x) = g(y)) : (pullback f g).1 :=
@pullback.lift Top _ _ X Y Z f g _ (pt_hom x) (pt_hom y) (begin simp, rw e,  end) ⟨⟩

@[simp] lemma pullback_pt_fst {X Y Z : Top} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y} (e : f(x) = g(y)) :
  subtype.val (@pullback.fst _ _ X Y Z f g _) (pullback_mk_pt x y e) = x :=
begin refl end

@[simp] lemma pullback_pt_snd {X Y Z : Top} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y} (e : f(x) = g(y)) :
  subtype.val (@pullback.snd _ _ X Y Z f g _) (pullback_mk_pt x y e) = y :=
begin refl end

@[simp] lemma pullback_pt_lift {X Y Z : Top} {f : X ⟶ Z} {g : Y ⟶ Z} (v : pullback f g) :
  pullback_mk_pt ((pullback.fst : pullback f g ⟶ X).val v) ((pullback.snd : pullback f g ⟶ Y).val v) (begin change (pullback.fst ≫ f).val v = (pullback.snd ≫ g).val v, rw pullback.condition end) = v :=
begin
cases v,
apply subtype.ext.2,
simp, funext,
cases j,
refl, refl,
have l : f _ = _, apply v_property walking_cospan.hom.inl,
apply l,
end

lemma pullback_pt_asdf {X Y Z : Top} {f : X ⟶ Z} {g : Y ⟶ Z} {P : pullback f g → Prop} :
  (∃ v : pullback f g, P(v)) ↔ ∃ (x : X) (y : Y) (e : f(x) = g(y)), P(pullback_mk_pt x y e) :=
begin
  split,
  { rintros ⟨v,h⟩,
    refine ⟨(pullback.fst : pullback f g ⟶ X).1 v, (pullback.snd : pullback f g ⟶ Y).1 v,_,_⟩,
    change (pullback.fst ≫ f).val v = (pullback.snd ≫ g).val v,
      rw pullback.condition,
    simp,
    apply h,
  },
  {
    rintros ⟨x,y,e,h⟩,
    refine ⟨pullback_mk_pt x y e, h⟩
  }
end

lemma pullback_preserves_open {ℱ : set (over X)} {o : are_open ℱ} {g : Y ⟶ X} : are_open (over.pullback g '' ℱ) :=
begin
  rintros U ⟨f,fℱ,rfl⟩ V oV,
  change set (pullback g f.hom).α at V,
  change is_open {y : Y | ∃ v : (pullback g f.hom), _ ∧ _ = y},
  have : {y : Y | ∃ v : (pullback g f.hom).α, v ∈ V ∧ (pullback.fst : pullback g f.hom ⟶ Y).val v = y} = {y : Y | ∃ x z e, (pullback.fst : pullback g f.hom ⟶ Y).val (pullback_mk_pt x z e) = y},
    ext y,
    apply pullback_pt_asdf,
  /- sketch:
     - pullback.fst '' V = {y : Y | ∃ ⟨y,z⟩ ∈ V, g(y) = f(z)} by the implementation of pullbacks for Type.
     - ... = g ⁻¹' {x : X | ∃ z ∈ f.left, x = f(z)}
     which is open by assumption
   -/
  suffices : is_open {y : Y | ∃ v : pullback g f.hom, v ∈ _ ∧ subtype.val (pullback.fst : pullback g f.hom ⟶ ) v = y},
  have : {y : Y | ∃ v : pullback g f.hom, _} = {y : Y | ∃ (z : f.left) (e : g(y) = f.hom(z)), pullback_mk_pt y z e = _},
    ext, split, {
      rintro ⟨⟨u,_⟩,_⟩,
      refine ⟨u walking_cospan.right,_⟩, rw ← a_h,
      have hl : g _ = _, apply a_w_property walking_cospan.hom.inl,
      have hr : f.hom _ = _, apply a_w_property walking_cospan.hom.inr,
      rw [hr],
      apply hl.symm
    },
    { rintro ⟨_,_⟩,
      refine ⟨⟨_,_⟩,_⟩,
        intro, cases j, refine x, refine a_w, refine g x,
        rintro _ _ (_ | _), simp, apply a_h, refl,
        refl,
    },
  rw this,
  have : {y : Y | ∃ z : f.left, f.hom (z) = g(y)} = g ⁻¹' {x | ∃ z : f.left, f.hom (z) = x}, refl,
  rw this,
  apply ctns_hom,
  apply o VF,
end

instance covers_is_grothendieck_basis : @grothendieck.basis Top Top_is_category Top_has_pullbacks covers :=
begin
  refine {..},
  { rintros X Y e, split,
    {apply iso_is_open},
    {intro y, refine ⟨over.mk e.hom,e.inv y,_,_⟩,
      simp,
    dsimp, simp}
  },
  { -- idea: the pullback of `g` with the `U : over X` containing `x` gives the new cover.
    -- finding the point in `pullback g U` is found by lifting the cone with the point topology `Y ⟵ unit ⟶ U.left`.
    refine λ X Y ℱ h₁ (g : Y ⟶ X), _,
    rcases h₁ with ⟨o,h₁⟩,
    split,
    { apply pullback_preserves_open, assumption,
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
    { rintros U ⟨f,VF,g,gf,rfl⟩,

     },
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