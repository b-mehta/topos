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

def skeleton_obj := quotient (skeleton.setoid C)
#check @quotient.rep
#check @set.image


-- def skeleton.arrows.setoid : setoid (Σ (X Y : C), X ⟶ Y) :=
-- { r := λ ⟨X₁,Y₁,f₁⟩ ⟨X₂,Y₂,f₂⟩, ∃ (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂), f₁ ≫ y.hom = x.hom ≫ f₂,
--   iseqv := begin
--     refine ⟨_,_,_⟩,
--     { rintro ⟨X,Y,f⟩, refine ⟨iso.refl X, iso.refl Y, _⟩,
--       simp, },
--     { rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨x,y,e⟩,
--       refine ⟨x.symm,y.symm,_⟩,
--       simp,
--       rw [iso.eq_inv_comp, ← category.assoc, ←e,  iso.comp_inv_eq],},
--     { rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨X3,Y3,f3⟩ ⟨x12,y12,e12⟩ ⟨x23,y23,e23⟩,
--       refine ⟨iso.trans x12 x23,iso.trans y12 y23,_⟩,
--       simp, rw [←category.assoc, e12, category.assoc, e23]}
--   end
-- }
-- local attribute [instance] skeleton.arrows.setoid

-- def skeleton.arrows := quotient (skeleton.arrows.setoid C)

variable {C}
def skeleton_obj.mk (X : C) : skeleton_obj C := ⟦X⟧

structure is_skeleton (D : set C) : Prop :=
(skel_prop : ∀ {X Y} (hx : X ∈ D) (hy : Y ∈ D), (X ≅ Y) → X = Y )
(ess_surj : ∀ (X : C), ∃ {Y:C}, Y ∈ D ∧ nonempty (X ≅ Y))

instance {D : set C} : category { X : C // X ∈ D } := by apply_instance

lemma skeleton_exists : ∃ (D : set C), @is_skeleton C 𝒞 D :=
begin
  let D : set C := {X : C | ∃ XX : quotient (skeleton.setoid C), quotient.out XX = X},
  refine ⟨D,_,_⟩,
  { rintros X Y ⟨XX,rfl⟩ ⟨YY,rfl⟩ i,
    congr,
    induction XX,
    induction YY,
    apply quotient.sound',
    have h1, refine (@quotient.mk_out C (skeleton.setoid C) XX), cases h1,
    have h2, refine (@quotient.mk_out C (skeleton.setoid C) YY), cases h2,
    refine ⟨calc XX ≅ _ : h1.symm ... ≅ _ : i ... ≅ YY : h2⟩,
    refl, refl,},
  { rintros X,
    refine ⟨quotient.out ⟦X⟧,⟨⟦X⟧,rfl⟩,are_iso.symm (@quotient.mk_out C (skeleton.setoid C) X)⟩,
  }
end

def skeleton.under.setoid (X : C) : setoid (under X) :=
{ r := λ f g, ∃ (y : f.right ≅ g.right), f.hom ≫ y.hom = g.hom
, iseqv := sorry
}

def skeleton.under (X : C) := quotient (skeleton.under.setoid X)
def skeleton.under.mk  (f : X ⟶ Y)  : skeleton.under X := @quotient.mk _ (skeleton.under.setoid X) (under.mk f)


def skeleton.arrows.mk {X Y : C} (f : X ⟶ Y) : skeleton.arrows C := ⟦⟨X,Y,f⟩⟧

def skeleton.arrows.dom (f : skeleton.arrows C) : skeleton C :=
quotient.lift_on' f (λ S, skeleton.mk S.1)
  (begin
    rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨x,y,e⟩,
    refine quotient.sound' ⟨x⟩,
  end)

def skeleton.arrows.cod (f : skeleton.arrows C) : skeleton C :=
quotient.lift_on' f (λ S, skeleton.mk S.2.1)
  (begin
    rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨x,y,e⟩,
    refine quotient.sound' ⟨y⟩,
  end)


def skeleton.concrete_lemma : ∀ (f : skeleton.arrows C) (x : f.dom = ⟦X⟧) (y : f.cod = ⟦Y⟧), ∃ (f' : X ⟶ Y), f = skeleton.arrows.mk f' :=
begin
  intros f,
  induction f,
  rcases f with ⟨A,B,f⟩,
  intros x y,
  have xx : A ≅ X, refine (classical.choice (quotient.exact x)),
  have yy : B ≅ Y, refine (classical.choice (quotient.exact y)),
  refine ⟨(xx.inv ≫ f ≫ yy.hom),_ ⟩,
  refine quotient.sound ⟨xx,yy,_⟩, simp,
  intros, refl
end
def skeleton.pinch  (f : skeleton.arrows C) (d : f.dom = ⟦X⟧): skeleton.under X := sorry -- [todo] this is the crux.

def skeleton.hom (XX YY : skeleton C) : Type (max u v) :=
{f : skeleton.arrows C // f.dom = XX ∧ f.cod = YY }

-- [note] this doesn't work because it double-counts homs.
-- structure skeleton.hom (XX YY : skeleton C) : Type (max u v) :=
-- (dom : C)
-- (cod : C)
-- (hom : dom ⟶ cod)
-- (dom_mem : ⟦dom⟧ = XX)
-- (cod_mem : ⟦cod⟧ = YY)



def hom_iso {X1 Y1 X2 Y2 : C} (f1 : X1 ⟶ Y1) (f2 : X2 ⟶ Y2) := ∃ (x : X1 ≅ X2) (y : Y1 ≅ Y2), x.hom ≫ f2 = f1 ≫ y.hom

-- def skeleton.hom2 (XX YY : skeleton C) : Type (max u v) :=
-- quotient.lift_on₂' XX YY (λ X Y, X ⟶ Y)
-- (begin end)


set_option pp.proofs true

def skeleton.arrows.id (XX : skeleton C) : skeleton.arrows C :=
quotient.lift_on' XX (λ X, skeleton.arrows.mk (𝟙 X)) (
  begin
    rintros X1 X2 ⟨x⟩, refine quotient.sound' ⟨x,x,_⟩, simp
   end
)

def skeleton.id (XX : skeleton C) : skeleton.hom XX XX :=
begin
refine ⟨skeleton.arrows.id XX, _, _⟩,
repeat {induction XX, refine quotient.sound' ⟨_⟩, refl, refl,}
end

def skeleton.arrows.comp_prop (ff gg hh : skeleton.arrows C) : Prop :=
∃ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, skeleton.arrows.mk f = ff ∧ skeleton.arrows.mk g = gg ∧ skeleton.arrows.mk (f ≫ g) = hh

def skeleton.comp1 {XX YY ZZ : skeleton C} (f : skeleton.hom XX YY) (g : skeleton.hom YY ZZ) : skeleton.arrows C :=
begin
  induction XX with X,
  induction YY with Y,
  induction ZZ with Z,
  rcases f with ⟨f,fd,fc⟩,
  rcases g with ⟨g,gd,gc⟩,
  have hf, apply skeleton.concrete_lemma f fd fc,
  have hg, apply skeleton.concrete_lemma g gd gc,


end


def skeleton.arrows.comp [∀ (X Y : C), decidable (are_iso X Y)] (f g: skeleton.arrows C) : skeleton.arrows C :=
quotient.lift_on₂' f g (λ f g,
  @dite _ _ _ (λ e : are_iso f.2.1 g.1, skeleton.arrows.mk (f.2.2 ≫ (classical.choice e).hom ≫ g.2.2)) (λ _, skeleton.arrows.mk (𝟙 f.1))
)
  (begin rintros ⟨X1,Y1,f1⟩ ⟨Y1',Z1,g1⟩ ⟨X2,Y2,f2⟩ ⟨Y2',Z2,g1⟩ ⟨x,y,e⟩ ⟨y',z,e'⟩,
    simp,
    split_ifs with y1 y2,
    {cases y1, cases y2,
    refine quotient.sound' ⟨x,z,_⟩,
    simp, rw e',
    }

    have d : decidable (are_iso Y1 Y1'), by apply classical.dec _,
    cases d,
    rw dite.decidable,
    show dite (are_iso Y1 Y1')
      (λ (e),
         skeleton.arrows.mk (f1 ≫ (classical.choice e).hom ≫ g1))
      (λ (_x),
         skeleton.arrows.mk (𝟙 X1)) =
    dite (are_iso Y2 Y2')
      (λ (e),
         skeleton.arrows.mk (f2 ≫ (classical.choice e).hom ≫ g1))
      (λ (_x),
         skeleton.arrows.mk (𝟙 X2)),
    end)


end category_theory