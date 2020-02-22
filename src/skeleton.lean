/- Author: E.W.Ayers
   Skeleton category. -/
import .pullbacks


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

def is_skeletal : Prop := ∀ (X Y : C), ¬ are_iso X Y
def skeleton := quotient (skeleton.setoid C)


def skeleton.arrows.setoid : setoid (Σ (X Y : C), X ⟶ Y) :=
{ r := λ ⟨X₁,Y₁,f₁⟩ ⟨X₂,Y₂,f₂⟩, ∃ (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂), f₁ ≫ y.hom = x.hom ≫ f₂,
  iseqv := begin
    refine ⟨_,_,_⟩,
    { rintro ⟨X,Y,f⟩, refine ⟨iso.refl X, iso.refl Y, _⟩,
      simp, },
    { rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨x,y,e⟩,
      refine ⟨x.symm,y.symm,_⟩,
      simp,
      rw [iso.eq_inv_comp, ← category.assoc, ←e,  iso.comp_inv_eq],},
    { rintros ⟨X1,Y1,f1⟩ ⟨X2,Y2,f2⟩ ⟨X3,Y3,f3⟩ ⟨x12,y12,e12⟩ ⟨x23,y23,e23⟩,
      refine ⟨iso.trans x12 x23,iso.trans y12 y23,_⟩,
      simp, rw [←category.assoc, e12, category.assoc, e23]}
  end
}
local attribute [instance] skeleton.arrows.setoid

def skeleton.arrows := quotient (skeleton.arrows.setoid C)

variable {C}

def skeleton.mk (X : C) : skeleton C := ⟦X⟧
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

def skeleton.hom (XX YY : skeleton C) : Type (max u v) :=
{f : skeleton.arrows C // f.dom = XX ∧ f.cod = YY }

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

noncomputable def skeleton.arrows.comp (f g: skeleton.arrows C) : Π (e : f.cod = g.dom), skeleton.arrows C :=
begin
  induction f, rcases f with ⟨X,Y₁,f⟩,
  induction g, rcases g with ⟨Y₂,Z,g⟩,
  -- show ⟦Y₁⟧ = ⟦Y₂⟧ → skeleton.arrows C,
  intro e,
  have y : Y₁ ≅ Y₂, apply classical.choice, apply quotient.exact' e,
  refine (skeleton.arrows.mk (f ≫ y.hom ≫ g)),

  intros,
end


end category_theory