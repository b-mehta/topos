import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import category_theory.monad.adjunction
import adjunction
import binary_products
import cartesian_closed

universes v₁ v₂ u₁ u₂

namespace category_theory

open limits category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D] (i : D ⥤ C)

structure in_subcategory [ir : is_right_adjoint i] (A : C) :=
( returning : is_iso (ir.adj.unit.app A) )

def containment_iso (A : C) [ir : is_right_adjoint i] (h : in_subcategory i A) : A ≅ i.obj ((left_adjoint i).obj A) :=
begin
  haveI := h.returning,
  exact as_iso (ir.adj.unit.app A),
end

variables [has_finite_products.{v₁} C] [has_finite_products.{v₁} D] [is_cartesian_closed C]

class exponential_ideal extends reflective i :=
( strength (A B : C) (h : in_subcategory i B) : in_subcategory i (B ^^ A))

variable [exponential_ideal i]

def b1 (A B : C) (C' : D) : (A ⨯ B ⟶ i.obj C') ≃ (B ⨯ A ⟶ i.obj C') := sorry
def b2 (A B : C) (C' : D) : (B ⨯ A ⟶ i.obj C') ≃ (A ⟶ (i.obj C') ^^ B) := sorry
def b3 (A B : C) (C' : D) : (A ⟶ (i.obj C') ^^ B) ≃ (A ⟶ i.obj ((left_adjoint i).obj (i.obj C' ^^ B))) := sorry
def b4 (A B : C) (C' : D) : (A ⟶ i.obj ((left_adjoint i).obj (i.obj C' ^^ B))) ≃ ((left_adjoint i).obj A ⟶ (left_adjoint i).obj (i.obj C' ^^ B)) := sorry
def b5 (A B : C) (C' : D) : ((left_adjoint i).obj A ⟶ (left_adjoint i).obj (i.obj C' ^^ B)) ≃ (i.obj ((left_adjoint i).obj A) ⟶ i.obj ((left_adjoint i).obj (i.obj C' ^^ B))) := sorry
def b6 (A B : C) (C' : D) : (i.obj ((left_adjoint i).obj A) ⟶ i.obj ((left_adjoint i).obj (i.obj C' ^^ B))) ≃ (i.obj ((left_adjoint i).obj A) ⟶ i.obj C' ^^ B) := sorry
def b7 (A B : C) (C' : D) : (i.obj ((left_adjoint i).obj A) ⟶ i.obj C' ^^ B) ≃ (B ⨯ i.obj ((left_adjoint i).obj A) ⟶ i.obj C') := sorry

def bijection (A B : C) (C' : D) : (A ⨯ B ⟶ i.obj C') ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ C') :=
begin
end

def preserves_pair_of_exponential_ideal (A B : C) : preserves_limit (pair.{v₁} A B) (is_right_adjoint.left i) :=
begin
  apply preserves_binary_prod_of_prod_comparison_iso (is_right_adjoint.left i) _ _,

end

def preserves_binary_products_of_exponential_ideal : preserves_limits_of_shape (discrete walking_pair) (is_right_adjoint.left i) :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (diagram_iso_pair K).symm,
    apply preserves_pair_of_exponential_ideal,
  end }
end category_theory
