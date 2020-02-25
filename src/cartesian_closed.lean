import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import adjunction
import tactic

universes u v

namespace category_theory

open limits category
section
variables {C : Type u} [𝒞 : category.{v} C] [@has_binary_products.{v} C 𝒞] {A U V W X Y Z : C}
include 𝒞

@[simp] lemma prod_left_def : limit.π (pair X Y) walking_pair.left = limits.prod.fst := rfl
@[simp] lemma prod_right_def : limit.π (pair X Y) walking_pair.right = limits.prod.snd := rfl

lemma prod.hom_ext {a b : A ⟶ X ⨯ Y} (h1 : a ≫ limits.prod.fst = b ≫ limits.prod.fst) (h2 : a ≫ limits.prod.snd = b ≫ limits.prod.snd) : a = b :=
begin
  apply limit.hom_ext,
  rintros (_ | _),
  simp, assumption,
  simp, assumption,
end

def prodinl (X : C) : C ⥤ C :=
{ obj := λ Y, limits.prod X Y,
  map := λ Y Z f, limits.prod.map (𝟙 X) f,
  map_id' := begin intros, apply prod.hom_ext, simp, exact category.comp_id _ _, simp, exact category.comp_id _ _ end,
  map_comp' := λ U V W f g, begin apply prod.hom_ext, simp, rw [comp_id _ (𝟙 X)], simp end
}

@[simp] lemma prodinl_map_def {f : Y ⟶ Z} : (prodinl X).map f = limits.prod.map (𝟙 X) f := rfl
@[simp] lemma map_fst {f : U ⟶ V} {g : W ⟶ X} : limits.prod.map f g ≫ limits.prod.fst = limits.prod.fst ≫ f := by simp
@[simp] lemma map_snd {f : U ⟶ V} {g : W ⟶ X} : limits.prod.map f g ≫ limits.prod.snd = limits.prod.snd ≫ g := by simp
@[simp] lemma lift_fst {f : W ⟶ X} {g : W ⟶ Y} : limits.prod.lift f g ≫ limits.prod.fst = f := by simp
@[simp] lemma lift_snd {f : W ⟶ X} {g : W ⟶ Y} : limits.prod.lift f g ≫ limits.prod.snd = g := by simp
open category

def prodinl_comp (X Y : C) : prodinl (X ⨯ Y) ≅ prodinl Y ⋙ prodinl X :=
nat_iso.of_components (limits.prod.associator _ _) (
  begin
    intros U V f,
    apply prod.hom_ext,
      simp, dsimp, simp,
    apply prod.hom_ext,
      simp, dsimp, simp,
    simp,
  end
)

end

class exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] (X : C) :=
(exponentiable : is_left_adjoint (prodinl X))

def binary_product_exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) :
  exponentiable (limits.prod X Y) :=
{ exponentiable :=
  { right := hX.exponentiable.right ⋙ hY.exponentiable.right,
    adj := adjunction_of_nat_iso_left (adjunction.comp _ _ hY.exponentiable.adj hX.exponentiable.adj) (prodinl_comp _ _).symm } }

class is_cartesian_closed (C : Type u) [𝒞 : category.{v} C] [@has_binary_products C 𝒞] [@has_terminal C 𝒞] :=
(cart_closed : Π (X : C), exponentiable X)

variables {C : Type u} [𝒞 : category.{v} C] [has_binary_products.{v} C] [has_terminal.{v} C] [is_cartesian_closed C]
include 𝒞

/-- This is (-)^A -/
def exp.functor (A : C) : C ⥤ C :=
(is_cartesian_closed.cart_closed A).exponentiable.right

def exp.adjunction {A : C} : (prodinl A) ⊣ (exp.functor A) :=
(@is_cartesian_closed.cart_closed C 𝒞 _ _ _ A).exponentiable.adj

def ev.nat_trans (A : C) : (exp.functor A) ⋙ prodinl A ⟶ 𝟭 C :=
exp.adjunction.counit

def coev.nat_trans (A : C) : 𝟭 C ⟶ prodinl A ⋙ (exp.functor A) :=
exp.adjunction.unit

/-- `B ^ A` or `A ⇒ B` -/
def exp (A : C) (B : C) : C := (exp.functor A).obj B

def exp_lift {A X Y: C} (f : X ⟶ Y) : exp A X ⟶ exp A Y :=
(exp.functor A).map f

def ev (A B : C) : A ⨯ exp A B ⟶ B :=
(ev.nat_trans A).app B

def coev (A B : C) : B ⟶ exp A (A ⨯ B) :=
(coev.nat_trans A).app B

@[simp] lemma ev_coev (A B : C) : limits.prod.map (𝟙 A) (coev A B) ≫ ev A (A ⨯ B) = 𝟙 (A ⨯ B) :=
(@adjunction.left_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

@[simp] lemma coev_ev (A B : C) : (coev A (exp A B)) ≫ (exp.functor A).map (ev A B) = 𝟙 (exp A B) :=
(@adjunction.right_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

lemma coev_nat {A X Y : C} {f : X ⟶ Y} : f ≫ coev A Y = coev A X ≫ (exp.functor A).map (limits.prod.map (𝟙 A) f) :=
(coev.nat_trans A).naturality f

lemma ev_nat {A X Y : C} {f : X ⟶ Y} :  limits.prod.map (𝟙 A) ((exp.functor A).map f) ≫ ev A Y = ev A X ≫ f :=
(ev.nat_trans A).naturality f

-- [todo] exp 1 X ≅ X
-- BM: I thiiink we can prove this is natural in A, using properties of adjunctions
end category_theory
