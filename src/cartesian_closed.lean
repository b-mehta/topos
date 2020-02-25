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

variables {C : Type u} [𝒞 : category.{v} C] [has_binary_products.{v} C] {X X' Y Y' Z A B : C} [exponentiable A]
include 𝒞

/-- This is (-)^A -/
def exp.functor (A : C) [exponentiable A] : C ⥤ C :=
(exponentiable.exponentiable A).right

def exp.adjunction : (prodinl A) ⊣ (exp.functor A) :=
(exponentiable.exponentiable A).adj

def ev.nat_trans (A : C) [exponentiable A] : (exp.functor A) ⋙ prodinl A ⟶ 𝟭 C :=
exp.adjunction.counit

def coev.nat_trans (A : C) [exponentiable A] : 𝟭 C ⟶ prodinl A ⋙ (exp.functor A) :=
exp.adjunction.unit

/-- `B ^ A` or `B ⇐ A` -/
def exp (B : C) (A : C) [exponentiable A] : C := (exp.functor A).obj B

infixl `⇐`:100 := exp

-- [todo] rename as 'post compose' or similar?
def post (A : C) [exponentiable A] {X Y : C} (f : X ⟶ Y) : X⇐A ⟶ Y⇐A :=
(exp.functor A).map f

def ev : A ⨯ B⇐A ⟶ B :=
(ev.nat_trans A).app B

def coev : B ⟶ (A⨯B)⇐A :=
(coev.nat_trans A).app B

@[simp] lemma ev_coev : limits.prod.map (𝟙 A) coev ≫ ev = 𝟙 (A⨯B) :=
(@adjunction.left_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

@[simp] lemma coev_ev : coev ≫ post _ ev = 𝟙 (B⇐A) :=
(@adjunction.right_triangle_components C _ C _ (prodinl A) (exp.functor A) exp.adjunction B)

lemma coev_nat {f : X ⟶ Y} : f ≫ coev = coev ≫ post _ (limits.prod.map (𝟙 A) f) :=
(coev.nat_trans A).naturality f

lemma ev_nat {f : X ⟶ Y} : limits.prod.map (𝟙 A) (post _ f) ≫ ev = ev ≫ f :=
(ev.nat_trans A).naturality f

def exp_transpose : (A ⨯ Y ⟶ X) ≃ (Y ⟶ X ⇐ A) :=
exp.adjunction.hom_equiv _ _

lemma exp_transpose_natural_left  (f : X ⟶ X') (g : A ⨯ X' ⟶ Y) :
  exp_transpose.to_fun ((prodinl A).map f ≫ g) = f ≫ exp_transpose.to_fun g :=
adjunction.hom_equiv_naturality_left _ _ _

lemma exp_transpose_natural_right (f : A ⨯ X ⟶ Y) (g : Y ⟶ Y') :
  exp_transpose.to_fun (f ≫ g) = exp_transpose.to_fun f ≫ post _ g :=
adjunction.hom_equiv_naturality_right _ _ _

lemma exp_transpose_natural_right_symm  (f : X ⟶ Y ⇐ A) (g : Y ⟶ Y') :
  exp_transpose.inv_fun (f ≫ post A g) = exp_transpose.inv_fun f ≫ g :=
adjunction.hom_equiv_naturality_right_symm _ _ _

lemma exp_transpose_natural_left_symm  (f : X ⟶ X') (g : X' ⟶ Y ⇐ A) :
  exp_transpose.inv_fun (f ≫ g) = (prodinl A).map f ≫ exp_transpose.inv_fun g :=
adjunction.hom_equiv_naturality_left_symm _ _ _

-- [todo] exp X 1 ≅ X
variable [has_terminal.{v} C]

@[reducible]
def point_at_hom (f : A ⟶ Y) : ⊤_C ⟶ (Y ⇐ A) :=
exp_transpose.to_fun (limits.prod.fst ≫ f)

def pre (X : C) [exponentiable B] {f : B ⟶ A} : X⇐A ⟶ X⇐B :=
coev ≫ post B (limits.prod.map f (𝟙 _) ≫ ev)

end category_theory