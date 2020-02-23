import category_theory.limits.shapes.binary_products
import category_theory.adjunction
import adjunction
import tactic

universes u v

namespace category_theory

open limits category
section
variables {C : Type u} [𝒞 : category.{v} C] [@has_binary_products.{v} C 𝒞] {A X Y : C}
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

lemma prodinl_comp (X Y : C) : prodinl Y ⋙ prodinl X ≅ prodinl (X⨯Y) :=
{ hom := { app := λ T, begin apply (prod.associator _ _ _).inv end,
           naturality' := begin intros, simp only [functor.comp_map], dunfold prodinl, dsimp, ext, tactic.case_bash, simp, conv_rhs {erw comp_id}, work_on_goal 0 { dsimp at *, ext1, simp at * }, work_on_goal 1 { dsimp at *, simp at * }, tactic.case_bash, work_on_goal 0 { dsimp at *, simp at *, dsimp at *, simp at * }, dsimp, simp, dsimp, simp end}, -- I have zero idea why this works but it does
  inv := { app := λ T, begin apply (prod.associator _ _ _).hom end,
           naturality' := begin intros, dunfold prodinl, simp, ext, tactic.case_bash, work_on_goal 0 { dsimp at *, simp at *, dsimp at *, simp at * }, dsimp at *, simp at *, ext1, simp at *, dsimp at *, tactic.case_bash, work_on_goal 0 { dsimp at *, simp at *, dsimp at *, simp at * }, dsimp at *, simp at * end},
  hom_inv_id' := begin dsimp at *, ext1, dsimp at *, ext1, dsimp at *, ext1, simp at *, tactic.case_bash, simp, erw limit.lift_π, simp, erw limit.lift_π, simp at *, dsimp at *, ext1, simp at *, tactic.case_bash, simp, tidy? end,
  inv_hom_id' := begin tidy?, tactic.case_bash, tidy?, tactic.case_bash, simp, dsimp, simp  end
}
end

class exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] (X : C) :=
(exponentiable : is_left_adjoint (prodinl X))

def binary_product_exponentiable {C : Type u} [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] {X Y : C}
  (hX : exponentiable X) (hY : exponentiable Y) :
  exponentiable (limits.prod X Y) :=
{ exponentiable :=
  { right := hX.exponentiable.right ⋙ hY.exponentiable.right,
    adj := adjunction_of_nat_iso_left (adjunction.comp _ _ hY.exponentiable.adj hX.exponentiable.adj) (prodinl_comp _ _) } }

-- [todo] doesn't this need to be natural in X too?
class is_cartesian_closed (C : Type u) [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] :=
(cart_closed : Π (X : C), exponentiable X)

-- [todo] maybe an explicit definition?
-- class is_cc (C : Type u) [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] :=
-- (exp : Cᵒᵖ × C ⥤ C)
-- (ev : Π {X Y} : Y ⨯ exp X Y ⟶ X)
-- (coev : Π {X Y} : X ⟶ exp (Y ⨯ X) Y)
-- ...

end category_theory
