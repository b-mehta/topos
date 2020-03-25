/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.binary_products

universes v u

open category_theory category_theory.category category_theory.limits
namespace category_theory

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

@[simps]
def prod_functor : C ⥤ C ⥤ C :=
{ obj := λ X, { obj := λ Y, X ⨯ Y, map := λ Y Z, limits.prod.map (𝟙 X) },
  map := λ Y Z f, { app := λ T, limits.prod.map f (𝟙 T) }}

@[simp] lemma prod_left_def {X Y : C} : limit.π (pair X Y) walking_pair.left = limits.prod.fst := rfl
@[simp] lemma prod_right_def {X Y : C} : limit.π (pair X Y) walking_pair.right = limits.prod.snd := rfl

lemma prod.hom_ext {A X Y : C} {a b : A ⟶ X ⨯ Y} (h1 : a ≫ limits.prod.fst = b ≫ limits.prod.fst) (h2 : a ≫ limits.prod.snd = b ≫ limits.prod.snd) : a = b :=
begin
  apply limit.hom_ext,
  rintros (_ | _),
  simpa,
  simpa
end

lemma prod_map_comm {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
  limits.prod.map (𝟙 _) f ≫ limits.prod.map g (𝟙 _) = limits.prod.map g (𝟙 _) ≫ limits.prod.map (𝟙 _) f :=
begin
  apply prod.hom_ext, simp, erw id_comp, erw comp_id, simp, erw id_comp, erw comp_id
end

lemma prod_functorial {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  limits.prod.map (f ≫ g) (𝟙 W) = limits.prod.map f (𝟙 W) ≫ limits.prod.map g (𝟙 W) :=
begin
  apply prod.hom_ext,
  simp, simp, dsimp, simp
end
lemma prod_functorial' {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  limits.prod.map (𝟙 W) (f ≫ g) = limits.prod.map (𝟙 W) f ≫ limits.prod.map (𝟙 W) g :=
begin
  apply prod.hom_ext,
  simp, dsimp, simp, simp
end

end category_theory