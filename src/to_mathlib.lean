/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/

import category_theory.epi_mono
import category_theory.limits.shapes.binary_products

/-! # Stuff that should be in mathlib -/
namespace category_theory

universes v₁ u₁
variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

lemma mono_comp_of_mono {X Y Z : C}
  (m : X ⟶ Y) (m' : Y ⟶ Z) (hm : mono m) (hm' : mono m') : mono (m ≫ m') :=
⟨λ Z f g w,
  have f ≫ m = g ≫ m := (cancel_mono m').mp (by simp only [category.assoc]; exact w),
  (cancel_mono m).mp this⟩

lemma epi_comp_of_epi {X Y Z : C}
  (e : X ⟶ Y) (e' : Y ⟶ Z) (he : epi e) (he' : epi e') : epi (e ≫ e') :=
⟨λ Z f g w,
  have e' ≫ f = e' ≫ g := (cancel_epi e).mp (by simp only [category.assoc] at w; exact w),
  (cancel_epi e').mp this⟩

open category limits

variables [has_binary_products.{v₁} C] {X Y A B : C}

@[simp] lemma prod_left_def : limit.π (pair X Y) walking_pair.left = limits.prod.fst := rfl
@[simp] lemma prod_right_def : limit.π (pair X Y) walking_pair.right = limits.prod.snd := rfl

lemma prod.hom_ext {a b : A ⟶ X ⨯ Y} (h1 : a ≫ limits.prod.fst = b ≫ limits.prod.fst) (h2 : a ≫ limits.prod.snd = b ≫ limits.prod.snd) : a = b :=
begin
  apply limit.hom_ext,
  rintros (_ | _),
  simp, assumption,
  simp, assumption,
end

lemma prod_map_comm (f : A ⟶ B) (g : X ⟶ Y) : limits.prod.map (𝟙 _) f ≫ limits.prod.map g (𝟙 _) = limits.prod.map g (𝟙 _) ≫ limits.prod.map (𝟙 _) f :=
begin
  apply prod.hom_ext, simp, erw id_comp, erw comp_id, simp, erw id_comp, erw comp_id
end

end category_theory
