import category_theory.monad
/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

/-! # Kleisli category on a monad
TODO(WN): reference a book or the notes -/
namespace category_theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

def kleisli (T : C ⥤ C) [monad.{v} T] := C

instance kleisli.category (T : C ⥤ C) [monad.{v} T] : category (kleisli T) :=
{ hom  := λ (X Y : C), X ⟶ T.obj Y,
  id   := λ X, (η_ T).app X,
  comp := λ X Y Z f g, f ≫ T.map g ≫ (μ_ T).app Z,

  id_comp' := λ X Y f, by simp [←category.assoc, ←nat_trans.naturality (η_ T) f, monad.left_unit'],
  comp_id' := λ X Y f, by simp only [category.comp_id, monad.right_unit ],
  assoc'   := λ W X Y Z f g h, begin
    simp only [functor.map_comp, category.assoc],
    congr' 2, rw monad.assoc T Z,
    conv_rhs { erw [←category.assoc, nat_trans.naturality (μ_ T) h,
                    category.assoc] } -- TODO(WN): assoc_rw pls
  end }

namespace kleisli

variables (T : C ⥤ C) [monad.{v} T]

-- TODO(WN): what to call these functors (F_T and G_T)?
@[simps] def F_T : C ⥤ kleisli T :=
{ obj       := λ X, X,
  map       := λ X Y f, by dunfold has_hom.hom; exact f ≫ (η_ T).app Y,
  map_id'   := λ X, by simpa only [category.id_comp],
  map_comp' := λ X Y Z f g, begin
    dunfold category_struct.comp, dsimp,
    simpa only [monad.right_unit, category.comp_id,
                 functor.map_comp, category.assoc,
                 ←nat_trans.naturality (η_ T) g] end }

@[simps] def G_T : kleisli T ⥤ C :=
{ obj       := λ X, T.obj X,
  map       := λ X Y f, T.map f ≫ (μ_ T).app Y,
  map_id'   := λ X, by simp only [category_struct.id, monad.right_unit],
  map_comp' := λ X Y Z f g, begin
    dunfold category_struct.comp, dsimp,
    simp only [monad.assoc T Z, functor.map_comp, category.assoc],
    congr' 1,
    erw [←category.assoc, nat_trans.naturality (μ_ T) g, category.assoc],
  end }

theorem F_T_G_T_eq_T : F_T T ⋙ G_T T = T :=
begin
  apply functor.ext,
  { intros X Y f,
    show T.map (f ≫ (η_ T).app Y) ≫ (μ_ T).app Y = _,
    simp only [category.comp_id, category.id_comp,
               eq_to_hom_refl, monad.right_unit,
               category.assoc, functor.map_comp] },
  { intro X, refl }
end

/- The Kleisli adjunction which gives rise to the monad (T, η_ T, μ_ T). -/
def adj : F_T T ⊣ G_T T :=
adjunction.mk_of_unit_counit
{ unit := by rw [F_T_G_T_eq_T]; exact η_ T,
  counit :=
    { app := λ X, 𝟙 (T.obj X),
      naturality' := λ X Y f, begin
        dunfold category_struct.comp, dsimp,
        simp only [category.comp_id, category.id_comp, category.assoc,
                   functor.map_id, monad.left_unit] end },
  left_triangle' := begin
    ext X, simp, dunfold category_struct.comp, dsimp,
    simp [category_struct.id],
    congr, exact F_T_G_T_eq_T T,
    simp only [eq_mpr_heq]
  end,
  right_triangle' := begin
    sorry
    -- TODO(WN): rw in unit causes horrible heq stuff here, how to get rid?
    -- or alternatively, how to write a reasonable proof using heqs?
  end }

end kleisli
end category_theory
