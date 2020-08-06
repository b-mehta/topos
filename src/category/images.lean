import category_theory.limits.shapes.images

universes v u

open category_theory category_theory.limits

namespace category_theory.limits

variables {C : Type u} [category.{v} C] [has_strong_epi_mono_factorisations.{v} C]

variables {X Y : C} (f : X ⟶ Y)

@[simps]
def unique_factorise (I' : C) (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e] [mono m] :
  I' ≅ image f :=
{ hom := {strong_epi_mono_factorisation . I := I', m := m, e := e}.to_mono_is_image.lift _,
  inv := image.lift {strong_epi_mono_factorisation . I := I', m := m, e := e}.to_mono_factorisation,
  hom_inv_id' := by erw [← cancel_mono m, category.assoc, category.id_comp, image.lift_fac, is_image.lift_fac],
  inv_hom_id' := by erw [← cancel_mono (image.ι f), category.id_comp, category.assoc, is_image.lift_fac, image.lift_fac] }

lemma unique_factorise_hom_comp_image (I' : C) (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e] [mono m] :
  (unique_factorise f I' e m comm).hom ≫ image.ι f = m :=
is_image.lift_fac _ _

lemma unique_factorise_inv_comp_mono (I' : C) (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e] [mono m] :
  (unique_factorise f I' e m comm).inv ≫ m = image.ι f :=
is_image.lift_fac _ _

end category_theory.limits