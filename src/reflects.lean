import category_theory.full_subcategory
import category_theory.limits.preserves
import category_theory.reflect_isomorphisms
import category_theory.punit

open category_theory category_theory.category category_theory.limits

universes v u u₂

variables {C : Type u} [category.{v} C]

variables {D : Type u₂} [category.{v} D]

variables (F : C ⥤ D)

instance cones_functoriality_full {J : Type v} [full F] [faithful F] [category J] (K : J ⥤ C) : full (cones.functoriality K F) :=
{ preimage := λ X Y t,
  { hom := F.preimage t.hom,
    w' := λ j, F.map_injective (by simpa using t.w j) } }

instance cones_functoriality_faithful {J : Type v} [faithful F] [category J] (K : J ⥤ C) : faithful (cones.functoriality K F) :=
{ map_injective' := λ X Y f g e, by { ext1, injection e, apply F.map_injective h_1 } }

instance fully_faithful_reflects_limits [full F] [faithful F] : reflects_limits F :=
{ reflects_limits_of_shape := λ J 𝒥₁, by exactI
  { reflects_limit := λ K,
    { reflects := λ c t,
      is_limit.mk_cone_morphism (λ s, (cones.functoriality K F).preimage (t.lift_cone_morphism _)) $
      begin
        apply (λ s m, (cones.functoriality K F).map_injective _),
        rw [functor.image_preimage],
        apply t.uniq_cone_morphism,
      end } } }

@[simps]
def point (A : C) : punit ⥤ C := { obj := λ _, A, map := λ _ _ _, 𝟙 A }

@[simps]
def punit_cone_of_morphism {A B : C} (f : A ⟶ B) : cone (point B) :=
{ X := A,
  π := { app := λ _, f } }

def is_iso_of_is_limit {A B : C} (f : A ⟶ B) (t : is_limit (punit_cone_of_morphism f)) : is_iso f :=
{ inv := t.lift (punit_cone_of_morphism (𝟙 _)),
  inv_hom_id' := t.fac _ punit.star,
  hom_inv_id' :=
  begin
    apply t.hom_ext,
    rintro j,
    rw [assoc, id_comp, t.fac _ j],
    apply comp_id
  end }

def is_limit_of_is_iso {A B : C} (f : A ⟶ B) [is_iso f] : is_limit (punit_cone_of_morphism f) :=
{ lift := λ s, s.π.app punit.star ≫ inv f,
  uniq' := λ s m w, (as_iso f).eq_comp_inv.2 (w punit.star) }

def map_cone_point (B : C) : point B ⋙ F ≅ point (F.obj B) :=
nat_iso.of_components
(λ X, iso.refl _)
(λ X Y f, by { erw F.map_id, refl })

instance reflects_iso_of_reflects_limits_of_shape [reflects_limits_of_shape punit F] : reflects_isomorphisms F :=
{ reflects := λ A B f,
  begin
    introsI i,
    apply is_iso_of_is_limit,
    suffices : is_limit (F.map_cone (punit_cone_of_morphism f)),
      apply reflects_limit.reflects this,
    have l := is_limit_of_is_iso (F.map f),
    let t : cone (point B ⋙ F) ≌ cone _ := cones.postcompose_equivalence (map_cone_point F B),
    apply is_limit.of_iso_limit (is_limit.of_cone_equiv t.inverse l),
    apply cones.ext _ _,
    apply iso.refl _,
    intro j,
    dsimp [map_cone_point],
    simp
  end }