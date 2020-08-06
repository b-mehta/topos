import category_theory.full_subcategory
import category_theory.limits.preserves
import category_theory.reflects_isomorphisms
import category_theory.punit

open category_theory category_theory.category category_theory.limits

universes v u u₂

variables {C : Type u} [category.{v} C]

variables {D : Type u₂} [category.{v} D]

variables (F : C ⥤ D)

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

instance fully_faithful_reflects_colimits [full F] [faithful F] : reflects_colimits F :=
{ reflects_colimits_of_shape := λ J 𝒥₁, by exactI
  { reflects_colimit := λ K,
    { reflects := λ c t,
      is_colimit.mk_cocone_morphism (λ s, (cocones.functoriality K F).preimage (t.desc_cocone_morphism _)) $
      begin
        apply (λ s m, (cocones.functoriality K F).map_injective _),
        rw [functor.image_preimage],
        apply t.uniq_cocone_morphism,
      end } } }

@[simps]
def punit_cone_of_morphism {A B : C} (f : A ⟶ B) : cone (functor.from_punit B) :=
{ X := A,
  π := { app := λ _, f } }

@[simps]
def punit_cocone_of_morphism {A B : C} (f : A ⟶ B) : cocone (functor.from_punit A) :=
{ X := B,
  ι := { app := λ _, f } }

def is_iso_of_is_limit {A B : C} (f : A ⟶ B) (t : is_limit (punit_cone_of_morphism f)) : is_iso f :=
{ inv := t.lift (punit_cone_of_morphism (𝟙 _)),
  inv_hom_id' := t.fac _ punit.star,
  hom_inv_id' := t.hom_ext $ λ j, by { rw [assoc, t.fac _ j], simp } }

def is_iso_of_is_colimit {A B : C} (f : A ⟶ B) (t : is_colimit (punit_cocone_of_morphism f)) : is_iso f :=
{ inv := t.desc (punit_cocone_of_morphism (𝟙 _)),
  hom_inv_id' := t.fac _ punit.star,
  inv_hom_id' := t.hom_ext $ λ j, by { rw t.fac_assoc, dsimp, simp } }

def is_limit_of_is_iso {A B : C} (f : A ⟶ B) [is_iso f] : is_limit (punit_cone_of_morphism f) :=
{ lift := λ s, s.π.app punit.star ≫ inv f,
  uniq' := λ s m w, (as_iso f).eq_comp_inv.2 (w punit.star) }

def is_colimit_of_is_iso {A B : C} (f : A ⟶ B) [is_iso f] : is_colimit (punit_cocone_of_morphism f) :=
{ desc := λ s, inv f ≫ s.ι.app punit.star,
  uniq' := λ s m w, (as_iso f).eq_inv_comp.2 (w punit.star) }

def map_cone_point (B : C) : functor.from_punit B ⋙ F ≅ functor.from_punit (F.obj B) :=
nat_iso.of_components
(λ X, iso.refl _)
(λ X Y f, by { erw F.map_id, refl })

/--
If `F` reflects limits of shape `1`, then `F` reflects isomorphisms.
This is actually an iff.
-/
instance reflects_iso_of_reflects_limits_of_shape_punit [reflects_limits_of_shape (discrete punit) F] :
  reflects_isomorphisms F :=
{ reflects := λ A B f,
  begin
    introsI i,
    apply is_iso_of_is_limit,
    suffices : is_limit (F.map_cone (punit_cone_of_morphism f)),
      apply reflects_limit.reflects this,
    have l := is_limit_of_is_iso (F.map f),
    let t : cone (functor.from_punit B ⋙ F) ≌ cone _ := cones.postcompose_equivalence (map_cone_point F B),
    apply is_limit.of_iso_limit (is_limit.of_right_adjoint t.inverse l),
    refine cones.ext (iso.refl _) _,
    intro j,
    dsimp [map_cone_point],
    simp
  end }

/--
If `F` reflects colimits of shape `1`, then `F` reflects isomorphisms.
This is actually an iff.
-/
instance reflects_iso_of_reflects_colimits_of_shape_punit [reflects_colimits_of_shape (discrete punit) F] :
  reflects_isomorphisms F :=
{ reflects := λ A B f,
  begin
    introsI i,
    apply is_iso_of_is_colimit,
    suffices : is_colimit (F.map_cocone (punit_cocone_of_morphism f)),
      apply reflects_colimit.reflects this,
    have l := is_colimit_of_is_iso (F.map f),
    let t : cocone (functor.from_punit A ⋙ F) ≌ cocone _ := cocones.precompose_equivalence (map_cone_point F A).symm,
    apply is_colimit.of_iso_colimit (is_colimit.of_left_adjoint t.inverse l),
    refine cocones.ext (iso.refl _) _,
    intro j,
    dsimp [map_cone_point],
    simp
  end }

example [reflects_limits F] : reflects_isomorphisms F :=
infer_instance

example [reflects_colimits F] : reflects_isomorphisms F :=
infer_instance