/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.limits
import category_theory.limits.preserves

open category_theory category_theory.limits

namespace category_theory

universes v u₁ u₂ u₃

variables {C : Type u₁} [𝒞 : category.{v} C]
include 𝒞

section isomorphisms

variables {J : Type v} [small_category J] {K : J ⥤ C}

/--
Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
def cone_iso_of_hom_iso {K : J ⥤ C} {c d : cone K} (f : c ⟶ d) [i : is_iso f.hom] :
  is_iso f :=
{ inv :=
  { hom := i.inv,
    w' := λ j, (as_iso f.hom).inv_comp_eq.2 (f.w j).symm } }

variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒟

/--
Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class reflects_isomorphisms (F : C ⥤ D) :=
(reflects : Π {A B : C} (f : A ⟶ B) [is_iso (F.map f)], is_iso f)

-- TODO: should cones.functoriality take K as an explicit argument? I think so...
/--
If `F` reflects isomorphisms, then `cones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [reflects_isomorphisms F] (K : J ⥤ C) :
  reflects_isomorphisms (@cones.functoriality _ _ _ _ K _ _ F) :=
begin
  constructor,
  introsI,
  haveI : is_iso (F.map f.hom) := (cones.forget (K ⋙ F)).map_is_iso ((cones.functoriality F).map f),
  haveI := reflects_isomorphisms.reflects F f.hom,
  apply cone_iso_of_hom_iso
end

-- Having this as an instance seems to break resolution, so let's not.
/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
def is_iso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D)
  [h : reflects_isomorphisms F] [is_iso (F.map f)] :
  is_iso f :=
reflects_isomorphisms.reflects F f

end isomorphisms

variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒟

variables {J : Type v} [small_category J] {K : J ⥤ C}

/--
Note this definition is really only useful when `c` is a limit already.
For a cone `c` for `K ⋙ F`, give a cone for `K` which is a lift of `c`,
i.e. the image of it under `F` is (iso) to `c`.
-/
structure lift_cone (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) :=
(above_cone : cone K)
(above_hits_original : F.map_cone above_cone ≅ c)

/--
Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone above, and further that `F` reflects
limits for `K`.

Note this is equivalent to Riehl's definition - the missing part here appears to
be that the lifted cone is not a limit, but `reflects` guarantees that it is.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`
-/
class creates_limit (K : J ⥤ C) (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(lifts : Π (c : cone (K ⋙ F)), is_limit c → lift_cone K F c)
(reflects : reflects_limit K F)

class creates_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(creates_limit : Π {K : J ⥤ C}, creates_limit K F)

class creates_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(creates_limits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI creates_limits_of_shape J F)

-- TODO: reflects iso is equivalent to reflecting limits of shape 1

/--
A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure lifts_to_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) :=
(lifted : lift_cone K F c)
(makes_limit : is_limit lifted.above_cone)

/--
If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
-/
def creates_limit_of_reflects_iso {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F]
  (h : Π c t, lifts_to_limit K F c t) :
  creates_limit K F :=
{ lifts := λ c t, (h c t).lifted,
  reflects :=
  { reflects := λ (d : cone K) (hd : is_limit (F.map_cone d)),
    begin
      let d' : cone K := (h (F.map_cone d) hd).lifted.above_cone,
      let hd'₁ : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).lifted.above_hits_original,
      let hd'₂ : is_limit d' := (h (F.map_cone d) hd).makes_limit,
      let f : d ⟶ d' := hd'₂.lift_cone_morphism d,
      have: F.map_cone_morphism f = hd'₁.inv := (hd.of_iso_limit hd'₁.symm).uniq_cone_morphism,
      have: @is_iso _ cone.category _ _ (functor.map_cone_morphism F f),
        rw this, apply_instance,
      haveI: is_iso ((cones.functoriality F).map f) := this,
      haveI := is_iso_of_reflects_iso f (cones.functoriality F),
      exact is_limit.of_iso_limit hd'₂ (as_iso f).symm,
    end } }

end category_theory