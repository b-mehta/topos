/-
Copyright (c) 2020 E.W.Ayers, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers, Bhavik Mehta
-/

import category_theory.limits.limits
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.monad.limits
import category_theory.monad.adjunction
import category_theory.limits.shapes.equalizers
universes u₁ u₂ v

namespace category_theory

open limits
open category_theory
variables {C : Type u₁} [category.{v} C]
variables {A B : C}

structure reflexive_pair (f g : A ⟶ B) :=
(back : B ⟶ A)
(back_f : back ≫ f = 𝟙 B)
(back_g : back ≫ g = 𝟙 B)

structure split_coequalizer  (f g : A ⟶ B) :=
(cf : cofork f g)
(t : B ⟶ A)
(s : cf.X ⟶ B)
(p1 : s ≫ cf.π = 𝟙 _)
(p2 : t ≫ g = 𝟙 B)
(p3 : t ≫ f = cf.π ≫ s)

section
open category_theory.limits.walking_parallel_pair category_theory.limits.walking_parallel_pair_hom

def colimit_of_splits {F : walking_parallel_pair.{v} ⥤ C} (c : cocone F) (s : c.X ⟶ F.obj one) (t : F.obj one ⟶ F.obj zero)
  (hs : s ≫ c.ι.app _ = 𝟙 (c.X)) (gt : t ≫ F.map right = 𝟙 (F.obj one)) (ftsh : t ≫ F.map left = c.ι.app one ≫ s) :
  is_colimit c :=
{ desc := λ s', s ≫ s'.ι.app one,
  fac' := λ s',
  begin
    have: c.ι.app one ≫ s ≫ s'.ι.app one = s'.ι.app one,
      rw [← reassoc_of ftsh, s'.w left, ← s'.w right, reassoc_of gt],
    rintro ⟨j⟩, rw ← c.w left, slice_lhs 2 4 {rw this}, apply s'.w,
    assumption
  end,
  uniq' := λ s' m J,
  begin
    rw [← J one, reassoc_of hs]
  end }
end

def split_coequalizer_is_coequalizer' {f g : A ⟶ B} (sc : split_coequalizer f g) : is_colimit (cofork.of_π sc.cf.π sc.cf.condition) :=
colimit_of_splits _ sc.s sc.t sc.p1 sc.p2 sc.p3

variable (C)
def has_reflexive_coequalizers := Π ⦃A B : C⦄ ⦃f g : A ⟶ B⦄, reflexive_pair f g → has_colimit (parallel_pair f g)
variable {C}

variables {D : Type u₂} [category.{v} D]

def reflexive_coeq_of_equiv (F : C ⥤ D) [is_equivalence F] (hrc : has_reflexive_coequalizers C) : has_reflexive_coequalizers D :=
begin
  intros X Y f g r,
  apply adjunction.has_colimit_of_comp_equivalence _ F.inv,
  have : limits.has_colimit (limits.parallel_pair ((functor.inv F).map f) ((functor.inv F).map g)),
    apply hrc,
    refine ⟨F.inv.map r.back, _, _⟩,
    simp [← F.inv.map_comp, r.back_f],
    simp [← F.inv.map_comp, r.back_g],
  refine @has_colimit_of_iso _ _ _ _ _ _ this (diagram_iso_parallel_pair.{v} (limits.parallel_pair f g ⋙ F.inv)),
end

section algebra
open monad

variables (G : D ⥤ C) [is_right_adjoint G]
abbreviation F := left_adjoint G
abbreviation algebras := monad.algebra (F G ⋙ G)
variable {G}
abbreviation η : 𝟭 C ⟶ F G ⋙ G := is_right_adjoint.adj.unit
abbreviation ε : G ⋙ F G ⟶ 𝟭 D := is_right_adjoint.adj.counit

variable {G}

-- local notation `F` := (left_adjoint G)
-- local notation `CT` := monad.algebra (F ⋙ G)
-- local notation `adjj` := is_right_adjoint.adj G
-- local notation `ε` := (adjunction.counit (is_right_adjoint.adj G)).app

open category
open adjunction

def algebra_pair_reflexive (α : algebras G) : reflexive_pair (((F G).map) α.a) (ε.app ((F G).obj α.A)) :=
{ back := (F G).map (η.app _),
  back_f := by { erw [← functor.map_comp, monad.algebra.unit α], simp },
  back_g := by simp }

def other_adjunctive_coequalizer (α : algebras G) : cofork (G.map ((F G).map α.a)) (G.map (ε.app _)) :=
cofork.of_π α.a α.assoc.symm

def other_adjunctive_coequalizer_split (α : algebras G) : split_coequalizer (G.map ((F G).map α.a)) (G.map (ε.app _)) :=
{ cf := other_adjunctive_coequalizer α,
  t := η.app _,
  s := η.app _,
  p1 := α.unit,
  p2 := right_triangle_components _,
  p3 := (η.naturality _).symm }

-- -- TODO (BM): this is redundant, it's a special case of above
def adjunctive_coequalizer (B : D) : cofork (G.map ((F G).map (G.map (ε.app B)))) (G.map (ε.app _)) :=
cofork.of_π (G.map (ε.app B))
begin
  rw ← G.map_comp, rw ← G.map_comp, congr' 1,
  exact ε.naturality (ε.app B)
end

def adjunctive_coequalizer' (B : D) : cofork (G.map ((F G).map (G.map (ε.app B)))) (G.map (ε.app _)) :=
other_adjunctive_coequalizer ⟨G.obj B, G.map (ε.app B), right_triangle_components _, by { erw [← G.map_comp, ← G.map_comp, ← ε.naturality], dsimp, refl }⟩

def adjunctive_coequalizer_split (B : D) : split_coequalizer (G.map ((F G).map (G.map (ε.app B)))) (G.map (ε.app _)) :=
⟨ adjunctive_coequalizer B,
  (adjunction.unit (is_right_adjoint.adj)).app _,
  (adjunction.unit (is_right_adjoint.adj)).app _,
  (is_right_adjoint.adj).right_triangle_components,
  (is_right_adjoint.adj).right_triangle_components,
  ((adjunction.unit (is_right_adjoint.adj)).naturality _).symm⟩

def adjunctive_coequalizer_split' (B : D) : split_coequalizer (G.map ((F G).map (G.map (ε.app B)))) (G.map (ε.app _)) :=
other_adjunctive_coequalizer_split ⟨G.obj B, G.map (ε.app B), right_triangle_components _, by { erw [← G.map_comp, ← G.map_comp, ← ε.naturality], dsimp, refl }⟩

def restrict_equivalence {A : Type u₁} {B : Type u₂} (h : A ≃ B) (p : A → Prop) (q : B → Prop) (sound : ∀ a, p a ↔ q (h a)) : {a // p a} ≃ {b // q b} :=
equiv.subtype_congr h sound

def coeq_equiv {X Y : C} (Z : C) (f g : X ⟶ Y) [has_colimit (parallel_pair f g)] : (coequalizer f g ⟶ Z) ≃ {h : Y ⟶ Z // f ≫ h = g ≫ h} :=
{ to_fun := λ i, ⟨coequalizer.π _ _ ≫ i, coequalizer.condition_assoc f g i⟩,
  inv_fun := λ h, coequalizer.desc h.1 h.2,
  left_inv := by tidy,
  right_inv := by tidy }

def e2_base {α : algebras G} {B : D} : ((F G).obj α.A ⟶ B) ≃ (α.A ⟶ G.obj B) := is_right_adjoint.adj.hom_equiv _ _

def e2_props {α : algebras G} {B : D} (f : (F G).obj α.A ⟶ B) :
  (F G).map α.a ≫ f = ε.app ((F G).obj α.A) ≫ f ↔
  α.a ≫ e2_base.to_fun f = G.map ((F G).map (e2_base.to_fun f)) ≫ G.map (ε.app B) :=
begin
  erw [← G.map_comp, ← hom_equiv_counit, ← hom_equiv_naturality_left, hom_equiv_apply_eq, hom_equiv_counit, counit_naturality],
  convert iff.refl _,
  apply e2_base.left_inv f
end

def e2 (α : algebras G) (B : D) : {f : (F G).obj α.A ⟶ B // (F G).map α.a ≫ f = ε.app ((F G).obj α.A) ≫ f} ≃ {fcheck : α.A ⟶ G.obj B // α.a ≫ fcheck = G.map ((F G).map fcheck) ≫ G.map (ε.app B)} :=
equiv.subtype_congr e2_base e2_props

def e3 (α : algebras G) (B : D) : {fcheck : α.A ⟶ G.obj B // α.a ≫ fcheck = G.map ((F G).map fcheck) ≫ G.map (ε.app B)} ≃ (α ⟶ (monad.comparison G).obj B) :=
{ to_fun := λ f, { f := f.1, h' := f.2.symm },
  inv_fun := λ g, ⟨g.f, g.h.symm⟩,
  left_inv := λ ⟨f, _⟩, by { dsimp, congr },
  right_inv := λ ⟨g, _⟩, by { dsimp, congr } }

/- Assume we have coequalizers for (F a) and (ε F A) for all algebras (A,a). -/
variables (hce : ∀ (α : algebras G), has_colimit (parallel_pair (((F G).map) α.a) (ε.app ((F G).obj α.A))))

def L_obj : algebras G → D :=
λ α, @colimit _ _ _ _ _ (hce α)

def e1 (α : algebras G) (B : D) : (L_obj hce α ⟶ B) ≃ {f : (F G).obj α.A ⟶ B // (F G).map α.a ≫ f = ε.app ((F G).obj α.A) ≫ f} :=
coeq_equiv _ _ _

def Le (α : algebras G) (B : D) : (L_obj hce α ⟶ B) ≃ (α ⟶ (monad.comparison G).obj B) :=
equiv.trans (e1 _ _ _) (equiv.trans (e2 _ _) (e3 _ _))

lemma Lhe (α : algebras G) (B B' : D) (g : B ⟶ B') (h : L_obj hce α ⟶ B) : (Le hce α B') (h ≫ g) = (Le hce α B) h ≫ (monad.comparison G).map g :=
begin
  ext, dunfold Le e1 e2 e3 coeq_equiv, dsimp,
  change (is_right_adjoint.adj.hom_equiv α.A B').to_fun (coequalizer.π ((F G).map α.a) (ε.app ((F G).obj α.A)) ≫ h ≫ g) =
       (is_right_adjoint.adj.hom_equiv α.A B).to_fun (coequalizer.π ((F G).map α.a) (ε.app ((F G).obj α.A)) ≫ h) ≫ G.map g,
  conv_lhs {congr, skip, rw ← assoc},
  apply hom_equiv_naturality_right
end

/-- The left adjoint to the comparison functor. -/
private def L : algebras G ⥤ D := adjunction.left_adjoint_of_equiv (Le hce) (Lhe hce)

/-- Suppose we have coequalizers for (F a) and (ε F A) for all algebras (A,a), then the comparison functor has a left adjoint.
    This is then shown to be an equivalence adjunction in the monadicity theorems.
  -/
def forms_adjoint : L hce ⊣ monad.comparison G := adjunction.adjunction_of_equiv_left (Le hce) (Lhe hce)
def left_adjoint_of_comparison : is_right_adjoint (monad.comparison G) :=
{ left := L hce, adj := forms_adjoint hce }

-- end algebra

-- -- /-- Take a G-split coequalizer `cf` for `f,g : A ⟶ B`, then we have a coequalizer for `f,g` and `G` of this coequalizer is still a colimit.  -/
-- def creates_G_split_coequalizers (G : D ⥤ C) :=
-- Π {A B : D} (f g : A ⟶ B) (cf : split_coequalizer (G.map f) (G.map g)),
-- creates_colimit (parallel_pair f g) G
--   -- Σ (hcl : has_colimit (parallel_pair f g)), is_colimit $ G.map_cocone hcl.cocone

def preserves_reflexive_coequalizers (G : D ⥤ C) :=
Π {A B : D} {f g : A ⟶ B}, reflexive_pair f g → preserves_colimit (parallel_pair f g) G

-- -- def reflects_isomorphisms (G : D ⥤ C) :=
-- -- Π {A B : D} {f : A ⟶ B}, is_iso (G.map f) → is_iso f

-- section creates
-- -- [note] universe is v, the same as the homs in D and C. See the variable decalaration note in cones.lean in mathlib to see why.
-- variables {J : Type v} [𝒥 : small_category J]
-- include 𝒥

-- variables {G : D ⥤ C} [monadic_right_adjoint G]

-- -- omit 𝒥
-- -- lemma monadic_really_creates_limits: creates_limits G :=
-- -- sorry

-- -- include 𝒥

-- -- lemma monadic_creates_colimits_that_monad_preserves (K : J ⥤ D) (ps : preserves_colimit (K ⋙ G) (left_adjoint G ⋙ G)) (ps : preserves_colimit (K ⋙ G) (left_adjoint G ⋙ G ⋙ left_adjoint G ⋙ G)) :
-- --   creates_colimit K G :=
-- -- sorry

-- end creates

-- variables {G : D ⥤ C} [is_right_adjoint G]

def adjoint_to_equivalence {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [unit_iso : is_iso adj.unit] [counit_iso : is_iso adj.counit] :
C ≌ D :=
{ functor := F,
  inverse := G,
  unit_iso := as_iso adj.unit,
  counit_iso := as_iso adj.counit }

def coequalizer_desc_is_iso {X Y Z : C} (f g : X ⟶ Y) [i : has_colimit (parallel_pair f g)] (h : Y ⟶ Z) (w : f ≫ h = g ≫ h) (t : is_colimit (cofork.of_π h w)) :
  is_iso (@coequalizer.desc _ _ _ _ f g i _ h w) :=
begin
  set iso := is_colimit.unique_up_to_iso (colimit.is_colimit _) t,
  have hi: (iso.hom ≫ iso.inv).hom = _, rw iso.hom_inv_id,
  have ih: (iso.inv ≫ iso.hom).hom = _, rw iso.inv_hom_id,
  refine ⟨iso.inv.hom, hi, ih⟩
end

def coeq_fork_is_colimit {X Y : C} (f g : X ⟶ Y) [i : has_colimit (parallel_pair f g)] :
  is_colimit (cofork.of_π (coequalizer.π f g) (coequalizer.condition _ _)) :=
begin
  apply is_colimit.of_iso_colimit (colimit.is_colimit  (parallel_pair f g)),
  apply cocones.ext _ _, refl, rintro ⟨j⟩, erw category.comp_id, rw ← cofork.left_app_one, refl,
  erw category.comp_id, refl
end

def really_preserves_coeq {X Y Z : D} {f g : X ⟶ Y} {h : Y ⟶ Z} (w₁ : f ≫ h = g ≫ h)
  (t : is_colimit (G.map_cocone (cofork.of_π h w₁))) : is_colimit (cofork.of_π (G.map h) (begin rw ← G.map_comp, simp [w₁] end) : cofork (G.map f) (G.map g)) :=
begin
  have q: limits.parallel_pair (G.map f) (G.map g) = limits.parallel_pair f g ⋙ G,
     apply functor.ext _ _, rintro ⟨j⟩; refl, intros, cases f_1, simp, simp, simp, dsimp, simp,
  convert t,
  dsimp [functor.map_cocone, cocones.functoriality, limits.cofork.of_π], congr,
  assumption, assumption,
  refine function.hfunext rfl _, intros, tactic.case_bash, simp, simp, apply proof_irrel_heq
end

def unit_iso
  (hrc : has_reflexive_coequalizers D)
  (prc : preserves_reflexive_coequalizers G)
  (ri : reflects_isomorphisms G) :
  is_iso (forms_adjoint (λ α, hrc (algebra_pair_reflexive α)) : _ ⊣ monad.comparison G).unit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intro α,
  -- set F := left_adjoint G,
  -- set ε := is_right_adjoint.adj.counit,
  dsimp [forms_adjoint, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv, adjunction.left_adjoint_of_equiv, L_obj],
  set hce := (λ (β : monad.algebra (F G ⋙ G)), hrc (algebra_pair_reflexive β)),
  letI: has_colimit (parallel_pair ((F G).map α.a) (ε.app ((F G).obj α.A))) := hce _,
  change is_iso ((Le hce α (coequalizer ((F G).map α.a) (ε.app ((F G).obj α.A)))).to_fun (𝟙 _)),
  dunfold Le e1 e2 e3 equiv.trans coeq_equiv,
  dsimp,
  apply @monad.algebra_iso_of_iso _ _ _ _ _ _ _ _,

  dsimp [equiv.subtype_congr, e2_base],
  erw category.comp_id,
  change is_iso
    ((is_right_adjoint.adj.hom_equiv α.A (coequalizer ((F G).map α.a) (ε.app ((F G).obj α.A)))).to_fun
       (coequalizer.π ((F G).map α.a) (ε.app ((F G).obj α.A)))),
  let t := coequalizer.π ((F G).map α.a) (ε.app ((F G).obj α.A)),
  let ι := (is_right_adjoint.adj.hom_equiv _ _).to_fun t,
  show is_iso ι,
  let q: is_colimit (cofork.of_π t _) := coeq_fork_is_colimit ((F G).map α.a) (ε.app ((F G).obj α.A)),
  have z := (prc (algebra_pair_reflexive _)).preserves,
  let m := really_preserves_coeq _ (z q),
  let alp : limits.is_colimit (limits.cofork.of_π α.a _) := split_coequalizer_is_coequalizer' (other_adjunctive_coequalizer_split α),
  let ι' := (is_colimit.unique_up_to_iso alp m).hom,
  have: ι = ι'.hom,
  { apply is_colimit.hom_ext alp,
    apply cofork.coequalizer_ext, show α.a ≫ ι = _ ≫ ((is_colimit.unique_up_to_iso alp m).hom).hom,
    dunfold is_colimit.unique_up_to_iso is_colimit.desc_cocone_morphism, dsimp,
    show α.a ≫ ι = (limits.cofork.of_π α.a _).ι.app limits.walking_parallel_pair.one ≫ _,
    erw alp.fac,
    dsimp,
    have: ι = (is_right_adjoint.adj).unit.app α.A ≫ G.map t, apply (is_right_adjoint.adj).hom_equiv_unit,
    rw this,
    slice_lhs 1 2 {erw (is_right_adjoint.adj).unit.naturality α.a},
    change ((is_right_adjoint.adj).unit.app (G.obj ((F G).obj α.A)) ≫ G.map ((F G).map α.a)) ≫ G.map t = G.map t,

    slice_lhs 2 3 {rw ← G.map_comp, rw coequalizer.condition ((F G).map α.a) (ε.app ((F G).obj α.A)), rw G.map_comp},
    slice_lhs 1 2 {rw (is_right_adjoint.adj).right_triangle_components},
    erw category.id_comp },
  rw this,
  let i : is_iso ι',
    apply_instance,
  refine ⟨i.inv.hom, _, _⟩,
  show (ι' ≫ is_iso.inv ι').hom = _, rw is_iso.hom_inv_id, refl,
  show (is_iso.inv ι' ≫ ι').hom = _, rw is_iso.inv_hom_id, refl,
end

def really_preserves_coeq' {X Y Z : D} {f g : X ⟶ Y} {h : Y ⟶ Z} (w₁ : f ≫ h = g ≫ h)
  (t : is_colimit (cofork.of_π (G.map h) (begin rw ← G.map_comp, simp [w₁] end) : cofork (G.map f) (G.map g))) :
  is_colimit (G.map_cocone (cofork.of_π h w₁)) :=
begin
  have q: limits.parallel_pair (G.map f) (G.map g) = limits.parallel_pair f g ⋙ G,
    apply functor.ext _ _, rintro ⟨j⟩; refl, intros, cases f_1, simp, simp, simp, dsimp, simp,
  convert t,
  rw ← q,
  dsimp [functor.map_cocone, cocones.functoriality, limits.cofork.of_π], congr,
  exact q.symm, exact q.symm,
  refine function.hfunext rfl _, intros, tactic.case_bash, simp, simp, apply proof_irrel_heq
end

def ε_B_is_coequalizer (B : D)
  (hrc : has_reflexive_coequalizers D)
  (prc : preserves_reflexive_coequalizers G)
  (ri : reflects_isomorphisms G) :
  is_colimit (cofork.of_π (ε.app B : (F G).obj (G.obj B) ⟶ B) (ε.naturality (ε.app B))) :=
begin
  let my_cocone := cofork.of_π (ε.app B : (F G).obj (G.obj B) ⟶ B) (ε.naturality (ε.app B)),
  have rp : reflexive_pair ((F G).map (G.map (ε.app B))) (ε.app ((G ⋙ is_right_adjoint.left G).obj B)),
  { refine ⟨(F G).map (η.app _), _, _⟩,
    { rw ← (F G).map_comp,
      change (F G).map (η.app (G.obj B) ≫ G.map (ε.app B)) = 𝟙 ((F G).obj (G.obj B)),
      rw is_right_adjoint.adj.right_triangle_components,
      apply (F G).map_id },
    { apply is_right_adjoint.adj.left_triangle_components }
  },
  haveI: has_colimit (parallel_pair ((F G).map (G.map (ε.app B))) (ε.app ((G ⋙ F G).obj B))) := hrc rp,
  set t := colimit.cocone (parallel_pair ((F G).map (G.map (ε.app B))) (ε.app ((G ⋙ F G).obj B))),

  set LKB := coequalizer ((F G).map (G.map (ε.app B))) (ε.app ((G ⋙ F G).obj B)),
  set ι : (F G).obj (G.obj B) ⟶ LKB := coequalizer.π ((F G).map (G.map (ε.app B))) (ε.app ((G ⋙ F G).obj B)),
  set ζ: t ⟶ my_cocone := is_colimit.desc_cocone_morphism (colimit.is_colimit _) my_cocone,
  suffices: is_iso ζ,
    resetI,
    apply is_colimit.of_iso_colimit (colimit.is_colimit _) (as_iso ζ),
  suffices: is_iso ((cocones.functoriality _ G).map ζ),
  { resetI, apply is_iso_of_reflects_iso ζ (cocones.functoriality _ G) },
  have maptco: is_colimit (G.map_cocone t),
    apply (prc rp).preserves,
    apply colimit.is_colimit,
  have mapmyco: is_colimit (G.map_cocone my_cocone),
    apply really_preserves_coeq',
    apply split_coequalizer_is_coequalizer' (adjunctive_coequalizer_split _),
  let z := is_colimit.unique_up_to_iso maptco mapmyco,
  have: (cocones.functoriality _ G).map ζ = z.hom,
    apply is_colimit.uniq_cocone_morphism maptco,
  rw this, apply_instance,
end

def counit_iso
  (hrc : has_reflexive_coequalizers D)
  (prc : preserves_reflexive_coequalizers G)
  (ri : reflects_isomorphisms G) :
  is_iso (forms_adjoint (λ α, hrc (algebra_pair_reflexive α)) : _ ⊣ monad.comparison G).counit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _, intro B,
  set F := left_adjoint G,
  dsimp [forms_adjoint, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv, Le, equiv.trans, e1, e2, e3, coeq_equiv, monad.comparison],
  apply coequalizer_desc_is_iso,
  convert ε_B_is_coequalizer B hrc (λ _ _ _ _, prc) ri,
  change ((is_right_adjoint.adj).hom_equiv (G.obj B) B).inv_fun (𝟙 (G.obj B)) = _,
  have: ((is_right_adjoint.adj).hom_equiv (G.obj B) B).inv_fun (𝟙 (G.obj B)) = _ := (is_right_adjoint.adj).hom_equiv_counit,
  rw this, rw functor.map_id, rw category.id_comp
end

def reflexive_monadicity_theorem
  (hrc : has_reflexive_coequalizers D)
  (prc : preserves_reflexive_coequalizers G)
  (ri : reflects_isomorphisms G) :
  is_equivalence (monad.comparison G) :=
begin
  apply is_equivalence.of_equivalence_inverse (adjoint_to_equivalence (forms_adjoint (λ α, hrc (algebra_pair_reflexive α)))),
  { apply unit_iso _ (λ _ _ _ _, prc) ri },
  { apply counit_iso _ (λ _ _ _ _, prc) ri }
end

-- /- Plan:
--    call the comparison functor K
--    1. for each algebra, (Fα,εFA) is reflexive so we have a coequalizer for it.
--    2. so we have a functor `L(A,α) := coeq(Fα,εFA)` as in left_adjoint_of_comparison
--    3. K L (A,a) ≅ (A,a): Show that `Gπ : G F A → G L A` and `a : G F A → A` both coequalize `(GFa,GεFA)`. ++ a commuting diagram for the algebras.
--    4. L K Y ≅ Y uses the fact that G preserves the coequalizer of (F ε Y, ε F G Y), so `G L (GY,GεY) ≅ G Y` and then G reflects isos.
--  -/



-- -- def precise_monadicity : creates_G_split_coequalizers G → is_equivalence (monad.comparison G) :=
-- -- sorry

-- -- def monadic_creates_split_coequalizers : is_equivalence (monad.comparison G) → creates_G_split_coequalizers G :=
-- -- begin
-- --   intro t,
-- --   rw creates_G_split_coequalizers,
-- --   intros,
-- --   apply (monadic_creates_colimits_that_monad_preserves _).creates_colimit,
-- --   exact ⟨t⟩,
-- --   refine ⟨_⟩,
-- --   intro K,

-- -- end



-- end category_theory

end algebra
end category_theory
