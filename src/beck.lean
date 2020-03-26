/- Author: E.W.Ayers.
   Monadicity theorems. Following chapter 5 of
   http://pi.math.cornell.edu/~dmehrle/notes/partiii/cattheory_partiii_notes.pdf
 -/

import data.fintype.basic
import category_theory.limits.limits
import category_theory.limits.preserves
import category_theory.monad.limits
import category_theory.monad.adjunction
import category_theory.monad
import category_theory.limits.shapes.equalizers
import tactic
import creates
import category_theory.monad.adjunction
universes uc ud v

namespace category_theory

open limits
open category_theory
variables {C : Type uc} [𝒞 : category.{v} C]
include 𝒞
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

@[simp] lemma simp_parallel_zero {f g : A ⟶ B} (t : cofork f g) : t.ι.app walking_parallel_pair.zero = f ≫ t.π :=
begin rw  ← cocone.w t walking_parallel_pair_hom.left, refl end

/-- You can make a coequalizer by finding a π which uniquely factors any other cofork. -/
def is_coeq_lemma' {f g : A ⟶ B} {X : C} (π : B ⟶ X)
  (e : f ≫ π = g ≫ π)
  (factor : ∀ {Y} (c : B ⟶ Y), (f ≫ c = g ≫ c) →  unique {m : X ⟶ Y // c = π ≫ m}) :
is_colimit (cofork.of_π π e) :=
begin
  refine {desc := λ c : cofork f g, _, fac' :=  λ c : cofork f g, _, uniq' :=  λ c : cofork f g, _},
  rcases (factor c.π c.condition) with ⟨⟨⟨k,h1⟩⟩,h2⟩, apply k,
  rcases (factor c.π c.condition) with ⟨⟨⟨k,h1⟩⟩,h2⟩, rintros (_|_),
    change (_ ≫ _) ≫ k = _,  rw category.assoc, rw ← h1, rw simp_parallel_zero,
    change π ≫ k = c.π, dsimp, rw h1,
  rcases (factor c.π c.condition) with ⟨⟨⟨k,h1⟩⟩,h2⟩,
      intros, change m = k,
        have, apply h2 ⟨m,eq.symm (w walking_parallel_pair.one)⟩,
        apply subtype.ext.1 this,
end

/-- You can make a coequalizer by finding a π which uniquely factors any other cofork. -/
def is_coeq_lemma {f g : A ⟶ B} {X : C} (π : B ⟶ X)
  (e : f ≫ π = g ≫ π)
  (factor : ∀ {Y} (c : B ⟶ Y), (f ≫ c = g ≫ c) → unique {m : X ⟶ Y // c = π ≫ m}) :
  has_colimit (parallel_pair f g) :=
{cocone := cofork.of_π π e, is_colimit := is_coeq_lemma' _ _ (λ Y, factor)}

def split_coequalizer_is_coequalizer' {f g : A ⟶ B} (sc : split_coequalizer f g) : is_colimit (cofork.of_π sc.cf.π (cofork.condition _)) :=
begin
  refine is_coeq_lemma' sc.cf.π (cofork.condition _) _,
  { intros, refine ⟨⟨⟨sc.s ≫ c, _⟩⟩,_⟩,
  erw [← category.assoc, ← sc.p3, category.assoc, a, ← category.assoc, sc.p2, category.id_comp],
  rintros ⟨m2,p⟩,
  apply subtype.ext.2,
  change m2 = sc.s ≫ c,
  rw [p, ← category.assoc, sc.p1], dsimp, simp }
end

def split_coequalizer_is_coequalizer {f g : A ⟶ B} (sc : split_coequalizer f g) : has_colimit (parallel_pair f g) :=
begin
  refine is_coeq_lemma sc.cf.π (cofork.condition _) _,
  { intros, refine ⟨⟨⟨sc.s ≫ c,_⟩⟩,_⟩,
  rw [← category.assoc, ← sc.p3, category.assoc, a, ← category.assoc, sc.p2, category.id_comp],
  rintros ⟨m2,p⟩,
  apply subtype.ext.2,
  change m2 = sc.s ≫ c,
  rw [p, ← category.assoc, sc.p1], dsimp, simp }
end

-- open category_theory.limits
open category_theory.limits.walking_parallel_pair category_theory.limits.walking_parallel_pair_hom

def colimit_of_splits {F : walking_parallel_pair.{v} ⥤ C} (c : cocone F) (s : c.X ⟶ F.obj one) (t : F.obj one ⟶ F.obj zero) (hs : s ≫ c.ι.app _ = 𝟙 (c.X)) (gt : t ≫ F.map right = 𝟙 (F.obj one)) (ftsh : t ≫ F.map left = c.ι.app one ≫ s) : is_colimit c :=
{ desc := λ s', s ≫ s'.ι.app one,
  fac' := λ s',
  begin
    have: c.ι.app one ≫ s ≫ s'.ι.app one = s'.ι.app one,
      slice_lhs 1 2 {rw ← ftsh},
      slice_lhs 2 3 {rw s'.ι.naturality left, erw ← s'.ι.naturality right},
      slice_lhs 1 2 {rw gt},
      simp,
    rintro ⟨j⟩, rw ← c.w left, slice_lhs 2 4 {rw this}, apply s'.w,
    assumption
  end,
  uniq' := λ s' m J,
  begin
    rw ← J one, slice_rhs 1 2 {rw hs}, simp
  end
}

variable (C)
def has_reflexive_coequalizers := Π {A B : C} {f g : A ⟶ B}, reflexive_pair f g → has_colimit (parallel_pair f g)
variable {C}

-- [NOTE] homs are in the same universe as C's homs. I'm doing it this way because that's how it's done in cones.lean
variables {D : Type ud} [𝒟 : category.{v} D]
include 𝒟

section algebra
open monad

variables {G : D ⥤ C} [is_right_adjoint G]
local notation `F` := (left_adjoint G)
local notation `CT` := monad.algebra (F ⋙ G)
local notation `adjj` := is_right_adjoint.adj G
local notation `ε` := (adjunction.counit (is_right_adjoint.adj G)).app

open category

def algebra_pair_reflexive (α : CT) : reflexive_pair (((F).map) α.a) (ε ((F).obj α.A)) :=
{ back :=(F).map $ (adjj).unit.app _,
  back_f := begin   rw ← functor.map_comp, rw ← adjunction.monad_η_app,  rw monad.algebra.unit α, simp end,
  back_g := begin simp end
}

def other_adjunctive_coequalizer (α : CT) : cofork (G.map ((F).map α.a)) (G.map (ε _)) :=
cofork.of_π α.a $ (
begin
  have := α.assoc,
  rw adjunction.monad_μ_app at this, rw this, rw functor.comp_map
end)

def other_adjunctive_coequalizer_split (α : CT) : split_coequalizer (G.map ((F).map α.a)) (G.map (ε _)) :=
⟨ other_adjunctive_coequalizer α,
  (adjunction.unit (is_right_adjoint.adj G)).app _,
  (adjunction.unit (is_right_adjoint.adj G)).app _,
  α.unit,
  (is_right_adjoint.adj G).right_triangle_components,
  ((adjunction.unit (is_right_adjoint.adj G)).naturality _).symm ⟩

-- TODO (BM): this is redundant, it's a special case of above
def adjunctive_coequalizer (B : D) : cofork (G.map ((F).map (G.map (ε B)))) (G.map (ε _)) :=
cofork.of_π (G.map (ε B))
begin
  rw ← G.map_comp, rw ← G.map_comp, congr' 1,
  apply (adjunction.counit (is_right_adjoint.adj G)).naturality (ε B)
end

def adjunctive_coequalizer_split (B : D) : split_coequalizer (G.map ((F).map (G.map (ε B)))) (G.map (ε _)) :=
⟨ adjunctive_coequalizer B,
  (adjunction.unit (is_right_adjoint.adj G)).app _,
  (adjunction.unit (is_right_adjoint.adj G)).app _,
  (is_right_adjoint.adj G).right_triangle_components,
  (is_right_adjoint.adj G).right_triangle_components,
  ((adjunction.unit (is_right_adjoint.adj G)).naturality _).symm⟩

  -- let mapped_cocone : cofork (G.map (F.map (G.map (ε.app B)))) (G.map (ε.app _)) := cofork.of_π (G.map (ε.app B)) _,
  --   swap, rw ← G.map_comp, rw ← G.map_comp, congr' 1,
  --   apply (ε.naturality (ε.app B)),
  -- let sc: split_coequalizer (G.map (F.map (G.map (ε.app B)))) (G.map (ε.app _)),  -- LOOK HERE
  -- { refine ⟨mapped_cocone,
  --           η.app _,
  --           η.app _,
  --           (is_right_adjoint.adj G).right_triangle_components,
  --           (is_right_adjoint.adj G).right_triangle_components,
  --           (η.naturality _).symm ⟩ },

omit 𝒞 𝒟
def restrict_equivalence {A B : Type v} (h : A ≃ B) (p : A → Prop) (q : B → Prop) (sound : ∀ a, p a ↔ q (h a)) : {a // p a} ≃ {b // q b} :=
{ to_fun := λ a, ⟨h.to_fun a.1, (sound a.1).1 a.2⟩,
  inv_fun := λ b, ⟨h.inv_fun b.1, begin apply (sound (h.inv_fun b.1)).2, convert b.2, apply h.right_inv end⟩,
  left_inv := begin rintro ⟨a, _⟩, dsimp, congr, rw h.left_inv end,
  right_inv := begin rintro ⟨b, _⟩, dsimp, congr, rw h.right_inv end }
include 𝒞
def coeq_equiv {X Y Z : C} {f g : X ⟶ Y} [has_colimit (parallel_pair f g)] : (coequalizer f g ⟶ Z) ≃ {h : Y ⟶ Z // f ≫ h = g ≫ h} :=
{ to_fun := λ i, ⟨coequalizer.π _ _ ≫ i, begin rw ← assoc, rw coequalizer.condition, simp end⟩,
  inv_fun := λ h, coequalizer.desc f g h.1 h.2,
  left_inv := λ i, begin dsimp, ext1, rw colimit.ι_desc, refl end,
  right_inv := λ ⟨h, t⟩, begin dsimp, congr, rw colimit.ι_desc, refl end }

include 𝒟

def e2 (α : CT) (B : D) : {f : (F).obj α.A ⟶ B // (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f} ≃ {fcheck : α.A ⟶ G.obj B // α.a ≫ fcheck = G.map ((F).map fcheck) ≫ G.map (ε B)} :=
restrict_equivalence ((adjj).hom_equiv _ _) _ _ $ λ f,
begin
  change (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f ↔
         α.a ≫ ((adjj).hom_equiv α.A B).to_fun f = G.map ((F).map (((adjj).hom_equiv α.A B).to_fun f)) ≫ G.map (ε B),
  rw ← G.map_comp,
  change (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f ↔
         α.a ≫ ((adjj).hom_equiv α.A B).to_fun f = G.map ((F).map (((adjj).hom_equiv α.A B).to_fun f) ≫ ε B),
  have: (F).map (((adjj).hom_equiv α.A B).to_fun f) ≫ ε B = f,
    erw ← (adjj).hom_equiv_counit, apply ((adjj).hom_equiv α.A B).left_inv f,
  rw this, clear this,
  change (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f ↔ α.a ≫ ((adjj).hom_equiv α.A B).to_fun f = G.map f,
  have: ((adjj).hom_equiv _ B).to_fun ((F).map α.a ≫ f) = α.a ≫ ((adjj).hom_equiv α.A B).to_fun f := (adjj).hom_equiv_naturality_left α.a f,
  rw ← this, clear this,
  split,
  { have: ((adjj).hom_equiv _ B).to_fun ((F).map α.a ≫ f) = _ := (adjj).hom_equiv_unit,
    rw this, clear this,
    intro t,
    rw t,
    rw G.map_comp,
    rw ← assoc,
    change ((adjj).unit.app (G.obj _) ≫ _) ≫ _ = _,
    rw (adjj).right_triangle_components, erw id_comp },
  { intro t,
    apply function.injective_of_left_inverse ((adjj).hom_equiv _ _).left_inv,
    rw t,
    have: ((adjj).hom_equiv _ B).to_fun (ε ((F).obj α.A) ≫ f) = ((adjj).hom_equiv _ ((F).obj α.A)).to_fun (ε ((F).obj α.A)) ≫
      G.map f := (adjj).hom_equiv_naturality_right (ε ((F).obj α.A)) f,
    erw this, clear this,
    symmetry,
    convert id_comp _ _,
    have: ((adjj).hom_equiv (G.obj ((F).obj α.A)) ((F).obj α.A)).to_fun (ε ((F).obj α.A)) = _ := (adjj).hom_equiv_unit,
    rw this,
    rw (adjj).right_triangle_components, refl }

end

def e3 (α : CT) (B : D) : {fcheck : α.A ⟶ G.obj B // α.a ≫ fcheck = G.map ((F).map fcheck) ≫ G.map (ε B)} ≃ (α ⟶ (monad.comparison G).obj B) :=
{ to_fun := λ f, { f := f.1, h' := f.2.symm },
  inv_fun := λ g, ⟨g.f, g.h.symm⟩,
  left_inv := λ ⟨f, _⟩, by {dsimp, congr},
  right_inv := λ ⟨g, _⟩, by {dsimp, ext1, refl} }

/- Assume we have coequalizers for (F a) and (ε F A) for all algebras (A,a). -/
variables (hce : ∀ (α : CT), has_colimit (parallel_pair (((F).map) α.a) (ε ((F).obj α.A))))

def L_obj : CT → D :=
λ α, @colimit _ _ _ _ _ (hce α)

def e1 (α : CT) (B : D) : (L_obj hce α ⟶ B) ≃ {f : (F).obj α.A ⟶ B // (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f} :=
coeq_equiv

def Le (α : CT) (B : D) : (L_obj hce α ⟶ B) ≃ (α ⟶ (monad.comparison G).obj B) :=
equiv.trans (e1 _ _ _) (equiv.trans (e2 _ _) (e3 _ _))

lemma Lhe (α : CT) (B B' : D) (g : B ⟶ B') (h : L_obj hce α ⟶ B) : (Le hce α B') (h ≫ g) = (Le hce α B) h ≫ (monad.comparison G).map g :=
begin
  ext, dunfold Le e1 e2 e3 coeq_equiv restrict_equivalence, dsimp,
  show ((adjj).hom_equiv α.A B').to_fun (coequalizer.π ((F).map α.a) (ε ((F).obj α.A)) ≫ h ≫ g) =
       ((adjj).hom_equiv α.A B ).to_fun (coequalizer.π ((F).map α.a) (ε ((F).obj α.A)) ≫ h) ≫ G.map g,
  conv_lhs {congr, skip, rw ← assoc},
  apply (adjj).hom_equiv_naturality_right
end

/-- The left adjoint to the comparison functor. -/
private def L : CT ⥤ D := adjunction.left_adjoint_of_equiv (Le hce) (Lhe hce)

/-- Suppose we have coequalizers for (F a) and (ε F A) for all algebras (A,a), then the comparison functor has a left adjoint.
    This is then shown to be an equivalence adjunction in the monadicity theorems.
  -/
def forms_adjoint : L hce ⊣ monad.comparison G := adjunction.adjunction_of_equiv_left (Le hce) (Lhe hce)
def left_adjoint_of_comparison : is_right_adjoint (monad.comparison G) :=
{ left := L hce, adj := forms_adjoint hce }

end algebra

-- /-- Take a G-split coequalizer `cf` for `f,g : A ⟶ B`, then we have a coequalizer for `f,g` and `G` of this coequalizer is still a colimit.  -/
def creates_G_split_coequalizers (G : D ⥤ C) :=
Π {A B : D} (f g : A ⟶ B) (cf : split_coequalizer (G.map f) (G.map g)),
creates_colimit (parallel_pair f g) G
  -- Σ (hcl : has_colimit (parallel_pair f g)), is_colimit $ G.map_cocone hcl.cocone

def preserves_reflexive_coequalizers (G : D ⥤ C) :=
Π {A B : D} {f g : A ⟶ B}, reflexive_pair f g → preserves_colimit (parallel_pair f g) G

-- def reflects_isomorphisms (G : D ⥤ C) :=
-- Π {A B : D} {f : A ⟶ B}, is_iso (G.map f) → is_iso f

section creates
-- [note] universe is v, the same as the homs in D and C. See the variable decalaration note in cones.lean in mathlib to see why.
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

-- def creates_limits (d : J ⥤ C) (F : C ⥤ D) :=
-- Π [fl : has_limit (d ⋙ F)], Σ (l : has_limit d),
--   is_limit $ F.map_cone l.cone

-- structure creates_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) :=
-- (upstairs : cone K)
-- (up_hits : F.map_cone upstairs ≅ c)
-- (any_up_is_lim : Π (up' : cone K) (iso : F.map_cone up' ≅ c), is_limit up')

-- -- Π (c : cone (d ⋙ F)) (t : is_limit c), (Σ (t : cone d), F.map_cone t ≅ c)

-- def creates_colimits (d : J ⥤ C) (F : C ⥤ D) :=
-- Π [fl : has_colimit (d ⋙ F)], Σ (l : has_colimit d),
--   is_colimit $ F.map_cocone l.cocone

variables {G : D ⥤ C} [monadic_right_adjoint G]

-- omit 𝒥
-- lemma monadic_really_creates_limits: creates_limits G :=
-- sorry

-- include 𝒥

-- lemma monadic_creates_colimits_that_monad_preserves (K : J ⥤ D) (ps : preserves_colimit (K ⋙ G) (left_adjoint G ⋙ G)) (ps : preserves_colimit (K ⋙ G) (left_adjoint G ⋙ G ⋙ left_adjoint G ⋙ G)) :
--   creates_colimit K G :=
-- sorry

end creates

variables {G : D ⥤ C} [is_right_adjoint G]

def adjoint_to_equivalence {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [unit_iso : is_iso adj.unit] [counit_iso : is_iso adj.counit] : C ≌ D :=
{ functor := F,
  inverse := G,
  unit_iso := as_iso adj.unit,
  counit_iso := as_iso adj.counit }

omit 𝒟
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
  apply cocones.ext _ _, refl, rintro ⟨j⟩, erw category.comp_id, rw simp_parallel_zero, refl,
  erw category.comp_id, refl
end

include 𝒟

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
  set F := left_adjoint G,
  set ε := (is_right_adjoint.adj G).counit,
  dsimp [forms_adjoint, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv, adjunction.left_adjoint_of_equiv, L_obj],
  set hce := (λ (β : monad.algebra (F ⋙ G)), hrc (algebra_pair_reflexive β)),
  letI: has_colimit (parallel_pair (F.map α.a) (ε.app (F.obj α.A))) := hce _,
  change is_iso ((Le hce α (coequalizer (F.map α.a) (ε.app (F.obj α.A)))).to_fun (𝟙 _)),
  dunfold Le e1 e2 e3 equiv.trans coeq_equiv restrict_equivalence,
  apply monad.algebra_iso_of_iso _,
  dsimp,
  erw category.comp_id,
  change is_iso
    (((is_right_adjoint.adj G).hom_equiv α.A (coequalizer (F.map α.a) (ε.app (F.obj α.A)))).to_fun
       (coequalizer.π (F.map α.a) (ε.app (F.obj α.A)))),
  let t := coequalizer.π (F.map α.a) (ε.app (F.obj α.A)),
  let ι := ((is_right_adjoint.adj G).hom_equiv _ _).to_fun t,
  show is_iso ι,
  let q: is_colimit (cofork.of_π t _) := coeq_fork_is_colimit (F.map α.a) (ε.app (F.obj α.A)),

  -- have := colimit.is_colimit (parallel_pair (F.map α.a) (ε.app (F.obj α.A))),
  have z := (prc (algebra_pair_reflexive _)).preserves,
  let m := really_preserves_coeq _ (z q),
  have alp: limits.is_colimit (limits.cofork.of_π α.a _) := split_coequalizer_is_coequalizer' (other_adjunctive_coequalizer_split α),
  let ι' := (is_colimit.unique_up_to_iso alp m).hom,
  have: ι = ι'.hom,
    apply is_colimit.hom_ext alp,
    apply cocone_parallel_pair_ext, show α.a ≫ ι = _ ≫ ((is_colimit.unique_up_to_iso alp m).hom).hom,
    dunfold is_colimit.unique_up_to_iso is_colimit.desc_cocone_morphism, dsimp,
    show α.a ≫ ι = (limits.cofork.of_π α.a _).ι.app limits.walking_parallel_pair.one ≫ _,
    erw alp.fac,
    dsimp,
    have: ι = (is_right_adjoint.adj G).unit.app α.A ≫ G.map t, apply (is_right_adjoint.adj G).hom_equiv_unit,
    rw this,
    have := (is_right_adjoint.adj G).unit.naturality α.a,
    slice_lhs 1 2 {erw (is_right_adjoint.adj G).unit.naturality α.a},
    change ((is_right_adjoint.adj G).unit.app (G.obj (F.obj α.A)) ≫ G.map (F.map α.a)) ≫ G.map t = G.map t,

    slice_lhs 2 3 {rw ← G.map_comp, rw coequalizer.condition (F.map α.a) (ε.app (F.obj α.A)), rw G.map_comp},
    slice_lhs 1 2 {rw (is_right_adjoint.adj G).right_triangle_components},
    erw category.id_comp,
  rw this,
  have i: is_iso ι',
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
  is_colimit (cofork.of_π ((is_right_adjoint.adj G).counit.app B) ((is_right_adjoint.adj G).counit.naturality ((is_right_adjoint.adj G).counit.app B))) :=
begin
  let ε := (is_right_adjoint.adj G).counit,
  let η := (is_right_adjoint.adj G).unit,
  let F := left_adjoint G,
  let my_cocone := cofork.of_π (ε.app B) (ε.naturality (ε.app B)),
  have rp : reflexive_pair (F.map (G.map (ε.app B))) (ε.app ((G ⋙ is_right_adjoint.left G).obj B)),
  { refine ⟨F.map (η.app _), _, _⟩,
    { rw ← F.map_comp,
      show F.map (η.app (G.obj B) ≫ G.map (ε.app B)) = 𝟙 (F.obj (G.obj B)),
      rw (is_right_adjoint.adj G).right_triangle_components,
      apply F.map_id },
    { show F.map (η.app (G.obj B)) ≫ ε.app (F.obj (G.obj B)) = 𝟙 (F.obj (G.obj B)),
      apply (is_right_adjoint.adj G).left_triangle_components }
  },
  haveI: has_colimit (parallel_pair (F.map (G.map (ε.app B))) (ε.app ((G ⋙ F).obj B))) := hrc rp,
  set t := colimit.cocone (parallel_pair (F.map (G.map (ε.app B))) (ε.app ((G ⋙ F).obj B))),

  set LKB := coequalizer (F.map (G.map (ε.app B))) (ε.app ((G ⋙ F).obj B)),
  set ι : F.obj (G.obj B) ⟶ LKB := coequalizer.π (F.map (G.map (ε.app B))) (ε.app ((G ⋙ F).obj B)),
  set ζ: t ⟶ my_cocone := is_colimit.desc_cocone_morphism (colimit.is_colimit _) my_cocone,
  suffices: is_iso ζ,
    apply is_colimit.of_iso_colimit (colimit.is_colimit _) (as_iso ζ),
  suffices: is_iso ((limits.cocones.functoriality G).map ζ),
    apply @is_iso_of_reflects_iso _ _ _ _ _ _ ζ _ (category_theory.reflects_cocone_isomorphism G _) _,
  have maptco: is_colimit (G.map_cocone t),
    apply (prc rp).preserves,
    apply colimit.is_colimit,
  have mapmyco: is_colimit (G.map_cocone my_cocone),
    apply really_preserves_coeq',
    apply split_coequalizer_is_coequalizer' (adjunctive_coequalizer_split _),
  let z := is_colimit.unique_up_to_iso maptco mapmyco,
  have: (cocones.functoriality G).map ζ = z.hom,
    apply is_colimit.uniq_cocone_morphism maptco,
  rw this, apply_instance,
end

set_option pp.implicit false
def counit_iso
  (hrc : has_reflexive_coequalizers D)
  (prc : preserves_reflexive_coequalizers G)
  (ri : reflects_isomorphisms G) :
  is_iso (forms_adjoint (λ α, hrc (algebra_pair_reflexive α)) : _ ⊣ monad.comparison G).counit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _, intro B,
  set F := left_adjoint G,
  set ε := (is_right_adjoint.adj G).counit,
  dsimp [forms_adjoint, adjunction.adjunction_of_equiv_left, adjunction.mk_of_hom_equiv, Le, equiv.trans, e1, e2, e3, coeq_equiv, restrict_equivalence, monad.comparison],
  apply coequalizer_desc_is_iso,
  convert ε_B_is_coequalizer B (λ _ _ _ _, hrc) (λ _ _ _ _, prc) ri,
  have: ((is_right_adjoint.adj G).hom_equiv (G.obj B) B).inv_fun (𝟙 (G.obj B)) = _ := (is_right_adjoint.adj G).hom_equiv_counit,
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

/- Plan:
   call the comparison functor K
   1. for each algebra, (Fα,εFA) is reflexive so we have a coequalizer for it.
   2. so we have a functor `L(A,α) := coeq(Fα,εFA)` as in left_adjoint_of_comparison
   3. K L (A,a) ≅ (A,a): Show that `Gπ : G F A → G L A` and `a : G F A → A` both coequalize `(GFa,GεFA)`. ++ a commuting diagram for the algebras.
   4. L K Y ≅ Y uses the fact that G preserves the coequalizer of (F ε Y, ε F G Y), so `G L (GY,GεY) ≅ G Y` and then G reflects isos.
 -/



-- def precise_monadicity : creates_G_split_coequalizers G → is_equivalence (monad.comparison G) :=
-- sorry

-- def monadic_creates_split_coequalizers : is_equivalence (monad.comparison G) → creates_G_split_coequalizers G :=
-- begin
--   intro t,
--   rw creates_G_split_coequalizers,
--   intros,
--   apply (monadic_creates_colimits_that_monad_preserves _).creates_colimit,
--   exact ⟨t⟩,
--   refine ⟨_⟩,
--   intro K,

-- end



end category_theory

