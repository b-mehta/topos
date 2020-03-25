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

structure split_coequaliser  (f g : A ⟶ B) :=
(cf : cofork f g)
(t : B ⟶ A)
(s : cf.X ⟶ B)
(p1 : s ≫ cf.π = 𝟙 _)
(p2 : t ≫ g = 𝟙 B)
(p3 : t ≫ f = cf.π ≫ s)

@[simp] lemma simp_parallel_zero {f g : A ⟶ B} (t : cofork f g) : t.ι.app walking_parallel_pair.zero = f ≫ t.π :=
begin rw  ← cocone.w t walking_parallel_pair_hom.left, refl end

/-- You can make a coequaliser by finding a π which uniquely factors any other cofork. -/
def is_coeq_lemma {f g : A ⟶ B} {X : C} (π : B ⟶ X)
  (e : f ≫ π = g ≫ π)
  (factor : ∀ {Y} (c : B ⟶ Y), (f ≫ c = g ≫ c) →  unique {m : X ⟶ Y // c = π ≫ m}) :
  has_colimit (parallel_pair f g) :=
  begin
    refine {cocone := cofork.of_π π e, is_colimit := _},
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

def split_coequaliser_is_coequaliser {f g : A ⟶ B} (sc : split_coequaliser f g) : has_colimit (parallel_pair f g):=
begin
  refine is_coeq_lemma sc.cf.π _ _,
  apply limits.cofork.condition,
  intros, refine ⟨⟨⟨sc.s ≫ c,_⟩⟩,_⟩,
  rw [← category.assoc, ← sc.p3, category.assoc, a, ← category.assoc, sc.p2, category.id_comp],
  rintros ⟨m2,p⟩,
  apply subtype.ext.2,
  change m2 = sc.s ≫ c,
  rw [p, ← category.assoc, sc.p1], dsimp, simp
end

variable (C)
def has_reflexive_coequalisers := Π {A B : C} {f g : A ⟶ B}, reflexive_pair f g → has_colimit (parallel_pair f g)
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

lemma algebra_pair_reflexive (α : CT) : reflexive_pair (((F).map) α.a) (ε ((F).obj α.A)) :=
{ back :=(F).map $ (adjj).unit.app _,
  back_f := begin   rw ← functor.map_comp, rw ← adjunction.monad_η_app,  rw monad.algebra.unit α, simp end,
  back_g := begin simp end
}

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

/- Assume we have coequalisers for (F a) and (ε F A) for all algebras (A,a). -/
variables (hce : ∀ (α : CT), has_colimit (parallel_pair (((F).map) α.a) (ε ((F).obj α.A))))

def L_obj : CT → D :=
λ α, @colimit _ _ _ _ _ (hce α)

def e1 (α : CT) (B : D) : (L_obj hce α ⟶ B) ≃ {f : (F).obj α.A ⟶ B // (F).map α.a ≫ f = ε ((F).obj α.A) ≫ f} :=
coeq_equiv

@[reducible]
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

#check adjunction.left_adjoint_of_equiv (Le hce) (Lhe hce)

/-- The left adjoint to the comparison functor. -/
private def L : CT ⥤ D := adjunction.left_adjoint_of_equiv (Le hce) (Lhe hce)

/-- Suppose we have coequalisers for (F a) and (ε F A) for all algebras (A,a), then the comparison functor has a left adjoint.
    This is then shown to be an equivalence adjunction in the monadicity theorems.
  -/
def forms_adjoint : L hce ⊣ monad.comparison G := adjunction.adjunction_of_equiv_left (Le hce) (Lhe hce)
def left_adjoint_of_comparison : is_right_adjoint (monad.comparison G) :=
{ left := L hce, adj := forms_adjoint hce }

end algebra

/-- Take a G-split coequaliser `cf` for `f,g : A ⟶ B`, then we have a coequaliser for `f,g` and `G` of this coequaliser is still a colimit.  -/
def creates_split_coequalisers (G : D ⥤ C) :=
Π {A B : D} (f g : A ⟶ B) (cf : split_coequaliser (G.map f) (G.map g)),
  Σ (hcl : has_colimit (parallel_pair f g)), is_colimit $ G.map_cocone hcl.cocone

def preserves_reflexive_coequalisers (G : D ⥤ C) :=
Π {A B : D} {f g : A ⟶ B}, reflexive_pair f g → preserves_limit (parallel_pair f g) G

def reflects_isomorphisms (G : D ⥤ C) :=
Π {A B : D} {f : A ⟶ B}, is_iso (G.map f) → is_iso f

section creates
-- [note] universe is v, the same as the homs in D and C. See the variable decalaration note in cones.lean in mathlib to see why.
variables {J : Type v} [𝒥 : small_category J]
include 𝒥

def creates_limits (d : J ⥤ C) (F : C ⥤ D) :=
Π [fl : has_limit (d ⋙ F)], Σ (l : has_limit d),
  is_limit $ F.map_cone l.cone

structure creates_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) :=
(upstairs : cone K)
(up_hits : F.map_cone upstairs ≅ c)
(any_up_is_lim : Π (up' : cone K) (iso : F.map_cone up' ≅ c), is_limit up')

-- Π (c : cone (d ⋙ F)) (t : is_limit c), (Σ (t : cone d), F.map_cone t ≅ c)

def creates_colimits (d : J ⥤ C) (F : C ⥤ D) :=
Π [fl : has_colimit (d ⋙ F)], Σ (l : has_colimit d),
  is_colimit $ F.map_cocone l.cocone

variables {G : D ⥤ C} [monadic_right_adjoint G]

lemma monadic_really_creates_limits (d : J ⥤ D) : creates_limits d G :=
sorry

lemma monadic_creates_colimits_that_monad_preserves (d : J ⥤ D) (ps : limits.preserves_colimits_of_shape J ((left_adjoint G) ⋙ G)) :
  creates_colimits d G :=
sorry

end creates

variables {G : D ⥤ C} [is_right_adjoint G]

theorem crude_monadicity_theorem
  (hrc : has_reflexive_coequalisers C)
  (prc : preserves_reflexive_coequalisers G)
  (ri : reflects_isomorphisms G) :
  is_equivalence (monad.comparison G) :=
sorry
/- Plan:
   call the comparison functor K
   1. for each algebra, (Fα,εFA) is reflexive so we have a coequaliser for it.
   2. so we have a functor `L(A,α) := coeq(Fα,εFA)` as in left_adjoint_of_comparison
   3. K L (A,a) ≅ (A,a): Show that `Gπ : G F A → G L A` and `a : G F A → A` both coequalise `(GFa,GεFA)`. ++ a commuting diagram for the algebras.
   4. L K Y ≅ Y uses the fact that G preserves the coequaliser of (F ε Y, ε F G Y), so `G L (GY,GεY) ≅ G Y` and then G reflects isos.
 -/



def precise_monadicity : creates_split_coequalisers G → is_equivalence (monad.comparison G) :=
sorry

def monadic_creates_split_coequalisers : is_equivalence (monad.comparison G) → creates_split_coequalisers G :=
sorry



end category_theory

