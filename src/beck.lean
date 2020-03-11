import data.fintype
import category_theory.limits.limits
import category_theory.limits.shapes.equalizers
import tactic
import category_theory.monad.adjunction
universes u v u₂ v₂ v₁ 
  
namespace category_theory

open limits
section reflexive_pair
def reflexive_pair : Type v := limits.walking_parallel_pair.{v}
open limits.walking_parallel_pair
inductive reflexive_pair_hom : reflexive_pair.{v} → reflexive_pair.{v} → Type v
|left : reflexive_pair_hom zero one
|right : reflexive_pair_hom zero one
|back : reflexive_pair_hom one zero
|left_back : reflexive_pair_hom zero zero
|right_back : reflexive_pair_hom zero zero
|id : Π (X : reflexive_pair), reflexive_pair_hom X X
open reflexive_pair_hom

def reflexive_pair_hom.comp :
  Π (X Y Z : reflexive_pair.{v})
    (f : reflexive_pair_hom.{v} X Y) (g : reflexive_pair_hom.{v} Y Z),
    reflexive_pair_hom.{v} X Z
  | _ _ _ back left := reflexive_pair_hom.id _
  | _ _ _ back right := reflexive_pair_hom.id _
  | _ _ _ left back := left_back
  | _ _ _ right back := right_back
  | _ _ _ back left_back := back
  | _ _ _ back right_back := back
  | _ _ _ left_back left_back := left_back
  | _ _ _ right_back right_back := right_back
  | _ _ _ left_back left := left
  | _ _ _ left_back right := left
  | _ _ _ right_back left := right
  | _ _ _ right_back right := right
  | _ _ _ left_back right_back := left_back
  | _ _ _ right_back left_back := right_back
  | _ _ _ (id _) h := h
  | _ _ _ back (id zero) := back
  | _ _ _ left_back (id zero) := left_back
  | _ _ _ right_back (id zero) := right_back
  | _ _ _ left (id one) := left
  | _ _ _ right (id one) := right


end reflexive_pair
instance walking_parallel_pair_hom_category : small_category.{v} reflexive_pair :=
{ hom  := reflexive_pair_hom,
  id   := reflexive_pair_hom.id,
  comp := reflexive_pair_hom.comp,
  assoc' := begin intros, cases f; cases g; cases h, all_goals {refl} end,
  id_comp' := begin intros, cases f, all_goals {refl} end,
  comp_id' := begin intros, cases f, all_goals {refl} end,
}

variables {C : Type u} [𝒞 : category.{v} C] 
include 𝒞
variables {A B : C}

structure split_coequaliser  (f g : A ⟶ B) :=
(cf : cofork f g)
(t : B ⟶ A)
(s : cf.X ⟶ B)
(p1 : s ≫ cf.π = 𝟙 _)
(p2 : t ≫ g = 𝟙 B)
(p3 : t ≫ f = cf.π ≫ s)

-- [todo] show it's a coequaliser
open category_theory

@[simp] lemma fml {f g : A ⟶ B} (t : cofork f g) : t.ι.app walking_parallel_pair.zero = f ≫ t.π :=
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
      change (_ ≫ _) ≫ k = _,  rw category.assoc, rw ← h1, rw fml,
      change π ≫ k = c.π, dsimp, rw h1,
    rcases (factor c.π c.condition) with ⟨⟨⟨k,h1⟩⟩,h2⟩,
        intros, change m = k,
         have, apply h2 ⟨m,eq.symm (w walking_parallel_pair.one)⟩,
         apply subtype.ext.1 this, 
  end
 
def as_coeq {f g : A ⟶ B} (sc : split_coequaliser f g) : has_colimit (parallel_pair f g):= 
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

-- [todo] sort out universe polymorphism
variables {D : Type u} [𝒟 : category.{v} D] 
include 𝒟

-- variables (G : D ⥤ C)

def functor_split (G : D ⥤ C) {A B : D} {f g : A ⟶ B} := 
split_coequaliser (G.map f) (G.map g)

def paraparapar  (G : D ⥤ C) {A B : D} (f g : A ⟶ B) : parallel_pair (G.map f) (G.map g) = (parallel_pair f g) ⋙ G :=
begin
  apply functor.ext, intros, cases f_1, dsimp, simp, dsimp, simp, dsimp, simp,
  intros, cases X, refl, refl
end

-- [NOTE] we really need a creates_limits 

-- [TODO] make the above definition not completely foul. To do this, instead of showing that the cones are iso, show that the apexes are iso and the pis commute
def creates_split_coequalisers (G : D ⥤ C) : Prop := 
∀ {A B : D} (f g : A ⟶ B) (cf : split_coequaliser (G.map f) (G.map g)), 
  ∃ (hcl : has_colimit (parallel_pair f g)), 
    let c1 := (limits.cocones.functoriality G).obj (@colimit.cocone _ _ _ _  (parallel_pair f g) hcl) in
    let c2 := cf.cf in
    ∃ e : c1.X ≅ c2.X, (c1.ι.app limits.walking_parallel_pair.one) ≫ e.hom = c2.π

-- def precise_monadicity (G : D ⥤ C) [is_right_adjoint G] : creates_split_coequalisers G ≃ is_equivalence (monad.comparison G) := 
-- sorry


-- variables {J : Type v} [𝒥 : small_category J]
-- include 𝒥

end category_theory
