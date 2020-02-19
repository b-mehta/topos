import category_theory.whiskering
import category_theory.opposites
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.pullbacks
import category_theory.epi_mono
import category_theory.category.Cat
import category_theory.yoneda
import .pullbacks
universes u v w

namespace category_theory

/-- The subobject category -/
structure sub (C : Type u) [𝒞 : category.{v} C] (X : C) :=
(A : C)
(f : A ⟶ X)
(hf : @mono C 𝒞 _ _ f)

def sub.obj_of_iso {C : Type u} [𝒞 : category.{v} C] {X Y : C} (f : X ≅ Y) : sub C Y := { A := X, f := f.hom, hf := begin apply is_iso.mono_of_iso end}

/-- sub is a cateogry. -/
instance sub.is_cat {C : Type u} [𝒞 : category.{v} C] {X : C} : category (@sub C 𝒞 X) :=
{  hom := λ A B, {h : A.A ⟶ B.A // h ≫ B.f = A.f}
,  id  := λ A, ⟨𝟙 A.A, by simp⟩
, comp :=
  λ A B C a b, subtype.mk ((subtype.val a) ≫ b.val) (begin
    cases b, cases a, dsimp at *, simp [b_property, a_property] at *,
  end)
, assoc' := begin rintros ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_,_⟩ ⟨_,_⟩ ⟨_,_⟩ ⟨_,_⟩, simp  end
, id_comp' := begin rintros ⟨A,a,_⟩ ⟨B,b,_⟩ ⟨f,_⟩, apply subtype.ext.2, dsimp,  simp end
, comp_id' := begin rintros ⟨A,a,_⟩ ⟨B,b,_⟩ ⟨f,_⟩, apply subtype.ext.2, dsimp, simp end
}

@[simp] lemma sub_id {C : Type u} [𝒞 : category.{v} C] {X : C} {A : sub C X}: subtype.val (𝟙 A) = 𝟙 A.A := by refl
@[simp] lemma sub_id2 {C : Type u} [𝒞 : category.{v} C] {X : C} {A : sub C X}: ↑(𝟙 A) = 𝟙 A.A := by refl
@[simp] lemma sub_comp {C : Type u} [𝒞 : category.{v} C] {X : C} {A B D : sub C X} {f : A ⟶ B} {g : B ⟶ D}: subtype.val (f ≫ g) = f.val ≫ g.val := by refl

open category_theory.limits
open opposite

def sub.map {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X Y : C} (YX : Y ⟶ X) : (sub C X) → (sub C Y)
| A := sub.mk (pullback A.f YX) (pullback.snd) (pullback.preserve_mono A.hf)

def sub.map_id {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X : C} {s : sub C X}
  : sub.map (𝟙 X) s ≅ s :=
begin
  sorry
end

def sub.map_comp {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {s : sub C Z}
  : sub.map (f ≫ g) s ≅ (sub.map f (sub.map g s)) :=
begin
  sorry
end

-- /-- sub is a functor -/
-- def sub.functor (C : Type u) [small_category C] [has_pullbacks C]: functor Cᵒᵖ (Type u) :=
-- { obj := λ (X : Cᵒᵖ), (sub C (unop X)) -- [todo] this needs to be the skeleton of `sub C X`
-- , map := λ X Y f, sub.map f.unop,
-- , map_id' := begin intro X, simp [sub.map],  /-[todo] big problem here: this is only up to iso! -/ sorry   end
-- , map_comp' := begin sorry end
-- }

-- def has_subobject_classifier (C : Type u) [small_category C] [has_pullbacks C] [has_terminal C] := @representable C _ (sub.functor)

open category_theory.limits

end category_theory
