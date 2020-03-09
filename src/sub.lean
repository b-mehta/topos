/- Author: E.W.Ayers
    Definition of the subobject category. -/
import category_theory.full_subcategory
import .pullbacks .comma

universes u v w

namespace category_theory

open category_theory.limits
open category
open opposite

variables {C : Type u} [𝒞 : category.{v} C] {X Y : C}
include 𝒞

/-- The subobject category -/
-- NB: this isn't currently correct, it needs quotienting over
def sub (X : C) := {f : over X // mono f.hom}

def sub.obj_of_iso (f : X ≅ Y) : sub Y :=
⟨ over.mk f.hom,
  begin simp, apply is_iso.mono_of_iso end⟩

def sub.mk (f : X ⟶ Y) [mono f]: sub Y := ⟨over.mk f, by simp; apply_instance⟩
def sub.dom (s : sub X) : C := s.1.left
def sub.hom (s : sub X) : s.dom ⟶ X := s.1.hom
instance sub.mono (s : sub X) : mono s.hom := s.2

instance sub.is_cat : category (@sub C 𝒞 X) := show category {f : over X // _}, by apply_instance
def sub_hom {A B : sub X} (f : A ⟶ B) : A.dom ⟶ B.dom := comma_morphism.left f

variables {A B D: sub X}
@[simp] lemma sub_id :  sub_hom (𝟙 A) = 𝟙 (A.dom) := by refl
@[simp] lemma sub_comp {f : A ⟶ B} {g : B ⟶ D}: sub_hom (f ≫ g) = (sub_hom f) ≫ (sub_hom g) := by refl

def sub.mk_iso {A B : sub X} (f : A.dom ≅ B.dom) (e : f.hom ≫ B.hom = A.hom) : A ≅ B :=
begin
  refine iso.mk (over.hom_mk f.hom e) (over.hom_mk f.inv (eq.symm _)) _ _,
    apply (iso.eq_inv_comp f).2 e,
    {ext, show _ ≫ _ = 𝟙 _, simp  },
    {ext, show _ ≫ _ = 𝟙 _, simp  }
end

def sub.map [@has_pullbacks C 𝒞] (YX : Y ⟶ X) : (sub X) → (sub Y)
| A := @sub.mk _ _ (pullback A.hom YX) _ (pullback.snd) (pullback.preserve_mono A.mono)

@[simp] lemma sub.map.def [@has_pullbacks C 𝒞] (A : sub X) : (sub.map (𝟙 X) A).hom = pullback.snd := rfl

-- def sub.map_id {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X : C} {s : sub X}
--   : sub.map (𝟙 X) s ≅ s :=
-- begin
--   refine sub.mk_iso _ _,
--   apply limits.pullback.with_id_l s.hom,
--   have sq, apply @limits.pullback.condition _ _ _ _ _ (sub.hom s) (𝟙 X),
--   rw [comp_id] at sq,
--   simp,
--   rw ← sq,
--   refl
-- end

-- def sub.map_comp {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {s : sub Z}
--   : sub.map (f ≫ g) s ≅ (sub.map f (sub.map g s)) :=
-- begin
--   refine sub.mk_iso (limits.pullback.comp_r) _,
-- end

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
