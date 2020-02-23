import category_theory.limits.shapes.binary_products
import category_theory.adjunction

universes u v

namespace category_theory

open limits category
section
variables {C : Type u} [𝒞 : category.{v} C] [@has_binary_products.{v} C 𝒞] {A X Y : C}
include 𝒞

@[simp] lemma prod_left_def  : limit.π (pair X Y) walking_pair.left = limits.prod.fst := rfl
@[simp] lemma prod_right_def  : limit.π (pair X Y) walking_pair.right = limits.prod.snd := rfl

lemma prod.hom_ext {a b : A ⟶ X ⨯ Y} (h1 : a ≫ limits.prod.fst = b ≫ limits.prod.fst) (h2 : a ≫ limits.prod.snd = b ≫ limits.prod.snd) : a = b :=
begin
  apply limit.hom_ext,
  rintros (_ | _),
  simp, assumption,
  simp, assumption,
end

def prodinl {X : C} : C ⥤ C :=
{ obj := λ Y, limits.prod X Y,
  map := λ Y Z f, limits.prod.map (𝟙 X) f,
  map_id' := begin intros, apply prod.hom_ext, simp, exact category.comp_id _ _, simp, exact category.comp_id _ _ end,
  map_comp' := λ U V W f g, begin apply prod.hom_ext, simp, rw [comp_id _ (𝟙 X)], simp end
}
end

-- [todo] doesn't this need to be natural in X too?
def is_cartesian_closed (C : Type u) [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] :=
∀ X : C, @is_left_adjoint C 𝒞 C 𝒞 (@prodinl C 𝒞 bp X)

-- [todo] maybe an explicit definition?
-- class is_cc (C : Type u) [𝒞 : category.{v} C] [bp : @has_binary_products C 𝒞] :=
-- (exp : Cᵒᵖ × C ⥤ C)
-- (ev : Π {X Y} : Y ⨯ exp X Y ⟶ X)
-- (coev : Π {X Y} : X ⟶ exp (Y ⨯ X) Y)
-- ...

end category_theory
