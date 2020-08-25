import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.terminal
import category_theory.limits.limits
import category_theory.limits.types

namespace category_theory

open limits

universes v u
variables {C : Type u} [category.{v} C]
variable {Q : C}

section prods

variables [has_binary_products C] {X Y : C}

def pair (x : Q ⟶ X) (y : Q ⟶ Y) : Q ⟶ X ⨯ Y :=
prod.lift x y

def fst (xy : Q ⟶ X ⨯ Y) : Q ⟶ X :=
xy ≫ limits.prod.fst

def snd (xy : Q ⟶ X ⨯ Y) : Q ⟶ Y :=
xy ≫ limits.prod.snd

def prod.equiv (Q X Y : C) : (Q ⟶ X ⨯ Y) ≃ (Q ⟶ X) × (Q ⟶ Y) :=
{ to_fun := λ f, (fst f, snd f),
  inv_fun := λ gh, pair gh.1 gh.2,
  left_inv := λ f, prod.hom_ext (by simp [pair, fst]) (by simp [pair, snd]),
  right_inv := λ gh, prod.ext (by simp [pair, fst]) (by simp [pair, snd]) }

end prods

-- section type
-- local attribute [instance] has_terminal.has_limits_of_shape

-- instance : has_terminal (Type u) :=
-- { has_limits_of_shape := infer_instance }

-- def element_iso_type {X : Type u} : (terminal.{u} (Type u) ⟶ X) ≃ X :=
-- { to_fun := λ f, f ⟨λ k, k.elim, by rintro ⟨⟩⟩,
--   inv_fun := λ x _, x,
--   left_inv := λ f,
--   begin
--     ext1 ⟨⟩,
--     dsimp,
--     congr' 2,
--     ext1 ⟨⟩,
--   end,
--   right_inv := λ x, rfl }
-- end type

end category_theory