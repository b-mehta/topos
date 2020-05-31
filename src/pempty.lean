/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.pempty

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/

universes v u w -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

namespace functor
variables (C : Type u) [category.{v} C]

def unique_from_pempty (K : pempty ⥤ C) : functor.empty C ≅ K :=
begin
  apply nat_iso.of_components _ _,
  rintro ⟨⟩,
  rintro ⟨⟩
end

end functor
end category_theory