/- Author: E.W.Ayers
   This should be in mathlib. Some simp and extensionality lemmas for comma and over. -/
import category_theory.comma

namespace category_theory

universes u v
variables {C : Type u} [category.{v} C] {X : C}

@[simp] lemma over.mk_hom_id {f : over X} : over.mk f.hom = f :=
begin cases f, dsimp [over.mk], congr, apply subsingleton.elim end

end category_theory