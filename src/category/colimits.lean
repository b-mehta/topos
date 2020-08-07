import category_theory.elements
import category_theory.limits.limits
import category_theory.functor_category
import category_theory.limits.types
import category_theory.limits.functor_category
import category_theory.adjunction
import category.adjunction

namespace category_theory

open category limits
universes v₁ v₂ u₁ u₂

set_option pp.universes true

-- check what happens if we allow C's homs to be in another universe
variables {C : Type u₁} [small_category C]

section
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variables [has_colimits ℰ]
variable (A : C ⥤ ℰ)

def R : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
{ obj := λ E,
  { obj := λ c, A.obj c.unop ⟶ E,
    map := λ c c' f k, A.map f.unop ≫ k },
  map := λ E E' k, { app := λ c f, f ≫ k } }.

def L_obj (P : Cᵒᵖ ⥤ Type u₁) : ℰ :=
colimit ((category_of_elements.π P).left_op ⋙ A)

set_option pp.universes false

def Le (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) : (L_obj A P ⟶ E) ≃ (P ⟶ (R A).obj E) :=
(colimit.hom_iso' ((category_of_elements.π P).left_op ⋙ A) E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f,
    begin
      ext p,
      let p' : (P.elements)ᵒᵖ := (opposite.op ⟨c, p⟩),
      let p'' : (P.elements)ᵒᵖ := (opposite.op ⟨c', P.map f p⟩),
      let f' : p'' ⟶ p' := has_hom.hom.op ⟨f, rfl⟩,
      apply (k.2 f').symm,
    end },
  inv_fun := λ τ,
  { val := λ p, τ.app p.unop.1 p.unop.2,
    property := λ p p' f,
    begin
      change A.map f.unop.1.unop ≫ τ.app p'.unop.1 p'.unop.2 = τ.app p.unop.1 p.unop.2,
      have := congr_fun (τ.naturality f.unop.1) p'.unop.2,
      dsimp [R] at this,
      erw [← this, f.unop.2],
    end },
  left_inv :=
  begin
    rintro ⟨k₁, k₂⟩,
    ext,
    dsimp,
    congr' 1,
    rw opposite.op_eq_iff_eq_unop,
    cases x.unop,
    refl,
  end,
  right_inv :=
  begin
    rintro ⟨_, _⟩,
    ext,
    refl,
  end }

def L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv (λ P E, Le A P E)
begin
  intros P E E' g k,
  ext,
  dsimp [Le, colimit.hom_iso', is_colimit.hom_iso', R],
  simp,
end

def L_adjunction : L A ⊣ R A := adjunction.adjunction_of_equiv_left _ _
end

set_option pp.universes false

def right_is_id : R (yoneda : C ⥤ _) ≅ 𝟭 _ :=
nat_iso.of_components
(λ P,
nat_iso.of_components (λ X, by apply yoneda_sections_small X.unop)
(λ X Y f,
begin
  ext,
  dsimp [R, yoneda_lemma, ulift_trivial],
  have := congr_fun (x.naturality f) (𝟙 _),
  dsimp at this,
  rw [id_comp, ← this, comp_id]
end))
begin
  intros,
  ext c g,
  refl,
end

def left_is_id : L (yoneda : C ⥤ _) ≅ 𝟭 _ :=
left_adjoint_uniq (L_adjunction _) (adjunction.of_nat_iso_right adjunction.id right_is_id.symm)

def main (P : Cᵒᵖ ⥤ Type u₁) :
  colimit ((category_of_elements.π P).left_op ⋙ yoneda) ≅ P :=
left_is_id.app P

def the_cocone (P : Cᵒᵖ ⥤ Type u₁) :
  cocone ((category_of_elements.π P).left_op ⋙ yoneda) :=
 cocone.extend (colimit.cocone _) (main P).hom

def is_a_limit (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (the_cocone P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ yoneda)),
  change is_iso (main P).hom,
  apply_instance,
end

#check L_adjunction yoneda

end category_theory
