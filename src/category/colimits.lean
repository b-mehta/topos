import category_theory.elements
import category_theory.limits.limits
import category_theory.functor_category
import category_theory.limits.types
import category_theory.limits.functor_category
import category_theory.adjunction.opposites

namespace category_theory

open category limits
universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [small_category C]

namespace colimit_adj
variables {ℰ : Type u₂} [category.{u₁} ℰ]
variables [has_colimits ℰ]
variable (A : C ⥤ ℰ)

@[simps]
def R : ℰ ⥤ (Cᵒᵖ ⥤ Type u₁) :=
{ obj := λ E,
  { obj := λ c, A.obj c.unop ⟶ E,
    map := λ c c' f k, A.map f.unop ≫ k },
  map := λ E E' k, { app := λ c f, f ≫ k } }.

private noncomputable def L_obj (P : Cᵒᵖ ⥤ Type u₁) : ℰ :=
colimit ((category_of_elements.π P).left_op ⋙ A)

def Le' (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) {c : cocone ((category_of_elements.π P).left_op ⋙ A)}
  (t : is_colimit c) : (c.X ⟶ E) ≃ (P ⟶ (R A).obj E) :=
(t.hom_iso' E).to_equiv.trans
{ to_fun := λ k,
  { app := λ c p, k.1 (opposite.op ⟨_, p⟩),
    naturality' := λ c c' f,
    begin
      ext p,
      let p' : P.elementsᵒᵖ := opposite.op ⟨c, p⟩,
      let p'' : P.elementsᵒᵖ := opposite.op ⟨c', P.map f p⟩,
      let f' : p'' ⟶ p' := has_hom.hom.op ⟨f, rfl⟩,
      apply (k.2 f').symm,
    end },
  inv_fun := λ τ,
  { val := λ p, τ.app p.unop.1 p.unop.2,
    property := λ p p' f,
    begin
      simp_rw [← f.unop.2],
      apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm,
    end },
  left_inv :=
  begin
    rintro ⟨k₁, k₂⟩,
    ext,
    dsimp,
    congr' 1,
    simp,
  end,
  right_inv :=
  begin
    rintro ⟨_, _⟩,
    ext,
    refl,
  end }

lemma Le'_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂)
  {c : cocone _} (t : is_colimit c) (k : c.X ⟶ E₁) :
Le' A P E₂ t (k ≫ g) = Le' A P E₁ t k ≫ (R A).map g :=
begin
  ext _ X p,
  apply (assoc _ _ _).symm,
end

noncomputable def L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
adjunction.left_adjoint_of_equiv
(λ P E, Le' A P E (colimit.is_colimit _))
(λ P E E' g, Le'_natural A P E E' g _)

noncomputable def L_adjunction : L A ⊣ R A := adjunction.adjunction_of_equiv_left _ _
end colimit_adj

open colimit_adj

def right_is_id : R (yoneda : C ⥤ _) ≅ 𝟭 _ :=
nat_iso.of_components
(λ P, nat_iso.of_components (λ X, yoneda_sections_small X.unop _)
  (λ X Y f, funext $ λ x,
  begin
    apply eq.trans _ (congr_fun (x.naturality f) (𝟙 _)),
    dsimp [ulift_trivial, yoneda_lemma],
    simp only [id_comp, comp_id],
  end))
(λ _ _ _, nat_trans.ext _ _ $ funext $ λ _, funext $ λ _, rfl)

noncomputable def left_is_id : L (yoneda : C ⥤ _) ≅ 𝟭 _ :=
adjunction.left_adjoint_uniq (L_adjunction _) (adjunction.of_nat_iso_right adjunction.id right_is_id.symm)

noncomputable def main (P : Cᵒᵖ ⥤ Type u₁) :
  colimit ((category_of_elements.π P).left_op ⋙ yoneda) ≅ P :=
left_is_id.app P

-- This is a cocone with point `P`, for which the diagram consists solely of representables.
noncomputable def the_cocone (P : Cᵒᵖ ⥤ Type u₁) :
  cocone ((category_of_elements.π P).left_op ⋙ yoneda) :=
cocone.extend (colimit.cocone _) (main P).hom

lemma desc_self {J : Type v₁} {C : Type u₁} [small_category J] [category.{v₁} C]
  (F : J ⥤ C) {c : cocone F} (t : is_colimit c) : t.desc c = 𝟙 c.X :=
(t.uniq _ _ (λ j, comp_id _)).symm

lemma col_desc_self {J : Type v₁} {C : Type u₁} [small_category J] [category.{v₁} C] (F : J ⥤ C)
  [has_colimit F] : colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
desc_self F (colimit.is_colimit _)

noncomputable def is_a_limit (P : Cᵒᵖ ⥤ Type u₁) : is_colimit (the_cocone P) :=
begin
  apply is_colimit.of_point_iso (colimit.is_colimit ((category_of_elements.π P).left_op ⋙ yoneda)),
  change is_iso (colimit.desc _ (cocone.extend _ _)),
  rw [colimit.desc_extend, col_desc_self, id_comp],
  apply_instance,
end

end category_theory
