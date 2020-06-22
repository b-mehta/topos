import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.types
import category_theory.limits.shapes.binary_products
import category_theory.limits.functor_category
import category_theory.functor_category
import sieve
import subobject_classifier

universes v u

open category_theory category_theory.category category_theory.limits

section reflects
variables {C : Type u} [category.{v} C]

def make_exponential [has_finite_products.{v} C] (A : C) (expo : C → C) (ev : Π B, A ⨯ expo B ⟶ B) (trans : Π {B B'} (φ : A ⨯ B ⟶ B'), B ⟶ expo B')
  (comm : ∀ {B B' : C} (φ : A ⨯ B ⟶ B'), limits.prod.map (𝟙 _) (trans φ) ≫ ev B' = φ)
  (unique_trans : ∀ {B B' : C} {φ : A ⨯ B ⟶ B'} {t : B ⟶ expo B'}, limits.prod.map (𝟙 A) t ≫ ev B' = φ → trans φ = t) :
  exponentiable A :=
{ is_adj :=
  { right :=
    begin
      refine @adjunction.right_adjoint_of_equiv _ _ _ _ (prod_functor.obj A) expo _ _,
      intros B B',
      refine ⟨trans, λ g, limits.prod.map (𝟙 _) g ≫ ev _, comm, λ g, unique_trans rfl⟩,
      dsimp,
      intros,
      apply unique_trans,
      rw [prod_map_id_comp, assoc, comm],
    end,
    adj := adjunction.adjunction_of_equiv_right _ _ } }

variables {J K : Type v} [small_category J] [small_category K]

variables {F : J ⥤ K ⥤ C}

@[simps]
def pointwise_cone (k : K) (c : cone F) : cone (F.flip.obj k) :=
{ X := c.X.obj k,
  π := { app := λ j, (c.π.app j).app k } }.

def jointly_reflects (c : cone F) (t : Π k, is_limit (pointwise_cone k c)) : is_limit c :=
{ lift := λ s,
  { app := λ k,
    begin
      apply (t k).lift ⟨s.X.obj k, _⟩,
      refine ⟨λ j, (s.π.app j).app k, _⟩,
      dsimp, intros,
      simp only [cone.functor_w, id_comp],
    end,
    naturality' :=
    begin
      intros,
      apply (t Y).hom_ext,
      intro j,
      rw [assoc, (t Y).fac],
      simp only [nat_trans.naturality, assoc, pointwise_cone_π_app],
      change _ = _ ≫ (pointwise_cone _ _).π.app _ ≫ _,
      rw (t X).fac_assoc _ j,
    end },
  fac' := λ s j,
  begin
    ext k,
    apply (t k).fac,
  end,
  uniq' := λ s m w,
  begin
    ext1,
    ext1,
    apply (t x).hom_ext,
    intro j,
    rw (t x).fac,
    simp [(t x).fac, ← w],
  end }

end reflects

variables {C : Type u} [small_category C]

def jointly_reflects_pullback {W X Y Z : Cᵒᵖ ⥤ Type u} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) (comm : f ≫ h = g ≫ k)
  (t : ∀ (c : C), is_limit (pullback_cone.mk (f.app (opposite.op c)) (g.app (opposite.op c)) (begin change (f ≫ h).app _ = _, rw comm, refl end) : pullback_cone (h.app (opposite.op c)) (k.app (opposite.op c)))) :
 is_limit (pullback_cone.mk _ _ comm) :=
begin
  apply jointly_reflects,
  intro c',
  specialize t c'.unop,
  apply is_limit.of_iso_limit (is_limit.of_cone_equiv (cones.postcompose_equivalence (diagram_iso_cospan ((cospan h k).flip.obj c'))).inverse _) _,
  swap,
  apply t,
  apply cones.ext _ _,
  apply iso.refl _,
  intro j,
  cases j,
  dsimp [diagram_iso_cospan], simp,
  cases j,
  dsimp [diagram_iso_cospan], simp,
  dsimp [diagram_iso_cospan], simp,
end

variable (C)
@[simps]
def presheaf.classifier : Cᵒᵖ ⥤ Type u :=
{ obj := λ A, sieve A.unop,
  map := λ A B f S, S.pullback f.unop }

@[simps]
def one : Cᵒᵖ ⥤ Type u :=
{ obj := λ T, punit,
  map := λ T₁ T₂ f, id }

@[simps]
def presheaf.truth : one C ⟶ presheaf.classifier C :=
{ app := λ X _, (⊤ : sieve _) }

instance : mono (presheaf.truth C) :=
begin
  refine ⟨λ Z g h eq, _⟩,
  ext,
  apply subsingleton.elim _ _,
  dsimp,
  apply_instance,
end

@[simps]
def presheaf.classify (Q P : Cᵒᵖ ⥤ Type u) (i : Q ⟶ P) [mono i] : P ⟶ presheaf.classifier C :=
{ app := λ c x,
  begin
    refine ⟨λ f, ∃ y, i.app (opposite.op f.left) y = P.map f.hom.op x, _⟩,
    rintros Y Z f g ⟨w, h⟩,
    refine ⟨Q.map g.op w, _⟩,
    dsimp at ⊢ h,
    rw P.map_comp,
    dsimp,
    rw ← h,
    exact congr_fun (i.naturality g.op) w,
  end }.

noncomputable def presheaf.is_classifier : is_subobject_classifier (presheaf.truth C) :=
{ classifier_of := presheaf.classify C,
  classifies' := λ Q P i hi,
  { top := { app := λ _ _, punit.star },
    comm :=
    begin
      ext A x Y f,
      change true ↔ _,
      rw true_iff,
      exact ⟨Q.map f.op x, congr_fun (i.naturality f.op) x⟩,
    end,
    is_pb :=
    begin
      apply jointly_reflects_pullback,
      intro c,
      apply is_limit.mk''' _ _ _,
      refine ⟨λ Z g h eq, _⟩,
      funext, apply subsingleton.elim _ _,
      dsimp, apply_instance,
      change mono (i.app (opposite.op c)),
      resetI,
      exact preserves_mono_of_preserves_pullback ((evaluation _ (Type u)).obj (opposite.op c)) Q P i,
      intro s,
      refine ⟨_, _⟩,
      intro z,
      dsimp,
      have := congr_fun s.condition z,
      dsimp only [types_comp_apply, presheaf.classify] at this,
      have := congr_arg sieve.arrows this,
      dsimp at this,
      have q : _ = _ := congr_fun this_1 (over.mk (𝟙 c)),
      dsimp at q,
      change true = _ at q,
      rw [eq_iff_iff, P.map_id, true_iff, types_id_apply] at q,
      apply (classical.indefinite_description _ q).1,
      dsimp,
      change _ ≫ i.app _ = _,
      funext z,
      dsimp,
      refine (classical.indefinite_description (λ x, i.app (opposite.op c) x = s.snd z) _).2,
    end },
  uniquely' := λ Q P i hi χ hχ,
  begin
    ext1,
    ext1 c,
    change has_pullback_top _ _ _ at hχ,
    ext1,
    ext1,
    have hχc : has_pullback_top (i.app c) (χ.app c) ((presheaf.truth C).app c) := preserves_hpb ((evaluation _ (Type u)).obj c) hχ,
    dsimp at hχc,
    have hχf := preserves_hpb ((evaluation _ (Type u)).obj (opposite.op Y)) hχ,
    dsimp at hχf,
    dsimp [presheaf.classify],
    change (∃ (y : Q.obj (opposite.op Y)), i.app (opposite.op Y) y = P.map f.op x) ↔ over.mk f ∈ (χ.app c x).arrows,
    obtain ⟨kac, lac, mac⟩ := hχc,
    obtain ⟨kaf, laf, maf⟩ := hχf,
    split,
      rintro ⟨y, hy⟩,
      have hy₂ := congr_fun laf y,
      dsimp at hy₂,
      rw hy at hy₂,
      have hy₃ := congr_fun (χ.naturality f.op) x,
      dsimp at hy₃,
      rw hy₃ at hy₂,
      have : over.mk (𝟙 Y) ∈ (sieve.pullback (χ.app c x) f).arrows,
        rw ←hy₂,
        trivial,
      change over.mk (𝟙 Y ≫ f) ∈ (χ.app c x).arrows at this,
      rwa [id_comp] at this,
    intro hf,
    obtain ⟨l, hl₁, hl₂⟩ := pullback_cone.is_limit.lift' maf (𝟙 _) (λ _, P.map f.op x) _,
    refine ⟨l punit.star, _⟩,
    have := congr_fun hl₂ punit.star,
    exact this,
    ext1 ⟨⟩,
    dsimp,
    have hy₃ := congr_fun (χ.naturality f.op) x,
    dsimp at hy₃,
    rw hy₃,
    symmetry,
    rw eq_top_iff,
    intros t ht,
    simp [hf],
  end }.

noncomputable def presheaf_has_subobj_classifier : has_subobject_classifier.{u} (Cᵒᵖ ⥤ Type u) :=
{ Ω := _, Ω₀ := _, truth := _, is_subobj_classifier := presheaf.is_classifier C }

variables {C} (P Q R : Cᵒᵖ ⥤ Type u)

@[simps]
def exponential_functor : Cᵒᵖ ⥤ Type u :=
{ obj := λ A, yoneda.obj A.unop ⨯ P ⟶ Q,
  map := λ A A' f g, limits.prod.map (yoneda.map f.unop) (𝟙 _) ≫ g,
  map_comp' := λ A A' A'' f g,
  begin
    ext1,
    simp [prod_map_comp_id],
  end }.

@[simps]
def eval : P ⨯ exponential_functor P Q ⟶ Q :=
{ app := λ c θy,
  begin
    refine ((θy.1 walking_pair.right).app c) ⟨λ j, walking_pair.cases_on j (𝟙 _) (θy.1 walking_pair.left), _⟩,
    rintros ⟨j₁ | j₁⟩ _ ⟨⟨rfl⟩⟩; refl
  end,
  naturality' := λ c c' f,
  begin
    ext1 ⟨_, _⟩,
    dsimp,
    change _ = ((x_val walking_pair.right).app c ≫ Q.map f) ⟨λ j, walking_pair.cases_on j (𝟙 c.unop) (x_val walking_pair.left), _⟩,
    rw ← (x_val walking_pair.right).naturality f,
    change (x_val walking_pair.right).app c' _ = (x_val walking_pair.right).app c' _,
    congr' 1,
    rw subtype.ext,
    ext ⟨j⟩,
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _,
    rw [id_comp, comp_id],
    refl,
  end }

@[simps]
def transpose (φ : P ⨯ R ⟶ Q) : R ⟶ exponential_functor P Q :=
{ app := λ c u,
  { app := λ D,
    begin
      intro fx,
      apply φ.app D,
      refine ⟨λ j, walking_pair.cases_on j _ _, _⟩,
      exact fx.1 walking_pair.right,
      exact R.map (fx.1 walking_pair.left).op u,
      rintros ⟨_ | _⟩ _ ⟨⟨rfl⟩⟩; refl
    end,
    naturality' := λ D₁ D₂ k,
    begin
      ext1 ⟨x, hx⟩,
      change φ.app D₂ _ = (φ.app D₁ ≫ Q.map k) _,
      rw ← φ.naturality k,
      dsimp [types_comp_apply],
      congr' 1,
      rw subtype.ext,
      ext ⟨j⟩,
      dsimp,
      refl,
      apply congr_fun (R.map_comp (has_hom.hom.op (x walking_pair.left)) k) u,
    end
    },
  naturality' := λ X Y f,
  begin
    ext x c ⟨_, _⟩,
    change φ.app c ⟨_, _⟩ = φ.app c ⟨_, _⟩,
    congr' 2,
    ext ⟨j⟩,
    refl,
    change R.map (has_hom.hom.op (x_1_val walking_pair.left)) (R.map f x) = R.map (f ≫ has_hom.hom.op (x_1_val walking_pair.left)) x,
    rw R.map_comp, refl,
  end }.

def exponentiables (P : Cᵒᵖ ⥤ Type u) : exponentiable P :=
begin
  apply make_exponential P (exponential_functor P) (eval P) (λ R Q, transpose _ _ _) _ _,
  intros R Q φ,
  ext _ ⟨uy, _⟩,
  change φ.app x ⟨_, _⟩ = φ.app x ⟨_, _⟩,
  congr' 2,
  ext1 ⟨j⟩,
  refl,
  change R.map (𝟙 x) (uy walking_pair.right) = uy walking_pair.right,
  rw [R.map_id, types_id_apply],
  intros R Q φ t ht,
  ext c u D ⟨fx, _⟩,
  dsimp,
  rw ← ht,
  change (((R.map (has_hom.hom.op (fx walking_pair.left)) ≫ t.app _) u)).app D _ = (t.app c u).app D _,
  rw t.naturality,
  change (t.app c u).app D _ = (t.app c u).app D _,
  congr' 1,
  rw subtype.ext,
  ext1 ⟨j⟩,
  apply id_comp,
  refl,
end

instance : cartesian_closed.{u} (Cᵒᵖ ⥤ Type u) :=
{ closed := λ P, exponentiables P }