import category_theory.limits.shapes
import category_theory.limits.types
import category_theory.types
import category_theory.limits.shapes.binary_products
import category_theory.limits.functor_category
import category_theory.functor_category
import sieve
import subobject_classifier
import sheaf

universes v u

open category_theory category_theory.category category_theory.limits

section reflects
variables {C : Type u} [category.{v} C]

variables {J K : Type v} [small_category J] [small_category K]

variables {F : J ⥤ K ⥤ C}

@[simps]
def cone_of_pointwise_limit (c : Π k, cone (F.flip.obj k)) (t : Π k, is_limit (c k)) : cone F :=
{ X :=
  { obj := λ k, (c k).X,
    map := λ k₁ k₂ f, (t k₂).lift { X := (c k₁).X, π := (c k₁).π ≫ F.flip.map f },
    map_id' := λ k, ((t k).uniq _ _ (by simp)).symm,
    map_comp' := λ k₁ k₂ k₃ f₁ f₂, ((t k₃).uniq _ _ (by simp)).symm },
  π :=
  { app := λ j,
    { app := λ k, (c k).π.app j },
    naturality' := λ j₁ j₂ f,
    begin
      ext x,
      exact (c x).π.naturality f,
    end } }.

def pointwise_cone_forms_limit (c : Π k, cone (F.flip.obj k)) (t : Π k, is_limit (c k)) :
  is_limit (cone_of_pointwise_limit c t) :=
{ lift := λ s,
  { app := λ k,
    begin
      refine (t k).lift ⟨s.X.obj k, _⟩,
      refine ⟨λ j, (s.π.app j).app k, λ j₁ j₂ f, _⟩,
      erw [functor.flip_obj_map, functor.const.obj_map, cone.functor_w, id_comp],
    end,
    naturality' := λ k₁ k₂ f,
    begin
      apply (t k₂).hom_ext _,
      simp,
    end },
  uniq' := λ s m w,
  begin
    ext,
    dsimp,
    apply (t x).hom_ext,
    simp [(t x).fac, ← w],
  end }.

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

@[simps]
def exponential_functor (F G : C ⥤ Type u) : C ⥤ Type u :=
{ obj := λ A, coyoneda.obj (opposite.op A) ⨯ F ⟶ G,
  map := λ X Y f g, limits.prod.map (coyoneda.map f.op) (𝟙 _) ≫ g,
  map_comp' := λ X Y Z f g,
  begin
    ext1,
    simp [prod_map_comp_id],
  end }.

variable (C)
@[simps]
def presheaf.classifier : Cᵒᵖ ⥤ Type u :=
{ obj := λ A, sieve A.unop,
  map := λ A B f S, S.pullback f.unop,
  map_id' := λ A,
  begin
    ext1 S,
    dsimp,
    ext1,
    ext1,
    erw [sieve.mem_pullback2, category.comp_id],
    simpa,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext1 S,
    dsimp,
    ext1,
    ext1,
    erw [sieve.mem_pullback2],
    simp only [sieve.mem_pullback2, sieve.mem_pullback],
    rw ← assoc,
    apply iff.rfl, -- it should be possible to shuffle definitions so both of these are simp
  end }

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
    rintros f ⟨_, _⟩ Z g,
    refine ⟨Q.map g.op w, _⟩,
    dsimp,
    rw P.map_comp,
    change _ = P.map _ _,
    rw ← h,
    exact congr_fun (i.naturality g.op) w,
  end }.

-- lemma set_classifier_u {U X : Type u} {f : U ⟶ X} {χ₁ : X ⟶ ulift Prop} (q : classifying truth f χ₁) :
  -- ∀ x, (χ₁ x).down ↔ ∃ (a : U), f a = x :=
-- begin
  -- obtain ⟨ka, la, ma⟩ := q,
  -- intro x,
  -- split, rintro,
  -- { let g := ma.lift (pullback_cone.mk (𝟙 _) (λ _, x) (by simp [ulift.ext_iff, function.funext_iff, a, truth])),
    -- refine ⟨g punit.star, _⟩,
    -- have : (g ≫ f) _ = (λ _, x) _ := congr_fun (ma.fac _ walking_cospan.right) punit.star,
    -- exact this },
  -- rintro ⟨t, rfl⟩, have : _ = _ := congr_fun la t, simp at this, rw ← this, trivial,
-- end

noncomputable def presheaf.is_classifier : is_subobject_classifier (presheaf.truth C) :=
{ classifier_of := presheaf.classify C,
  classifies' := λ Q P i hi,
  { top := { app := λ _ _, punit.star },
    comm :=
    begin
      ext A x f,
      change true ↔ _,
      rw true_iff,
      exact ⟨Q.map f.hom.op x, congr_fun (i.naturality f.hom.op) x⟩,
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
    ext1 f,
    have hχc : has_pullback_top (i.app c) (χ.app c) ((presheaf.truth C).app c) := preserves_hpb ((evaluation _ (Type u)).obj c) hχ,
    dsimp at hχc,
    have hχf := preserves_hpb ((evaluation _ (Type u)).obj (opposite.op f.left)) hχ,
    dsimp at hχf,
    dsimp [presheaf.classify],
    change (∃ (y : Q.obj (opposite.op f.left)), i.app (opposite.op f.left) y = P.map f.hom.op x) ↔ f ∈ (χ.app c x).arrows,
    obtain ⟨kac, lac, mac⟩ := hχc,
    obtain ⟨kaf, laf, maf⟩ := hχf,
    split,
      rintro ⟨y, hy⟩,
      have hy₂ := congr_fun laf y,
      dsimp at hy₂,
      rw hy at hy₂,
      have hy₃ := congr_fun (χ.naturality f.hom.op) x,
      dsimp at hy₃,
      rw hy₃ at hy₂,
      have : over.mk (𝟙 f.left) ∈ sieve.pullback (χ.app c x) f.hom,
        rw ←hy₂,
        trivial,
      change over.mk (𝟙 f.left ≫ f.hom) ∈ (χ.app c x).arrows at this,
      rwa [id_comp, over.mk_hom_id] at this,
    intro hf,
    obtain ⟨l, hl₁, hl₂⟩ := pullback_cone.is_limit.lift' maf (𝟙 _) (λ _, P.map f.hom.op x) _,
    refine ⟨l punit.star, _⟩,
    have := congr_fun hl₂ punit.star,
    exact this,
    ext1 ⟨⟩,
    dsimp,
    have hy₃ := congr_fun (χ.naturality f.hom.op) x,
    dsimp at hy₃,
    rw hy₃,
    symmetry,
    rw eq_top_iff,
    intros t ht,
    rw sieve.mem_pullback2,
    apply sieve.subs,
    exact hf,
  end }.

noncomputable def presheaf_has_subobj_classifier : has_subobject_classifier.{u} (Cᵒᵖ ⥤ Type u) :=
{ Ω := _, Ω₀ := _, truth := _, is_subobj_classifier := presheaf.is_classifier C }

-- def subfunctor (P : Cᵒᵖ ⥤ Type u)
-- def make_subfunctor (P R : Cᵒᵖ ⥤ Type u) (θ : R ⟶ P) [mono θ] : Cᵒᵖ ⥤ Type u

-- def make_equivalence (F G H : C ⥤ Type u₁) : ((prod_functor.obj F).obj H ⟶ G) ≃ (H ⟶ exponential_functor G F) :=
-- { to_fun := λ f,
--   { app := λ c,
--     begin
--       intro x,
--       dsimp,
--       refine ⟨λ d i, _, _⟩,
--     end,
--     naturality' := sorry

--   }

-- }

-- def exponentiables (F : C ⥤ Type u₁) : exponentiable F :=
-- { is_adj :=
--   { right := adjunction.right_adjoint_of_equiv (λ H G, make_equivalence F G H)
--       begin
--         intros X' X Y f g,

--       end

--   }

-- }
-- instance : is_cartesian_closed.{u} (C ⥤ Type u) :=
-- { cart_closed := λ F, _

-- }