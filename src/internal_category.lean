import category_theory.limits.shapes.pullbacks
import category_theory.limits.limits
import category_theory.types
import category_theory.limits.types
import category_theory.monad.algebra
import category_theory.category.Cat
import tactic.equiv_rw
import category.pullbacks
import data.sigma

namespace category_theory

open category_theory category_theory.category category_theory.limits

universes v u

section
variables (A : Type u) [category.{v} A]

structure internal_category_struct :=
(C₀ C₁ C₂ : A) -- object of objects, object of morphisms, object of composable pairs (i.e (f,g) where f ∘ g makes sense)
(trg src : C₁ ⟶ C₀) -- get codomain and domain of morphisms
(ident : C₀ ⟶ C₁) -- get identity morphism on object
(first_hom comp second_hom : C₂ ⟶ C₁) -- decompose composite
(comp_comm : first_hom ≫ src = second_hom ≫ trg)
(comp_pb : is_limit (pullback_cone.mk _ _ comp_comm))
(ident_trg : ident ≫ trg = 𝟙 C₀)
(ident_src : ident ≫ src = 𝟙 C₀)
(comp_trg : comp ≫ trg = first_hom ≫ trg)
(comp_src : comp ≫ src = second_hom ≫ src)
end

open internal_category_struct

attribute [simp, reassoc] internal_category_struct.ident_src internal_category_struct.ident_trg
attribute [simp, reassoc] internal_category_struct.comp_comm internal_category_struct.comp_trg internal_category_struct.comp_src

section
variables {C : Type u} [category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
@[simp] lemma mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (pullback_cone.mk fst snd eq).fst = fst := rfl
@[simp] lemma mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
  (pullback_cone.mk fst snd eq).snd = snd := rfl
end

section
variables {A : Type u} [category.{v} A] (c : internal_category_struct A)
-- given f,g with the source of f = target of g (ie f ∘ g or g ≫ f makes sense), form the composable pair (f,g)

def make_pair {Q : A} (f g : Q ⟶ c.C₁)
  (composable : f ≫ c.src = g ≫ c.trg) :
Q ⟶ c.C₂ :=
(pullback_cone.is_limit.lift' c.comp_pb _ _ composable).1

@[simp, reassoc]
lemma compose_l {Q : A} (f g : Q ⟶ c.C₁)
  (cmp : f ≫ c.src = g ≫ c.trg) :
make_pair c f g cmp ≫ c.first_hom = f :=
(pullback_cone.is_limit.lift' c.comp_pb _ _ cmp).2.1

@[simp, reassoc]
lemma compose_r {Q : A} (f g : Q ⟶ c.C₁)
  (cmp : f ≫ c.src = g ≫ c.trg) :
make_pair c f g cmp ≫ c.second_hom = g :=
(pullback_cone.is_limit.lift' c.comp_pb _ _ cmp).2.2

@[reassoc] lemma compose_natural {Q R : A} (f g : R ⟶ c.C₁) (h : Q ⟶ R) (composable : f ≫ c.src = g ≫ c.trg) :
  h ≫ make_pair c f g composable = make_pair c (h ≫ f) (h ≫ g) (by simp [*]) :=
begin
  apply pullback_cone.is_limit.hom_ext c.comp_pb;
  simp,
end
end

section
variables {A : Type u} [category.{v} A] [has_finite_limits A] (c : internal_category_struct A)

/--
object of composable triples (f,g,h) where f ∘ (g ∘ h) makes sense
(as should (f ∘ g) ∘ h)
constructed as the pullback of (f,g₁) and (g₂,h) where g₁ = g₂
-/
def internal_category_struct.C₃ : A :=
pullback c.second_hom c.first_hom

open limits.pullback

/-- The first pair `(f, g₁)` of the triple `(f, g₁ = g₂, h)` -/
abbreviation internal_category_struct.left_pair : c.C₃ ⟶ c.C₂ := fst
/-- The second pair `(g₂, h)` of the triple `(f, g₁ = g₂, h)` -/
abbreviation internal_category_struct.right_pair : c.C₃ ⟶ c.C₂ := snd

/-- The first homomorphism `f` of the triple `(f, g, h)` -/
abbreviation internal_category_struct.trip_first_hom : c.C₃ ⟶ c.C₁ := c.left_pair ≫ c.first_hom
/-- The first homomorphism `h` of the triple `(f, g, h)` -/
abbreviation internal_category_struct.trip_third_hom : c.C₃ ⟶ c.C₁ := c.right_pair ≫ c.second_hom

/-- Prove `g₁ = g₂` in the triple `(f, g₁ = g₂, h)` -/
@[reassoc] lemma trip_snd_eq : c.left_pair ≫ c.second_hom = c.right_pair ≫ c.first_hom := condition

/-- Map `(f, g, h)` to `(f ∘ g, h)` -/
abbreviation internal_category_struct.comp_left_pair : c.C₃ ⟶ c.C₂ :=
make_pair c (c.left_pair ≫ c.comp) c.trip_third_hom $
by rw [assoc, c.comp_src, trip_snd_eq_assoc, assoc, c.comp_comm]

/-- Map `(f, g, h)` to `(f, g ∘ h)` -/
abbreviation internal_category_struct.comp_right_pair : c.C₃ ⟶ c.C₂ :=
make_pair c c.trip_first_hom (c.right_pair ≫ c.comp) $
by rw [assoc, assoc, c.comp_trg, c.comp_comm, trip_snd_eq_assoc]

end
def element {X : Type u} : (⊤_ (Type u) ⟶ X) ≃ X :=
{ to_fun := λ f, f ⟨λ t, t.elim, λ t, t.elim⟩,
  inv_fun := λ x _, x,
  left_inv := λ f,
  begin
    ext1 ⟨_, _⟩,
    dsimp,
    congr,
    ext ⟨⟩,
  end,
  right_inv := λ x, rfl }

@[simp] lemma element_natural {X Y : Type u} (f : ⊤_ _ ⟶ X) (g : X ⟶ Y) : element (f ≫ g) = g (element f) :=
rfl

@[simp] lemma element_unelement {X : Type u} (x : X) : element (element.symm x) = x :=
rfl

def category_struct_of_internal_category_struct_type (c : internal_category_struct.{u} (Type u)) :
  category_struct c.C₀ :=
{ hom := λ X Y, {h : c.C₁ // c.src h = Y ∧ c.trg h = X},
  id := λ X, ⟨c.ident X, congr_fun c.ident_src X, congr_fun c.ident_trg X⟩,
  comp := λ X Y Z f g,
  begin
    refine ⟨_, _, _⟩,
    { refine element (make_pair c (element.symm ↑f) (element.symm ↑g) _ ≫ c.comp),
      rw ← element.apply_eq_iff_eq,
      dsimp, rw [f.prop.1, g.prop.2] },
    { change (make_pair _ _ _ _ ≫ c.comp ≫ c.src) _ = Z,
      rw [c.comp_src, compose_r_assoc],
      exact g.prop.1 },
    { change (make_pair _ _ _ _ ≫ c.comp ≫ c.trg) _ = X,
      rw [c.comp_trg, compose_l_assoc],
      exact f.prop.2 },
  end }

structure internal_category (A : Type u) [category.{v} A] [has_finite_limits.{v} A] extends internal_category_struct.{v} A :=
(assoc : internal_category_struct.comp_left_pair _ ≫ comp = internal_category_struct.comp_right_pair _ ≫ comp)
(id_comp : make_pair _ (𝟙 _) (src ≫ ident) (by simp) ≫ comp = 𝟙 C₁)
(comp_id : make_pair _ (trg ≫ ident) (𝟙 _) (by simp) ≫ comp = 𝟙 C₁)

@[simps]
def internal_category_struct_type_of_category_struct (C : Type u) [category_struct.{u} C] : internal_category_struct.{u} (Type u) :=
{ C₀ := C,
  C₁ := Σ (X Y : C), X ⟶ Y,
  C₂ := Σ (X Y Z : C), (X ⟶ Y) × (Y ⟶ Z),
  src := λ f, f.1,
  trg := λ f, f.2.1,
  ident := λ x, ⟨x, x, 𝟙 _⟩,
  first_hom := λ x, ⟨x.2.1, x.2.2.1, x.2.2.2.2⟩,
  comp := λ x, ⟨x.1, x.2.2.1, x.2.2.2.1 ≫ x.2.2.2.2⟩,
  second_hom := λ x, ⟨x.1, x.2.1, x.2.2.2.1⟩,
  comp_comm := rfl,
  comp_pb :=
  begin
    refine construct_type_pb _ _,
    rintros ⟨Y, X, f⟩ ⟨Z, Y, g⟩ _,
    dsimp at a, subst a,
    refine ⟨⟨Z, Y, X, g, f⟩, rfl, rfl, _⟩,
    rintro ⟨Z', Y', X', g', f'⟩ h₁ h₂,
    dsimp at h₁ h₂,
    cases h₁,
    cases h₂,
    refl,
  end,
  ident_trg := rfl,
  ident_src := rfl,
  comp_trg := rfl,
  comp_src := rfl }

section

def tag (α : Type*) (n : ℕ) (t : α) := t

def alt_pb (C : Type u) [category_struct.{u} C] := Σ (W X Y Z : C), (W ⟶ X) × (X ⟶ Y) × (Y ⟶ Z)
def alt_π₁ (C : Type u) [category_struct.{u} C] :
  alt_pb C ⟶ (internal_category_struct_type_of_category_struct C).C₂ :=
begin
  intro x,
  refine ⟨x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2⟩,
end
def alt_π₂ (C : Type u) [category_struct.{u} C] :
  alt_pb C ⟶ (internal_category_struct_type_of_category_struct C).C₂ :=
begin
  intro x,
  refine ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1⟩,
end

lemma alt_comm (C : Type u) [category_struct.{u} C] :
  alt_π₁ C ≫ (internal_category_struct_type_of_category_struct C).second_hom = alt_π₂ C ≫ (internal_category_struct_type_of_category_struct C).first_hom :=
rfl

def is_pb (C : Type u) [category_struct.{u} C] :
  is_limit (pullback_cone.mk _ _ (alt_comm C)) :=
begin
  apply construct_type_pb _,
  rintros ⟨X, Y, Z, f, g⟩ ⟨W, X, Y, h, f⟩ _,
  dsimp [internal_category_struct_type_of_category_struct] at a,
  injection a with a₁ a₂,
  subst a₁,
  rw heq_iff_eq at a₂,
  injection a₂ with a₃ a₄,
  subst a₃,
  rw heq_iff_eq at a₄,
  subst a₄,
  refine ⟨⟨_, _, _, _, h, f, g⟩, _, _, _⟩,
  refl,
  refl,
  rintro ⟨_, _, _, _, _, _, _⟩ k l,
  cases k,
  cases l,
  refl,
end

end
-- def internal_category_struct.C₃ : A :=
-- pullback c.second_hom c.first_hom

def to_C₃ (C : Type u) [category_struct.{u} C] : alt_pb C ≅ (internal_category_struct_type_of_category_struct C).C₃ :=
limits.is_limit.cone_point_unique_up_to_iso (is_pb C) (limit.is_limit _)

@[simps]
def internal_category_type_of_category (C : Type u) [category.{u} C] : internal_category.{u} (Type u) :=
{ id_comp :=
  begin
    ext1 ⟨X, Y, f⟩,
    change (⟨_, _, _⟩ : Σ (X Y : C), X ⟶ Y) = _,
    congr' 2,
    apply id_comp,
  end,
  comp_id :=
  begin
    ext1 ⟨X, Y, f⟩,
    change (⟨X, Y, f ≫ 𝟙 _⟩ : Σ (X Y : C), X ⟶ Y) = (⟨X, Y, f⟩ : Σ (X Y : C), X ⟶ Y),
    congr' 2,
    apply comp_id,
  end,
  assoc :=
  begin
    haveI := is_iso.of_iso (to_C₃ C),
    rw [← cancel_epi (to_C₃ C).hom, compose_natural_assoc, compose_natural_assoc],
    change make_pair _ (pullback.lift _ _ _ ≫ pullback.fst ≫ _) (pullback.lift _ _ _ ≫ pullback.snd ≫ _) _ ≫ _ =
           make_pair _ (pullback.lift _ _ _ ≫ pullback.fst ≫ _) (pullback.lift _ _ _ ≫ pullback.snd ≫ _) _ ≫ _,
    simp_rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc],
    ext1 ⟨W, X, Y, Z, f, g, h⟩,
    change (⟨W, Z, f ≫ g ≫ h⟩ : Σ (X Y : C), X ⟶ Y) = (⟨W, Z, (f ≫ g) ≫ h⟩ : Σ (X Y : C), X ⟶ Y),
    simp,
  end,
  ..internal_category_struct_type_of_category_struct C }

instance category_of_internal_category_type (c : internal_category.{u} (Type u)) :
  small_category c.C₀ :=
{ comp_id' :=
  begin
    rintros X Y ⟨f, rfl, rfl⟩,
    ext1,
    change element (make_pair _ (element.symm f) _ _ ≫ c.comp) = f,
    equiv_rw (@element c.C₁).symm at f,
    rw equiv.apply_eq_iff_eq,
    change make_pair c.to_internal_category_struct f (element.symm (element ((f ≫ c.src) ≫ c.ident))) _ ≫ c.comp = _,
    simp_rw [equiv.symm_apply_apply, assoc],
    have := f ≫= c.id_comp,
    simp_rw [compose_natural_assoc, comp_id] at this,
    exact this,
  end,
  id_comp' :=
  begin
    rintros X Y ⟨f, rfl, rfl⟩,
    ext1,
    change element (make_pair _ _ (element.symm f) _ ≫ c.comp) = f,
    equiv_rw (@element c.C₁).symm at f,
    rw equiv.apply_eq_iff_eq,
    change make_pair c.to_internal_category_struct (element.symm (element ((f ≫ c.trg) ≫ c.ident))) f _ ≫ c.comp = _,
    simp_rw [equiv.symm_apply_apply, assoc],
    have := f ≫= c.comp_id,
    simp_rw [compose_natural_assoc, comp_id] at this,
    exact this,
  end,
  assoc' :=
  begin
    rintros W X Y Z ⟨f, rfl, rfl⟩ ⟨g, rfl, fg⟩ ⟨h, rfl, gh⟩,
    ext1,
    equiv_rw (@element c.C₁).symm at f,
    equiv_rw (@element c.C₁).symm at g,
    equiv_rw (@element c.C₁).symm at h,
    change element (make_pair _ _ _ _ ≫ c.comp) = element (make_pair _ _ _ _ ≫ c.comp),
    rw equiv.apply_eq_iff_eq,
    change make_pair _ (element.symm (element (make_pair _ (element.symm (element f)) (element.symm (element g)) _ ≫ c.comp))) (element.symm (element h)) _ ≫ c.comp =
           make_pair _ (element.symm (element f)) (element.symm (element (make_pair _ (element.symm (element g)) (element.symm (element h)) _ ≫ c.comp))) _ ≫ c.comp,
    simp_rw [equiv.symm_apply_apply],
    change make_pair _ (make_pair _ f g _ ≫ c.comp) h _ ≫ c.comp = make_pair _ f (make_pair _ g h _ ≫ c.comp) _ ≫ c.comp,
    have := pullback.lift (make_pair _ f g _) (make_pair _ g h _) _ ≫= c.assoc,
      rotate,
      { rw [equiv.symm_symm, ← element_natural _ c.trg, ← element_natural _ c.src, equiv.apply_eq_iff_eq] at fg,
        rw fg },
      { rw [equiv.symm_symm, ← element_natural _ c.trg, ← element_natural _ c.src, equiv.apply_eq_iff_eq] at gh,
        rw gh },
      { rw [compose_l, compose_r] },
    rw [← assoc, ← assoc] at this,
    convert this;
    apply pullback_cone.is_limit.hom_ext c.comp_pb;
    simp,
  end,
  ..category_struct_of_internal_category_struct_type c.to_internal_category_struct}

structure internal_functor {A : Type u} [category.{v} A] [has_finite_limits A] (c d : internal_category A) :=
(obj : c.C₀ ⟶ d.C₀)
(map : c.C₁ ⟶ d.C₁)
(map_src : map ≫ d.src = c.src ≫ obj)
(map_trg : map ≫ d.trg = c.trg ≫ obj)
(ident_map : c.ident ≫ map = obj ≫ d.ident)
(comp_map : make_pair _ (first_hom _ ≫ map) (second_hom _ ≫ map) (by simp [map_src, map_trg]) ≫ d.comp = c.comp ≫ map)

attribute [simp, reassoc] internal_functor.map_src internal_functor.map_trg internal_functor.ident_map internal_functor.comp_map
variables {A : Type u} [category.{v} A] [has_finite_limits A]

def internal_id (c : internal_category A) : internal_functor c c :=
{ obj := 𝟙 _,
  map := 𝟙 _,
  map_src := by simp,
  map_trg := by simp,
  ident_map := by simp,
  comp_map :=
  begin
    simp only [comp_id],
    convert id_comp _,
    apply pullback_cone.is_limit.hom_ext c.comp_pb;
    simp,
  end }

def internal_comp {c d e : internal_category A} (F : internal_functor c d) (G : internal_functor d e) :
  internal_functor c e :=
{ obj := F.obj ≫ G.obj,
  map := F.map ≫ G.map,
  map_src := by simp,
  map_trg := by simp,
  ident_map := by simp,
  comp_map :=
  begin
    rw [← F.comp_map_assoc, ← G.comp_map, compose_natural_assoc],
    simp,
  end }

@[ext] def internal_functor_ext {c d : internal_category A} (F G : internal_functor c d) (h₁ : F.obj = G.obj) (h₂ : F.map = G.map) : F = G :=
begin
  cases F, cases G,
  congr; assumption
end
@[simps]
def make_functor (c d : internal_category.{u} (Type u)) (F : internal_functor c d) :
  c.C₀ ⥤ d.C₀ :=
{ obj := F.obj,
  map := λ X Y f,
  begin
    refine ⟨F.map f.1, _, _⟩,
    { change (F.map ≫ d.src) _ = _,
      rw F.map_src,
      dsimp,
      rw f.prop.1 },
    { change (F.map ≫ d.trg) _ = _,
      rw F.map_trg,
      dsimp,
      rw f.prop.2 },
  end,
  map_id' := λ X,
  begin
    ext1,
    change (c.ident ≫ F.map) X = (F.obj ≫ d.ident) X,
    rw F.ident_map,
  end,
  map_comp' :=
  begin
    rintros _ _ Z ⟨f, rfl, rfl⟩ ⟨g, rfl, fg⟩,
    ext1,
    change F.map (element (make_pair _ (element.symm f) (element.symm g) _ ≫ c.comp)) = element (make_pair _ (element.symm (F.map f)) (element.symm (F.map g)) _ ≫ d.comp),
    equiv_rw (@element c.C₁).symm at f,
    equiv_rw (@element c.C₁).symm at g,
    have : g ≫ c.trg = f ≫ c.src,
      rw ← element.apply_eq_iff_eq,
      simpa using fg,
    simp_rw [← element_natural _ F.map, equiv.symm_apply_apply],
    rw [element.apply_eq_iff_eq, assoc, ← F.comp_map, compose_natural_assoc],
    simp,
  end }

def internalise_functor (C D : Type u) [small_category C] [small_category D] (F : C ⥤ D) :
  internal_functor (internal_category_type_of_category C) (internal_category_type_of_category D) :=
{ obj := F.obj,
  map := λ XYf, ⟨F.obj XYf.1, F.obj XYf.2.1, F.map XYf.2.2⟩,
  map_src := rfl,
  map_trg := rfl,
  ident_map :=
  begin
    ext1 X,
    dsimp,
    simp only [functor.map_id],
    refl,
  end,
  comp_map :=
  begin
    ext1 ⟨X, Y, Z, f, g⟩,
    dsimp [internal_category_struct_type_of_category_struct],
    change (⟨F.obj X, ⟨F.obj Z, F.map f ≫ F.map g⟩⟩ : Σ (X Y : D), X ⟶ Y) = (⟨F.obj X, ⟨F.obj Z, F.map (f ≫ g)⟩⟩ : Σ (X Y : D), X ⟶ Y),
    simp,
  end }

instance cat_of_int_cat : category (internal_category.{v} A) :=
{ hom := internal_functor,
  id := internal_id,
  comp := λ X Y Z, internal_comp,
  id_comp' := λ X Y f,
  begin
    apply internal_functor_ext;
    apply id_comp,
  end,
  comp_id' := λ X Y f,
  begin
    apply internal_functor_ext;
    apply comp_id,
  end,
  assoc' := λ c₁ c₂ c₃ c₄ f g h,
  begin
    apply internal_functor_ext;
    apply assoc,
  end }

@[simps]
def internal_equiv : internal_category (Type u) ⥤ Cat :=
{ obj := λ c, Cat.of c.C₀,
  map := make_functor,
  map_id' := λ c,
  begin
    refine functor.ext (λ X, rfl) _,
    intros,
    apply subtype.ext,
    dsimp [make_functor],
    simpa only [id_comp, comp_id],
  end,
  map_comp' := λ c d e f g,
  begin
    refine functor.ext (λ X, rfl) _,
    intros,
    apply subtype.ext,
    dsimp,
    simpa,
  end }

@[simps]
def internal_inv : Cat.{u} ⥤ internal_category (Type u) :=
{ obj := λ c, internal_category_type_of_category c.α,
  map := λ c d f, internalise_functor _ _ f }

-- -- set_option pp.all true
-- def internal_equivalence : internal_category.{u} (Type u) ≌ Cat.{u u} :=
-- { functor :=
--   { obj := λ c, Cat.of c.C₀,
--     map := make_functor,
--     map_id' := λ c,
--     begin
--       refine functor.ext (λ X, rfl) _,
--       intros,
--       apply subtype.ext,
--       dsimp [make_functor],
--       simpa only [id_comp, comp_id],
--     end,
--     map_comp' := λ c d e f g,
--     begin
--       refine functor.ext (λ X, rfl) _,
--       intros,
--       apply subtype.ext,
--       dsimp,
--       simpa,
--     end },
--   inverse :=
--   { obj := λ c, internal_category_type_of_category c.α,
--     map := λ c d f, internalise_functor _ _ f },
--   unit_iso :=
--   begin
--     -- apply nat_iso.of_components _ _,
--     -- intro X,
--     -- dsimp,
--     -- change X ≅ _,
--     -- dsimp [Cat.of, bundled.of, Cat.str, category_theory.category_of_internal_category_type, internal_category_type_of_category],
--     -- refine ⟨_, _, _, _⟩,
--     -- refine ⟨𝟙 _, λ x, ⟨X.src x, X.trg x, sorry⟩, rfl, rfl, _, _⟩,
--     -- ext1,
--     -- dsimp [internal_category_struct_type_of_category_struct],
--     -- change (⟨(X.ident ≫ X.src) x, (X.ident ≫ X.trg) x, _⟩ : Σ (X₁ Y₁ : X.to_internal_category_struct.C₀), X₁ ⟶ Y₁) = _,
--     sorry,
--   end,
--   counit_iso :=
--   begin
--     apply nat_iso.of_components _ _,
--     intro X,
--     apply eq_to_iso,
--     cases X,
--     dsimp [Cat.of, bundled.of],
--     congr,

--   end
-- }

end category_theory