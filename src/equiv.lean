import power
import kernel_pair
import category_theory.epi_mono
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.finite_products

universes v u

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C : Type u} [category.{v} C] [has_finite_limits.{v} C]

-- A relation should be mono, but we restrict this at the use site instead.
abbreviation relation (R A : C) := R ⟶ A ⨯ A

namespace relation

variables {A R : C}

abbreviation a (r : relation R A) : R ⟶ A := r ≫ limits.prod.fst
abbreviation b (r : relation R A) : R ⟶ A := r ≫ limits.prod.snd
def of_pair (f : R ⟶ A) (g : R ⟶ A) : relation R A := prod.lift f g
@[simp] lemma of_pair_a (f : R ⟶ A) (g : R ⟶ A) : (of_pair f g).a = f := prod.lift_fst _ _
@[simp] lemma of_pair_b (f : R ⟶ A) (g : R ⟶ A) : (of_pair f g).b = g := prod.lift_snd _ _

end relation

variables {A R : C} (rel : relation.{v} R A)

class reflexive :=
(r : A ⟶ R)
(cancel_a : r ≫ rel.a = 𝟙 _)
(cancel_b : r ≫ rel.b = 𝟙 _)

attribute [simp] reflexive.cancel_a reflexive.cancel_b

lemma reflexive_prop [reflexive rel] :
  reflexive.r rel ≫ rel = prod.lift (𝟙 _) (𝟙 _) :=
begin
  apply prod.hom_ext;
  simp only [assoc, prod.lift_fst, prod.lift_snd, reflexive.cancel_a, reflexive.cancel_b],
end

class symmetric :=
(s : R ⟶ R)
(w₁ : s ≫ rel.a = rel.b)
(w₂ : s ≫ rel.b = rel.a)

@[reassoc] lemma symmetric_idem [mono rel] [symmetric rel] : symmetric.s rel ≫ symmetric.s rel = 𝟙 _ :=
begin
  rw ← cancel_mono rel,
  apply prod.hom_ext;
  { simp only [assoc, id_comp, prod.lift_fst, prod.lift_snd, symmetric.w₁, symmetric.w₂] },
end
@[reassoc] lemma symmetric_pair [symmetric rel] :
  symmetric.s rel ≫ rel = prod.lift rel.b rel.a :=
begin
  apply prod.hom_ext;
  simp only [assoc, prod.lift_fst, prod.lift_snd, symmetric.w₁, symmetric.w₂],
end

-- represents triples (x,y,z) such that Rxy and Ryz
def triples : C := pullback rel.b rel.a

-- get Rxy out of the triple
def p : triples rel ⟶ R := pullback.fst
-- get Ryz out of the triple
def q : triples rel ⟶ R := pullback.snd

@[reassoc] lemma consistent : p rel ≫ rel.b = q rel ≫ rel.a := pullback.condition

/-- Show Rxz holds if Rxy and Ryz hold -/
class transitive :=
(t : triples rel ⟶ R)
(w₁ : t ≫ rel.a = p rel ≫ rel.a)
(w₂ : t ≫ rel.b = q rel ≫ rel.b)

lemma transitive_pair [transitive rel] :
  (transitive.t : triples rel ⟶ R) ≫ rel = prod.lift (p rel ≫ rel.a) (q rel ≫ rel.b) :=
begin
  apply prod.hom_ext,
  rw [assoc, prod.lift_fst, transitive.w₁],
  rw [assoc, prod.lift_snd, transitive.w₂],
end

-- Proving the note in 1.3.6(e)
instance subsingleton_reflexive [mono rel] :
  subsingleton (reflexive rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  rw ← cancel_mono rel,
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

instance subsingleton_symmetric [mono rel] :
  subsingleton (symmetric rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  rw ← cancel_mono rel,
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

instance subsingleton_transitive [mono rel] :
  subsingleton (transitive rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  rw ← cancel_mono rel,
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

-- That was nice and easy!

section equiv_of_kernel_pair

variables {B : C} {f : A ⟶ B} {a b : R ⟶ A} (k : is_kernel_pair f a b)

instance of_kernel_pair_mono (k : is_kernel_pair f a b) : mono (relation.of_pair a b) :=
⟨λ Z g h eq, begin
  apply k.is_limit.hom_ext,
  apply (pullback_cone.mk a b _).equalizer_ext,
  { simpa [relation.of_pair] using eq =≫ limits.prod.fst },
  { simpa [relation.of_pair] using eq =≫ limits.prod.snd },
end⟩

instance (k : is_kernel_pair f a b) : reflexive (relation.of_pair a b) :=
{ r := (k.lift' (𝟙 _) (𝟙 _) rfl).1,
  cancel_a := by rw [relation.of_pair_a, (k.lift' (𝟙 _) (𝟙 _) rfl).2.1],
  cancel_b := by rw [relation.of_pair_b, (k.lift' (𝟙 _) (𝟙 _) rfl).2.2] }

instance (k : is_kernel_pair f a b) : symmetric (relation.of_pair a b) :=
{ s := (k.lift' b a k.comm.symm).1,
  w₁ := by rw [relation.of_pair_a, relation.of_pair_b, (k.lift' b a k.comm.symm).2.1],
  w₂ := by rw [relation.of_pair_a, relation.of_pair_b, (k.lift' b a k.comm.symm).2.2] }

instance (k : is_kernel_pair f a b) : transitive (relation.of_pair a b) :=
{ t :=
  begin
    apply (k.lift' (p _ ≫ (relation.of_pair a b).a) (q _ ≫ (relation.of_pair a b).b) _).1,
    have : (relation.of_pair a b).a ≫ f = (relation.of_pair a b).b ≫ f,
      simp [k.comm],
    erw [assoc, this, pullback.condition_assoc, this, assoc, assoc, assoc],
    refl,
  end,
  w₁ := by simp only [relation.of_pair_a, (k.lift' _ _ _).2.1],
  w₂ := by simp only [relation.of_pair_b, (k.lift' _ _ _).2.2] }

end equiv_of_kernel_pair

-- Now we show the converse: any equivalence relation is a kernel pair.

lemma left_pb_comm [transitive rel] :
  (transitive.t : triples rel ⟶ _) ≫ rel = prod.lift (p rel) (q rel ≫ rel.b) ≫ limits.prod.map rel.a (𝟙 _) :=
begin
  rw [prod.lift_map, comp_id, transitive_pair],
end

lemma right_pb_comm :
  q rel ≫ rel =
prod.lift (p rel) (q rel ≫ rel.b) ≫ limits.prod.map rel.b (𝟙 _) :=
begin
  rw [prod.lift_map, comp_id],
  apply prod.hom_ext,
  { rw [assoc, prod.lift_fst, consistent] },
  { rw [assoc, prod.lift_snd] }
end

variables [has_subobject_classifier.{v} C] [cartesian_closed.{v} C]

def named [mono rel] : A ⟶ P A := hat rel

def right_pb_square [mono rel] : is_limit (pullback_cone.mk _ _ (right_pb_comm rel)) :=
is_limit.mk'' _ $ λ c,
begin
  have c₁ := c.condition =≫ limits.prod.fst,
  rw [assoc, assoc, limits.prod.map_fst] at c₁,
  have c₂ := c.condition =≫ limits.prod.snd,
  rw [assoc, assoc, limits.prod.map_snd, comp_id] at c₂,
  refine ⟨pullback.lift (c.snd ≫ limits.prod.fst) c.fst _, _, λ m m₁ m₂, _⟩,
  { rw [assoc, c₁] },
  { change pullback.lift _ _ _ ≫ prod.lift _ _ = _,
    apply prod.hom_ext,
    { rw [assoc, prod.lift_fst], apply pullback.lift_fst },
    { rw [assoc, prod.lift_snd, ← assoc, ← c₂], congr' 1, apply pullback.lift_snd } },
  { apply pullback.hom_ext,
    { erw [pullback.lift_fst, ← m₂, assoc, prod.lift_fst], refl },
    { rw pullback.lift_snd, exact m₁ } }
end

instance pbq_mono [mono rel] : mono (prod.lift (p rel) (q rel ≫ rel.b)) :=
pullback_mono_is_mono _ (right_pb_square rel)

def left_pb_square [mono rel] [symmetric rel] [transitive rel] : is_limit (pullback_cone.mk _ _ (left_pb_comm rel)) :=
is_limit.mk''' _ (category_theory.pbq_mono rel) $ λ c,
begin
  have c₁ := c.condition =≫ limits.prod.fst,
  rw [assoc, assoc, limits.prod.map_fst] at c₁,
  have c₂ := c.condition =≫ limits.prod.snd,
  rw [assoc, assoc, limits.prod.map_snd, comp_id] at c₂,
  have comm : (c.snd ≫ limits.prod.fst ≫ symmetric.s rel) ≫ rel.b = c.fst ≫ rel.a,
    rw [assoc, assoc, symmetric.w₂, c₁],
  let yRz : c.X ⟶ R := pullback.lift (c.snd ≫ limits.prod.fst ≫ symmetric.s rel) c.fst comm ≫ transitive.t,
  refine ⟨pullback.lift (c.snd ≫ limits.prod.fst) yRz _, _⟩,
  { simp only [assoc, transitive.w₁, p, pullback.lift_fst_assoc, symmetric.w₁] },
  { change _ ≫ prod.lift _ _ = _,
    apply prod.hom_ext,
    { simp only [assoc, prod.lift_fst, p, pullback.lift_fst] },
    { simp only [assoc, prod.lift_snd, q, pullback.lift_snd_assoc, transitive.w₂, c₂] } },
end

lemma relation_square_commutes [mono rel] [symmetric rel] [transitive rel] :
  rel.a ≫ named rel = rel.b ≫ named rel :=
begin
  rw [named, ← hat_natural_left, ← hat_natural_left],
  transitivity (hat (prod.lift (p rel) (q rel ≫ rel.b))),
  { apply lifting ((left_pb_square rel).lift _) (pullback.lift _ _ (left_pb_comm rel)) _ _,
    apply ((left_pb_square rel).fac _ walking_cospan.right),
    apply pullback.lift_snd },
  { apply lifting (pullback.lift _ _ (right_pb_comm rel)) ((right_pb_square rel).lift _) _ _,
    apply pullback.lift_snd,
    apply (right_pb_square rel).fac _ walking_cospan.right }
end

def makes_kernel_pair [mono rel] [reflexive rel] [symmetric rel] [transitive rel] :
  is_limit (pullback_cone.mk _ _ (relation_square_commutes rel)) :=
is_limit.mk' _ $ λ c,
begin
  have frgr : c.fst ≫ hat _ = c.snd ≫ hat _ := c.condition,
  let ab' : subq (A ⨯ A) := ⟦sub.mk' rel⟧,
  have subs : (subq.pullback (limits.prod.map c.fst (𝟙 _))).obj ab' = (subq.pullback (limits.prod.map c.snd (𝟙 _))).obj ab',
    apply name_bijection.right_inv.injective,
    change name_subobject ((subq.pullback (limits.prod.map c.fst (𝟙 _))).obj ab') = name_subobject ((subq.pullback (limits.prod.map c.snd (𝟙 _))).obj ab'),
    rw [name_pullback ab', name_pullback ab'],
    exact frgr,
  have subs2 : (subq.pullback (prod.lift c.fst c.snd)).obj ab' = (subq.pullback (prod.lift c.snd c.snd)).obj ab',
    have s₁ : prod.lift c.fst c.snd = prod.lift (𝟙 _) c.snd ≫ limits.prod.map c.fst (𝟙 _),
      rw [prod.lift_map, id_comp, comp_id],
    have s₂ : prod.lift c.snd c.snd = prod.lift (𝟙 _) c.snd ≫ limits.prod.map c.snd (𝟙 _),
      rw [prod.lift_map, id_comp, comp_id],
    rw [s₁, s₂, subq.pullback_comp, subs, subq.pullback_comp],
  have subs3 : (subq.pullback (prod.lift c.snd c.snd)).obj ab' = ⊤,
    have s₃ : prod.lift c.snd c.snd = c.snd ≫ prod.lift (𝟙 _) (𝟙 _),
      apply prod.hom_ext;
      simp only [prod.lift_fst, prod.lift_snd, assoc, comp_id],
    rw s₃,
    suffices : (subq.pullback (prod.lift (𝟙 _) (𝟙 _))).obj ab' = ⊤,
      rw [subq.pullback_comp, this, subq.pullback_top],
    rw [eq_top_iff],
    refine ⟨sub.hom_mk _ _⟩,
    refine pullback.lift (reflexive.r rel) (𝟙 _) _,
      rw [id_comp], apply reflexive_prop,
    apply pullback.lift_snd,
  rw [← subs2, eq_top_iff] at subs3,
  obtain ⟨t, ht⟩ : { t : c.X ⟶ pullback rel _ // t ≫ pullback.snd = 𝟙 _ } := raised_factors subs3,
  let u := t ≫ pullback.fst,
  have t' : u ≫ rel = prod.lift c.fst c.snd,
    rw [assoc, pullback.condition, reassoc_of ht],
  have t₁ := t' =≫ limits.prod.fst,
    rw [assoc, prod.lift_fst] at t₁,
  have t₂ := t' =≫ limits.prod.snd,
    rw [assoc, prod.lift_snd] at t₂,
  refine ⟨u, t₁, t₂, λ m m₁ m₂, _⟩,
  rw [← cancel_mono rel, t'],
  apply prod.hom_ext,
  { simpa only [assoc, prod.lift_fst] using m₁ },
  { simpa only [assoc, prod.lift_snd] using m₂ },
end

def equiv_to_kernel_pair [mono rel] [reflexive rel] [symmetric rel] [transitive rel] :
  is_kernel_pair (named rel) rel.a rel.b :=
{ comm := relation_square_commutes rel,
  is_limit := makes_kernel_pair rel }

namespace disjoint

lemma A242_commutes {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono f] :
  g ≫ singleton_arrow Z = f ≫ hat (prod.lift f g) :=
begin
  rw [← seven_six_one, ← hat_natural_left],
  apply lifting (pullback.lift (𝟙 _) (prod.lift (𝟙 _) g) _) pullback.fst _ _,
  rw [id_comp, prod.lift_map, id_comp, comp_id],
  rw pullback.lift_snd,
  rw [← cancel_mono (limits.prod.map f (𝟙 _)), ← pullback.condition, assoc, prod.lift_map, id_comp, comp_id],
  apply_instance,
end

def kata_is_pullback {X Y Z U V : C} {f : X ⟶ Y} {g : X ⟶ Z} {u₁ : Y ⟶ U} {u₂ : Z ⟶ U}
  {v₁ : Y ⟶ V} {v₂ : Z ⟶ V} (hu : f ≫ u₁ = g ≫ u₂) (hv : f ≫ v₁ = g ≫ v₂)
  (is_pullback : is_limit (pullback_cone.mk _ _ hu))
  (is_pushout : is_colimit (pushout_cocone.mk _ _ hv)) :
  is_limit (pullback_cone.mk _ _ hv) :=
is_limit.mk' _ $ λ s,
begin
  let h : V ⟶ U := is_pushout.desc (pushout_cocone.mk _ _ hu),
  have hh₁ : v₁ ≫ h = u₁ := is_pushout.fac _ walking_span.left,
  have hh₂ : v₂ ≫ h = u₂ := is_pushout.fac _ walking_span.right,
  have comm : s.fst ≫ u₁ = s.snd ≫ u₂,
    rw [← hh₁, s.condition_assoc, hh₂],
  refine ⟨is_pullback.lift (pullback_cone.mk _ _ comm), is_pullback.fac _ walking_cospan.left, is_pullback.fac _ walking_cospan.right, λ m m₁ m₂, _⟩,
  apply is_pullback.hom_ext,
  apply (pullback_cone.mk f g hu).equalizer_ext,
  erw [m₁, is_pullback.fac _ walking_cospan.left], refl,
  erw [m₂, is_pullback.fac _ walking_cospan.right], refl,
end

def A242_pullback {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [m : mono f] :
  is_limit (pullback_cone.mk _ _ (A242_commutes f g)) :=
is_limit.mk''' _ m $ λ c,
begin
  have prop : c.fst ≫ _ = c.snd ≫ hat _ := c.condition,
  rw [← seven_six_one, ← hat_natural_left] at prop,
  let π₂ : pullback (prod.lift f g) (limits.prod.map c.snd (𝟙 _)) ⟶ _ := pullback.snd,
  refine ⟨(how_inj_is_hat prop).hom ≫ pullback.fst, _⟩,
  have hq : _ ≫ π₂ = _ := very_inj prop,
  have pbc₁ : (pullback.fst ≫ _) ≫ _ = (π₂ ≫ _) ≫ _ := pullback.condition =≫ limits.prod.fst,
    rw [assoc, prod.lift_fst, assoc, limits.prod.map_fst] at pbc₁,
  erw [assoc, pbc₁, reassoc_of hq, prod.lift_fst_assoc, id_comp]
end

def A243_part1 {W X Y Z : C} {g : W ⟶ Y} {d : Y ⟶ Z} {f : W ⟶ X} {e : X ⟶ Z} [mono f] (comm : g ≫ d = f ≫ e)
  (t : is_colimit (pushout_cocone.mk _ _ comm)) : mono d :=
begin
  have : _ = singleton_arrow _ := t.fac (pushout_cocone.mk (singleton_arrow Y) (hat (prod.lift f g)) (A242_commutes _ _)) walking_span.left,
  apply mono_of_mono_fac this,
end

def A243_part2 {W X Y Z : C} {g : W ⟶ Y} {d : Y ⟶ Z} {f : W ⟶ X} {e : X ⟶ Z} [mono f] (comm : g ≫ d = f ≫ e)
  (t : is_colimit (pushout_cocone.mk _ _ comm)) : is_limit (pullback_cone.mk _ _ comm) :=
kata_is_pullback (A242_commutes _ _) _ (A242_pullback _ _) t

def pushout_coprod {A B : C} :
  is_colimit (pushout_cocone.mk coprod.inl coprod.inr (subsingleton.elim _ _) : pushout_cocone (default (⊥_ C ⟶ A)) (default (⊥_ C ⟶ B))) :=
pushout_cocone.is_colimit.mk _ _ _
  (λ s, coprod.desc s.inl s.inr)
  (λ s, coprod.inl_desc _ _)
  (λ s, coprod.inr_desc _ _) $
λ s m w₁ w₂,
begin
  apply coprod.hom_ext,
  { rwa [coprod.inl_desc] },
  { rwa [coprod.inr_desc] },
end

instance mono_coprod_inr {A B : C} : mono (coprod.inl : A ⟶ A ⨿ B) := A243_part1 _ pushout_coprod
instance mono_coprod_inl {A B : C} : mono (coprod.inr : B ⟶ A ⨿ B) :=
begin
  suffices : (coprod.inr : B ⟶ A ⨿ B) ≫ (coprod.braiding A B).hom = coprod.inl,
    exact mono_of_mono_fac this,
  simp only [coprod.inr_desc, coprod.braiding_hom]
end

def intersect_coprojections {A B : C} : pullback (coprod.inl : A ⟶ A ⨿ B) coprod.inr ≅ ⊥_ C :=
begin
  have : is_limit (pullback_cone.mk (default (⊥_ C ⟶ A)) (default (⊥_ C ⟶ B)) _) := A243_part2 _ pushout_coprod,
  apply is_limit.cone_point_unique_up_to_iso (limit.is_limit _) this,
end

end disjoint

end category_theory
