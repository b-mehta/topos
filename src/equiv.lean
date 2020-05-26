import power
import category_theory.epi_mono
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.finite_products

universes v u

open category_theory category_theory.category category_theory.limits

namespace category_theory

variables {C : Type u} [category.{v} C] [has_finite_limits.{v} C]

variables {A R : C}

-- Definitions 1.3.6
structure relation (R A : C) :=
(a : R ⟶ A)
(b : R ⟶ A)
[jointly_mono : mono (prod.lift a b)]

variable (rel : relation.{v} R A)

instance joint_mono : mono (prod.lift rel.a rel.b) :=
rel.jointly_mono

class reflexive :=
(r : A ⟶ R)
(cancel_a : r ≫ rel.a = 𝟙 _)
(cancel_b : r ≫ rel.b = 𝟙 _)

lemma reflexive_prop [reflexive rel] :
  reflexive.r rel ≫ prod.lift rel.a rel.b = prod.lift (𝟙 _) (𝟙 _) :=
begin
  apply prod.hom_ext;
  simp only [assoc, prod.lift_fst, prod.lift_snd, reflexive.cancel_a, reflexive.cancel_b],
end

class symmetric :=
(s : R ⟶ R)
(w₁ : s ≫ rel.a = rel.b)
(w₂ : s ≫ rel.b = rel.a)

lemma symmetric_idem [symmetric rel] : symmetric.s rel ≫ symmetric.s rel = 𝟙 _ :=
begin
  rw ← cancel_mono (prod.lift rel.a rel.b),
  apply prod.hom_ext;
  { simp only [assoc, id_comp, prod.lift_fst, prod.lift_snd, symmetric.w₁, symmetric.w₂] },
end
lemma symmetric_pair [symmetric rel] :
  symmetric.s rel ≫ prod.lift rel.a rel.b = prod.lift rel.b rel.a :=
begin
  apply prod.hom_ext;
  simp only [assoc, prod.lift_fst, prod.lift_snd, symmetric.w₁, symmetric.w₂],
end

def triples : C := pullback rel.b rel.a

def p : triples rel ⟶ R := pullback.fst
def q : triples rel ⟶ R := pullback.snd
@[reassoc]
lemma consistent : p rel ≫ rel.b = q rel ≫ rel.a := pullback.condition

class transitive :=
(t : triples rel ⟶ R)
(w₁ : t ≫ rel.a = p rel ≫ rel.a)
(w₂ : t ≫ rel.b = q rel ≫ rel.b)

lemma transitive_pair [transitive rel] :
  (transitive.t : triples rel ⟶ R) ≫ prod.lift rel.a rel.b = limits.prod.lift (p rel ≫ rel.a) (q rel ≫ rel.b) :=
begin
  apply prod.hom_ext,
  rw [assoc, prod.lift_fst, prod.lift_fst, transitive.w₁],
  rw [assoc, prod.lift_snd, prod.lift_snd, transitive.w₂],
end

-- Proving the note in 1.3.6(e)
instance subsingleton_reflexive :
  subsingleton (reflexive rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  haveI := rel.jointly_mono,
  rw ← cancel_mono (limits.prod.lift rel.a rel.b),
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

instance subsingleton_symmetric :
  subsingleton (symmetric rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  haveI := rel.jointly_mono,
  rw ← cancel_mono (limits.prod.lift rel.a rel.b),
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

instance subsingleton_transitive :
  subsingleton (transitive rel) :=
⟨begin
  rintros ⟨r₁, h₁r₁, h₂r₁⟩ ⟨r₂, h₁r₂, h₂r₂⟩,
  congr,
  haveI := rel.jointly_mono,
  rw ← cancel_mono (limits.prod.lift rel.a rel.b),
  apply prod.hom_ext,
  { simp [h₁r₁, h₁r₂] },
  { simp [h₂r₁, h₂r₂] },
end⟩

-- That was nice and easy!

-- Show a kernel pair is an equivalence relation.
@[simps]
def kernel_pair_relation {A B : C} (f : A ⟶ B) : relation.{v} (pullback f f) A :=
{ a := pullback.fst,
  b := pullback.snd,
  jointly_mono :=
  ⟨λ Z g h eq, begin apply pullback.hom_ext, simpa using eq =≫ limits.prod.fst, simpa using eq =≫ limits.prod.snd end⟩ }

instance {A B : C} (f : A ⟶ B) : reflexive (kernel_pair_relation f) :=
{ r := pullback.lift (𝟙 _) (𝟙 _) rfl,
  cancel_a := pullback.lift_fst _ _ _,
  cancel_b := pullback.lift_snd _ _ _ }

instance {A B : C} (f : A ⟶ B) : symmetric (kernel_pair_relation f) :=
{ s := pullback.lift pullback.snd pullback.fst pullback.condition.symm,
  w₁ := pullback.lift_fst _ _ _,
  w₂ := pullback.lift_snd _ _ _ }

def tag' (n : ℕ) (A B : C) (f : A ⟶ B) : A ⟶ B := f

instance {A B : C} (f : A ⟶ B) : transitive (kernel_pair_relation f) :=
{ t := pullback.lift (p _ ≫ pullback.fst) (q _ ≫ (kernel_pair_relation f).b)
      (by { erw [assoc, assoc, pullback.condition, consistent_assoc, pullback.condition], refl }),
  w₁ := pullback.lift_fst _ _ _,
  w₂ := pullback.lift_snd _ _ _
}

-- Now we show the converse: any equivalence relation is a kernel pair.

lemma left_pb_comm [transitive rel] :
  (transitive.t : triples rel ⟶ _) ≫ prod.lift rel.a rel.b = prod.lift (p rel) (q rel ≫ rel.b) ≫ limits.prod.map rel.a (𝟙 _) :=
begin
  rw [prod.lift_map, comp_id, transitive_pair],
end

lemma right_pb_comm :
  q rel ≫ prod.lift rel.a rel.b =
prod.lift (p rel) (q rel ≫ rel.b) ≫ limits.prod.map rel.b (𝟙 _) :=
begin
  rw [prod.lift_map, comp_id],
  apply prod.hom_ext,
  { rw [assoc, prod.lift_fst, prod.lift_fst, consistent] },
  { rw [assoc, prod.lift_snd, prod.lift_snd] }
end

variables [has_subobject_classifier.{v} C] [is_cartesian_closed.{v} C]

def named : A ⟶ P A := hat (prod.lift rel.a rel.b)

def right_pb_square : is_limit (pullback_cone.mk _ _ (right_pb_comm rel)) :=
is_limit.mk'' _ $ λ c,
begin
  have c₁ := c.condition =≫ limits.prod.fst,
  rw [assoc, assoc, prod.lift_fst, limits.prod.map_fst] at c₁,
  have c₂ := c.condition =≫ limits.prod.snd,
  rw [assoc, assoc, prod.lift_snd, limits.prod.map_snd, comp_id] at c₂,
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

instance pbq_mono : mono (prod.lift (p rel) (q rel ≫ rel.b)) :=
pullback_mono_is_mono _ (right_pb_square rel)

def left_pb_square [symmetric rel] [transitive rel] : is_limit (pullback_cone.mk _ _ (left_pb_comm rel)) :=
is_limit.mk''' _ (category_theory.pbq_mono rel) $ λ c,
begin
  have c₁ := c.condition =≫ limits.prod.fst,
  rw [assoc, prod.lift_fst, assoc, limits.prod.map_fst] at c₁,
  have c₂ := c.condition =≫ limits.prod.snd,
  rw [assoc, prod.lift_snd, assoc, limits.prod.map_snd, comp_id] at c₂,
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

lemma relation_square_commutes [symmetric rel] [transitive rel] : rel.a ≫ named rel = rel.b ≫ named rel :=
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

-- variable (e : equivalence_rel rel)

theorem makes_kernel_pair [reflexive rel] [symmetric rel] [transitive rel] :
  is_limit (pullback_cone.mk _ _ (relation_square_commutes rel)) :=
is_limit.mk' _ $ λ c,
begin
  have frgr : c.fst ≫ hat _ = c.snd ≫ hat _ := c.condition,
  let ab' : sub (A ⨯ A) := sub.mk (prod.lift rel.a rel.b),
  have subs : pullback_sub (limits.prod.map c.fst (𝟙 _)) ab' = pullback_sub (limits.prod.map c.snd (𝟙 _)) ab',
    apply name_bijection.right_inv.injective,
    change name_subobject (pullback_sub (limits.prod.map c.fst (𝟙 A)) ab') = name_subobject (pullback_sub (limits.prod.map c.snd (𝟙 A)) ab'),
    rw [name_pullback ab', name_pullback ab'],
    exact frgr,
  have subs2 : pullback_sub (prod.lift c.fst c.snd) ab' = pullback_sub (prod.lift c.snd c.snd) ab',
    have s₁ : prod.lift c.fst c.snd = prod.lift (𝟙 _) c.snd ≫ limits.prod.map c.fst (𝟙 _),
      rw [prod.lift_map, id_comp, comp_id],
    have s₂ : prod.lift c.snd c.snd = prod.lift (𝟙 _) c.snd ≫ limits.prod.map c.snd (𝟙 _),
      rw [prod.lift_map, id_comp, comp_id],
    rw [s₁, s₂, pullback_sub_comp, subs, pullback_sub_comp],
  have subs3 : pullback_sub (prod.lift c.snd c.snd) ab' = ⊤,
    have s₃ : prod.lift c.snd c.snd = c.snd ≫ prod.lift (𝟙 _) (𝟙 _),
      apply prod.hom_ext;
      simp only [prod.lift_fst, prod.lift_snd, assoc, comp_id],
    rw s₃,
    suffices : pullback_sub (prod.lift (𝟙 _) (𝟙 _)) ab' = ⊤,
      rw [pullback_sub_comp, this, pullback_top],
    rw [eq_top_iff, top_eq_top],
    refine ⟨pullback.lift (reflexive.r rel) (𝟙 _) _, _⟩,
      rw [id_comp], apply reflexive_prop,
    apply pullback.lift_snd,
  rw [← subs2, eq_top_iff] at subs3,
  obtain ⟨t, ht⟩ : { t : c.X ⟶ pullback (prod.lift _ _) _ // t ≫ pullback.snd = 𝟙 _ } := raised_factors subs3,
  let u := t ≫ pullback.fst,
  have t' : u ≫ prod.lift rel.a rel.b = prod.lift c.fst c.snd,
    rw [assoc, pullback.condition, reassoc_of ht],
  have t₁ := t' =≫ limits.prod.fst,
    rw [assoc, prod.lift_fst, prod.lift_fst] at t₁,
  have t₂ := t' =≫ limits.prod.snd,
    rw [assoc, prod.lift_snd, prod.lift_snd] at t₂,
  refine ⟨u, t₁, t₂, λ m m₁ m₂, _⟩,
  rw [← cancel_mono (prod.lift rel.a rel.b), t'],
  apply prod.hom_ext,
  { simpa only [assoc, prod.lift_fst] using m₁ },
  { simpa only [assoc, prod.lift_snd] using m₂ },
end

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
pushout_cocone.is_colimit.mk _
  (λ s, coprod.desc (pushout_cocone.inl s) (pushout_cocone.inr s))
  (λ s, coprod.inl_desc _ _)
  (λ s, coprod.inr_desc _ _)
$ λ s m w,
begin
  apply coprod.hom_ext,
  rw coprod.inl_desc, apply w walking_span.left,
  rw coprod.inr_desc, apply w walking_span.right,
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
