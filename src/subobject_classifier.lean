import category_theory.limits.shapes
import category_theory.limits.types
import pullbacks

universes v u

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]

-- Start with a long instance. Probably belongs in mathlib if it wasn't so poorly done
def has_equalizers_of_pullbacks_and_binary_products
  (C : Type u) [𝒞 : category.{v} C] [has_binary_products.{v} C] [has_pullbacks.{v} C] :
  has_equalizers.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := pullback (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left))
                      (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right)),
        π :=
        { app := λ x, walking_parallel_pair.cases_on x pullback.fst (pullback.fst ≫ F.map walking_parallel_pair_hom.left),
          naturality' :=
          begin
            intros, cases f, dsimp, rw id_comp,
              dsimp, rw id_comp,
              have q := @pullback.condition _ _ _ _ _
                        (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left))
                        (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right)) _,
              have l: pullback.fst ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left)  ≫ limits.prod.fst =
                      pullback.snd ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right) ≫ limits.prod.fst,
                rw ← assoc, rw ← assoc, rw q,
              simp [limit.lift_π, limit.lift_π] at l,
              have r: pullback.fst ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left) ≫ limits.prod.snd =
                     pullback.snd ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right) ≫ limits.prod.snd,
                rw ← assoc, rw ← assoc, rw q,
              simp at r, rw r, rw l,
            cases X, dsimp, rw id_comp, simp,
                     dsimp, rw id_comp, simp
          end } },
      is_limit :=
      { lift :=
        begin
          intro c, apply pullback.lift (c.π.app _) (c.π.app _),
          apply limit.hom_ext,
          rintro (_ | _), all_goals { simp [assoc, limit.lift_π] }
        end,
        fac' :=
        begin
          rintro _ (_ | _), simp, simp
        end,
        uniq' :=
        begin
          dsimp, intros c _ J,
          have J1 := J walking_parallel_pair.zero, dsimp at J1,
          apply limit.hom_ext, conv in (_ = _) { rw limit.lift_π },
          intro j, cases j, dunfold pullback_cone.mk, dsimp, rw ← J1,
          dunfold pullback_cone.mk, dsimp, rw ← J1,
          show m ≫ pullback.snd = m ≫ pullback.fst,
          symmetry,
          have q := @pullback.condition _ _ _ _ _
                    (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left))
                    (prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right)) _,
          have l: pullback.fst ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.left)  ≫ limits.prod.fst =
                  pullback.snd ≫ prod.lift (𝟙 (F.obj walking_parallel_pair.zero)) (F.map walking_parallel_pair_hom.right) ≫ limits.prod.fst,
            rw ← assoc, rw ← assoc, rw q,
          simp [limit.lift_π, limit.lift_π] at l,
          rw l, dunfold pullback_cone.mk, dsimp, rw ← limit.w _ _,
          swap, exact walking_cospan.left,
          swap, exact walking_cospan.hom.inl,
          rw ← assoc, rw J1, refl
        end
      }
      }}
}

-- Define what it means for χ to classify the mono f.
-- Should this be a class? I don't think so but maybe
-- Maybe it should be a structure though
-- def classifies {C : Type u} [𝒞 : category.{v} C]
--   {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) {f : U ⟶ X} (h : mono f) (χ : X ⟶ Ω)
--   := Σ' (k : U ⟶ Ω₀) (comm : k ≫ true = f ≫ χ),
--         is_limit (pullback_cone.mk _ _ comm)

structure classifying {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f) (χ : X ⟶ Ω) :=
(k : U ⟶ Ω₀)
(commutes : k ≫ true = f ≫ χ)
(forms_pullback' : is_limit (pullback_cone.mk _ _ commutes))
restate_axiom classifying.forms_pullback'

-- A subobject classifier is a mono which classifies every mono uniquely
class has_subobject_classifier (C : Type u) [𝒞 : category.{v} C] :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
(truth_mono' : @mono C 𝒞 _ _ truth)
(classifier_of : ∀ {U X} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f), X ⟶ Ω)
(classifies' : ∀ {U X} {f : U ⟶ X} (h : mono f), classifying truth h (classifier_of h))
(uniquely' : ∀ {U X} {f : U ⟶ X} (h : mono f) (χ₁ : X ⟶ Ω),
            classifying truth h χ₁ → χ₁ = classifier_of h)

lemma mono_id (A : C) : @mono _ 𝒞 _ _ (𝟙 A) := ⟨λ _ _ _ w, by simp at w; exact w⟩

variables [has_subobject_classifier C]

-- convenience defs
@[reducible]
def subobj.Ω : C :=
@has_subobject_classifier.Ω _ 𝒞 _
@[reducible]
def subobj.Ω₀ : C :=
@has_subobject_classifier.Ω₀ _ 𝒞 _
@[reducible]
def subobj.truth : subobj.Ω₀ ⟶ subobj.Ω :=
@has_subobject_classifier.truth _ 𝒞 _
@[reducible]
instance subobj.truth_mono : mono subobj.truth :=
@has_subobject_classifier.truth_mono' _ 𝒞 _
def subobj.classifier_of {U X : C} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f) : X ⟶ subobj.Ω :=
has_subobject_classifier.classifier_of h
def subobj.classifies {U X : C} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f) : classifying subobj.truth h (subobj.classifier_of h) :=
has_subobject_classifier.classifies' h
def subobj.square.k {U X : C} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f) : U ⟶ subobj.Ω₀ :=
(subobj.classifies h).k
def subobj.square.commutes {U X : C} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f) :
  subobj.square.k h ≫ subobj.truth = f ≫ subobj.classifier_of h :=
(subobj.classifies h).commutes
def subobj.square.is_pullback {U X : C} {f : U ⟶ X} (h : @mono C 𝒞 _ _ f) :
  is_limit (pullback_cone.mk _ _ (subobj.square.commutes h)) :=
(subobj.classifies h).forms_pullback
restate_axiom has_subobject_classifier.uniquely'

-- subobject classifier => there is a terminal object.
-- TODO: make a lemma saying subobj.Ω₀ = ⊤_C
-- NB: together with the commented out instance at the top and the instance below that, this shows
-- that every category with a subobj classifier and pullbacks has binary products and equalizers
-- It's a todo in mathlib to show binary products implies finite products, and we have
-- in mathlib and these together imply finite limits exist.
-- So when we define (elem) toposes, we only need assume pullbacks and subobj classifier
-- and not all finite limits (but of course cartesian closed is still necessary and such)
instance terminal_of_subobj : @has_terminal C 𝒞 :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := subobj.Ω₀,
        π := {app := λ p, pempty.elim p}},
      is_limit :=
      { lift := λ s, (subobj.classifies (mono_id s.X)).1,
        fac' := λ _ j, j.elim,
        uniq' := λ s m J,
        begin
          clear J,
          obtain ⟨χ₁, r1, r2⟩ := subobj.classifies (mono_id s.X),
          rw ← cancel_mono subobj.truth,
          rw r1, rw id_comp,
          apply has_subobject_classifier.uniquely (mono_id s.X),
          refine {k := m, commutes := _, forms_pullback' := _},
          rw id_comp,
          refine ⟨λ c, c.π.app walking_cospan.right, λ c, _, λ c, _⟩,
          apply pi_app_left (pullback_cone.mk m (𝟙 s.X) _) c,
          rw ← cancel_mono subobj.truth,
          rw assoc, rw pullback_cone.condition c, refl, apply_instance,
          erw comp_id,
          intros g₂ j, specialize j walking_cospan.right, erw comp_id at j,
          exact j, apply_instance
        end } } }
}

lemma terminal_obj (C : Type u) [𝒞 : category.{v} C] [has_subobject_classifier C] : terminal C = subobj.Ω₀ := rfl

instance unique_to_Ω₀ {C : Type u} [𝒞 : category.{v} C] [has_subobject_classifier C] (P : C) : unique (P ⟶ subobj.Ω₀) :=
limits.unique_to_terminal P

/--
A --> 1
|   / |
|  /  |
v /   v
B --> Ω
-/
def mono_is_equalizer {A B : C} {m : A ⟶ B} (hm : @mono C 𝒞 _ _ m) :
  is_limit (fork.of_ι m (begin rw ← subobj.square.commutes hm, rw ← assoc, congr' 1 end) : fork (subobj.classifier_of hm) (terminal.from B ≫ subobj.truth)) :=
{ lift := λ s, (subobj.square.is_pullback hm).lift (pullback_cone.mk (terminal.from s.X) (fork.ι s) (begin erw fork.condition s, rw ← assoc, congr' 1 end)),
  fac' := λ s,
    begin
      intro j, cases j,
        simp, erw (subobj.square.is_pullback hm).fac _ walking_cospan.right, refl,
      simp, rw ← assoc, erw (subobj.square.is_pullback hm).fac _ walking_cospan.right,
      rw ← s.w walking_parallel_pair_hom.left, refl
    end,
  uniq' := λ s n J,
  begin
    apply pullback_cone.hom_ext (subobj.square.is_pullback hm), apply subsingleton.elim,
    erw (subobj.square.is_pullback hm).fac, erw J walking_parallel_pair.zero, refl,
  end
}

-- TODO: move
lemma equalizer_is_mono {A B E : C} {f : A ⟶ B}
  {i₁ i₂ : B ⟶ E} (w : f ≫ i₁ = f ≫ i₂) (t : is_limit (fork.of_ι f w)) :
@mono C 𝒞 _ _ f :=
begin
  split,
  intros,
  apply t.hom_ext,
  intro j, cases j,
  simpa, simp, rw ← assoc, simp [w_1]
end

-- TODO: move
lemma epi_equalizer_is_iso {A B E : C} {f : A ⟶ B} (ef : @epi C 𝒞 _ _ f)
  {i₁ i₂ : B ⟶ E} {w : f ≫ i₁ = f ≫ i₂} (t : is_limit (fork.of_ι f w)) :
is_iso f :=
{ inv := t.lift (fork.of_ι (𝟙 B) (begin simp only [id_comp], rwa ← cancel_epi f end)),
  inv_hom_id' := t.fac (fork.of_ι (𝟙 B) _) walking_parallel_pair.zero,
  hom_inv_id' := begin haveI := equalizer_is_mono w t, rw ← cancel_mono f, rw assoc, erw t.fac (fork.of_ι (𝟙 B) _) walking_parallel_pair.zero, simp end
}

lemma balanced {A B : C} {f : A ⟶ B} (ef : @epi C 𝒞 _ _ f) (mf : mono f) : is_iso f :=
epi_equalizer_is_iso ef (mono_is_equalizer mf)