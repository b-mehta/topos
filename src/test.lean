import category_theory.limits.shapes
import category_theory.limits.types
import pullbacks

universes v v₂ u

open category_theory category_theory.category category_theory.limits

-- Mathlib PR 1998:
-- def has_binary_products_of_terminal_and_pullbacks
--   (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_pullbacks.{v} C] :
--   has_binary_products.{v} C :=
-- { has_limits_of_shape :=
--   { has_limit := λ F,
--     { cone :=
--       { X := pullback (terminal.from (F.obj walking_pair.left))
--                      (terminal.from (F.obj walking_pair.right)),
--         π := nat_trans.of_homs (λ x, walking_pair.cases_on x pullback.fst pullback.snd)},
--       is_limit :=
--       { lift := λ c, pullback.lift ((c.π).app walking_pair.left)
--                                    ((c.π).app walking_pair.right)
--                                    (subsingleton.elim _ _),
--         fac' := λ s c, walking_pair.cases_on c (limit.lift_π _ _) (limit.lift_π _ _),
--         uniq' := begin
--                    intros _ _ J,
--                    have J1 := J walking_pair.left, rw ← J1,
--                    have J2 := J walking_pair.right, rw ← J2,
--                    clear J J1 J2,
--                    apply limit.hom_ext, conv in (_ = _) { rw limit.lift_π },
--                    intro j, cases j, refl, refl,
--                    dsimp [pullback_cone.mk], apply subsingleton.elim,
--                  end}}}}

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
          intro c, rintro (_ | _), simp, simp
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
def classifies {C : Type u} [𝒞 : category.{v} C]
  {Ω Ω₀ U X : C} (true : Ω₀ ⟶ Ω) {f : U ⟶ X} (h : mono f) (χ : X ⟶ Ω)
  := Σ' (k : U ⟶ Ω₀) (comm : k ≫ true = f ≫ χ),
        is_limit (pullback_cone.mk _ _ comm)

-- A subobject classifier is a mono which classifies every mono uniquely
class has_subobject_classifier (C : Type u) [𝒞 : category.{v} C] :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
(truth_mono' : mono truth)
(classifies' : Π {U X} {f : U ⟶ X} (h : mono f), Σ χ, classifies truth h χ)
(uniquely' : Π {U X} {f : U ⟶ X} (h : mono f) (χ₁ χ₂ : X ⟶ Ω),
            classifies truth h χ₁ → classifies truth h χ₂ → χ₁ = χ₂)

variables {C : Type u} [𝒞 : category.{v} C]

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
@[reducible]
def subobj.classifies {U X} {f : U ⟶ X} (h : mono f) :
  Σ χ, classifies subobj.truth h χ :=
@has_subobject_classifier.classifies' C 𝒞 _ _ _ _ h
restate_axiom has_subobject_classifier.uniquely'

-- subobject classifier => there is a terminal object.
-- TODO: make a lemma saying subobj.Ω₀ = ⊤_C
-- NB: together with the commented out instance at the top and the instance below that, this shows
-- that every category with a subobj classifier and pullbacks has binary products and equalizers
-- It's a todo in mathlib to show binary products implies finite products, and we have
-- in mathlib and these together imply finite limits exist.
-- So when we define (elem) toposes, we only need assume pullbacks and subobj classifier
-- and not all finite limits (but of course cartesian closed is still necessary and such)
instance terminal_of_subobj (C : Type u) [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] [has_subobject_classifier C] : @has_terminal C 𝒞 :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := subobj.Ω₀,
        π := {app := λ p, pempty.elim p}},
      is_limit :=
      { lift := λ s, (subobj.classifies (mono_id s.X)).2.1,
        fac' := λ _ j, j.elim,
        uniq' :=
        begin
          intros s m J, dsimp at m, clear J,
          obtain ⟨χ₁, r⟩ := subobj.classifies (mono_id s.X),
          rw ← cancel_mono subobj.truth,
          apply has_subobject_classifier.uniquely (mono_id s.X), swap, rwa [r.2.1, id_comp],
          refine ⟨m, _, _⟩,
          rw id_comp, refine ⟨λ c, c.π.app walking_cospan.right, λ c, _, _⟩,
          rintro (_ | _ | _),
          show (c.π).app walking_cospan.right ≫ m = (c.π).app walking_cospan.left,
          rw ← cancel_mono subobj.truth,
          rw assoc, rw pullback_cone.condition c, apply_instance,
          dunfold pullback_cone.mk, rw comp_id, dunfold pullback_cone.mk, dsimp,
          rw ← assoc, conv_rhs {rw ← cone.w c walking_cospan.hom.inr}, rw assoc, refl,
          intros c g₂ j, specialize j walking_cospan.right, dsimp [pullback_cone.mk] at j,
          rw comp_id at j, exact j,
          apply_instance
        end}}}
}