import category_theory.limits.shapes
import category_theory.limits.types

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
          intro c, apply pullback.lift ((c.π).app _) ((c.π).app _), 
          apply limit.hom_ext, 
          rintro (_ | _), all_goals { simp [assoc, limit.lift_π] }
        end,
        fac' :=
        begin
          intro c, rintro (_ | _), simp, refl, 
          simp, dsimp [pullback_cone.mk], rw ← c.π.naturality', 
          simp, apply id_comp
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
          rw ← assoc, rw J1, refl, 
        end
      }
      }}}

-- The pasting lemma for pullbacks. Something like this will invariably be useful
lemma pasting (C : Type u) [𝒞 : category.{v} C] [has_pullbacks.{v} C] {U V W X Y Z : C}
  (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ X) (k : V ⟶ Y) (l : W ⟶ Z) (m : X ⟶ Y) (n : Y ⟶ Z) 
  (left_comm : f ≫ k = h ≫ m) (right_comm : g ≫ l = k ≫ n)
  (right : is_limit (pullback_cone.mk g k right_comm)) :
  is_limit (pullback_cone.mk (f ≫ g) h (begin rw assoc, rw right_comm, rw ← assoc, rw left_comm, rw assoc end)) ≅ 
  is_limit (pullback_cone.mk f h left_comm) :=
{ hom := 
  begin
    intro entire, 
    refine ⟨λ c, _, _, _⟩, 
    { have new_cone_comm: (pullback_cone.fst c ≫ g) ≫ l = pullback_cone.snd c ≫ m ≫ n,
        rw assoc, rw ← pullback_cone.condition_assoc, rw right_comm,
      exact entire.lift (pullback_cone.mk (pullback_cone.fst c ≫ g) (pullback_cone.snd c) new_cone_comm) }, 
    { intro c,
      have new_cone_comm: (pullback_cone.fst c ≫ g) ≫ l = pullback_cone.snd c ≫ m ≫ n,
        rw assoc, rw ← pullback_cone.condition_assoc, rw right_comm,
      set new_cone := pullback_cone.mk (pullback_cone.fst c ≫ g) (pullback_cone.snd c) new_cone_comm,
      have coned := entire.fac' new_cone, 
      rintro (_ | _ | _), 
      { show entire.lift new_cone ≫ f = pullback_cone.fst c, 
        apply is_limit.hom_ext right, 
        rintro (_ | _ | _), 
        { rw assoc, exact coned walking_cospan.left },
        { show (entire.lift new_cone ≫ f) ≫ k = _ ≫ k, 
          rw assoc, conv_lhs {congr, skip, rw left_comm}, rw ← assoc, 
          have: entire.lift new_cone ≫ h = (pullback_cone.snd _) := coned walking_cospan.right,
          rw pullback_cone.condition c, rw this, refl },
        { show (entire.lift new_cone ≫ f) ≫ g ≫ l = _ ≫ g ≫ l, conv_lhs {rw ← assoc, congr, rw assoc},
        have: entire.lift new_cone ≫ f ≫ g = (new_cone.π).app walking_cospan.left := coned walking_cospan.left, 
        rw this, rw ← assoc, refl } },
      { show entire.lift new_cone ≫ h = pullback_cone.snd new_cone, exact coned walking_cospan.right },
      { show entire.lift new_cone ≫ f ≫ k = (c.π).app walking_cospan.one, 
        rw ← cone.w c walking_cospan.hom.inr, show entire.lift new_cone ≫ f ≫ k = pullback_cone.snd new_cone ≫ m, conv_lhs {congr, skip, rw left_comm},
        rw ← assoc, congr, exact coned walking_cospan.right } },
    { intros c r j, 
      have new_cone_comm: (pullback_cone.fst c ≫ g) ≫ l = pullback_cone.snd c ≫ m ≫ n,
        rw assoc, rw ← pullback_cone.condition_assoc, rw right_comm,
      set new_cone := pullback_cone.mk (pullback_cone.fst c ≫ g) (pullback_cone.snd c) new_cone_comm,
      apply entire.uniq' new_cone r,
      rintros (_ | _ | _), { show r ≫ f ≫ g = _ ≫ g, rw ← assoc, congr, exact j walking_cospan.left }, 
      { show r ≫ h = (new_cone.π).app walking_cospan.right, exact j walking_cospan.right },
      { show r ≫ (f ≫ g) ≫ l = (_ ≫ g) ≫ l, rw ← assoc, congr' 1, rw ← assoc, congr, exact j walking_cospan.left }
    }
  end
, inv := 
  begin
    intro left,
    refine ⟨λ c, _, λ c, _, λ c, _⟩, 
    { have new_cone_comm: pullback_cone.fst c ≫ l = (pullback_cone.snd c ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition, 
      have new_cone2_comm: (right.lift (pullback_cone.mk _ _ new_cone_comm)) ≫ k = (pullback_cone.snd c : c.X ⟶ X) ≫ m := right.fac' (pullback_cone.mk _ _ new_cone_comm) walking_cospan.right,
      exact left.lift (pullback_cone.mk _ _ new_cone2_comm)
    }, 
    { set π₁ : c.X ⟶ W := pullback_cone.fst c,
      set π₂ : c.X ⟶ X := pullback_cone.snd c,
      have new_cone_comm: π₁ ≫ l = (π₂ ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition, 
      have new_cone2_comm: (right.lift (pullback_cone.mk _ _ new_cone_comm)) ≫ k = π₂ ≫ m := right.fac' (pullback_cone.mk _ _ new_cone_comm) walking_cospan.right,
      set new_cone := pullback_cone.mk _ _ new_cone_comm,
      set new_cone2 := pullback_cone.mk _ _ new_cone2_comm,
      have left_fac := left.fac' new_cone2,
      have right_fac := right.fac' new_cone,
      have ll: left.lift new_cone2 ≫ f = right.lift new_cone := left_fac walking_cospan.left,
      have lr: left.lift new_cone2 ≫ h = π₂ := left_fac walking_cospan.right, 
      have rl: right.lift new_cone ≫ g = π₁ := right_fac walking_cospan.left,
      have rr: right.lift new_cone ≫ k = π₂ ≫ m := right_fac walking_cospan.right, 
      rintro (_ | _ | _), 
      show left.lift new_cone2 ≫ f ≫ g = π₁, rw ← assoc, rw ll, rw rl,
      show left.lift new_cone2 ≫ h = π₂, exact lr,
      rw ← cone.w c walking_cospan.hom.inl,
      show left.lift new_cone2 ≫ (f ≫ g) ≫ l = π₁ ≫ l, rw ← assoc, congr, rw ← assoc, rw ll, rw rl },
    { set π₁ : c.X ⟶ W := pullback_cone.fst c,
      set π₂ : c.X ⟶ X := pullback_cone.snd c,
      have new_cone_comm: π₁ ≫ l = (π₂ ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition, 
            set new_cone := pullback_cone.mk _ _ new_cone_comm,
      have new_cone2_comm: (right.lift new_cone) ≫ k = π₂ ≫ m := right.fac' new_cone walking_cospan.right,
      set new_cone2 := pullback_cone.mk _ _ new_cone2_comm,
      intros r J, 
      show r = left.lift new_cone2, 
      apply left.uniq' new_cone2 r, 
      have Jl: r ≫ f ≫ g = π₁ := J walking_cospan.left,
      have Jr: r ≫ h = π₂ := J walking_cospan.right,
      have J1: r ≫ (f ≫ g) ≫ l = (c.π).app walking_cospan.one := J walking_cospan.one,
      rintro (_ | _ | _), 
      show r ≫ f = right.lift new_cone, 
      apply right.uniq' new_cone, 
      rintro (_ | _ | _), rw assoc, exact Jl,
      show (r ≫ f) ≫ k = π₂ ≫ m, rw ← Jr, rw assoc, conv_rhs {rw assoc}, congr, exact left_comm, 
      show (r ≫ f) ≫ g ≫ l = (new_cone.π).app walking_cospan.one, rw ← cone.w new_cone walking_cospan.hom.inl, 
      show (r ≫ f) ≫ g ≫ l = π₁ ≫ l, rw ← assoc, congr, rw assoc, exact Jl,
      show r ≫ h = π₂, exact Jr, 
      show r ≫ f ≫ k = (new_cone2.π).app walking_cospan.one, rw ← cone.w new_cone2 walking_cospan.hom.inr, 
      show r ≫ f ≫ k = π₂ ≫ m, conv_lhs {congr, skip, rw left_comm}, rw ← assoc, rw Jr }
  end
, hom_inv_id' := subsingleton.elim _ _
, inv_hom_id' := subsingleton.elim _ _
}

namespace category_theory

-- Define what it means for χ to classify the mono f.
-- Should this be a class? I don't think so but maybe
def classifies {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] 
  {Ω Ω₀ : C} (true : Ω₀ ⟶ Ω) {U X : C} {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f) (χ : X ⟶ Ω)
  := Σ' (k : U ⟶ Ω₀) (comm : k ≫ true = f ≫ χ), is_limit (pullback_cone.mk _ _ comm)

-- A subobject classifier is a mono which classifies every mono uniquely
class has_subobject_classifier (C : Type u) [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] :=
(Ω Ω₀ : C)
(truth : Ω₀ ⟶ Ω)
(true_mono' : @mono _ 𝒞 _ _ truth)
(classifies' : Π {U X} {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f), Σ χ, classifies truth h χ)
(uniq' : Π {U X} {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f) (χ₁ χ₂ : X ⟶ Ω), classifies truth h χ₁ → classifies truth h χ₂ → χ₁ = χ₂)

variables {C : Type u} [𝒞 : category.{v} C] [@has_pullbacks C 𝒞] [has_subobject_classifier C]

-- convenience defs
def subobj.Ω : C := 
@has_subobject_classifier.Ω _ 𝒞 _ _
def subobj.Ω₀ : C := 
@has_subobject_classifier.Ω₀ _ 𝒞 _ _
def subobj.truth : subobj.Ω₀ ⟶ subobj.Ω := 
@has_subobject_classifier.truth _ 𝒞 _ _
instance subobj.truth_mono : mono subobj.truth := 
@has_subobject_classifier.true_mono' _ 𝒞 _ _
def subobj.classifies {U X} {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f) : 
  Σ χ, classifies subobj.truth h χ :=
@has_subobject_classifier.classifies' C 𝒞 _ _ _ _ _ h
def subobj.classifies_uniquely {U X} {f : U ⟶ X} (h : @mono _ 𝒞 _ _ f) (χ₁ χ₂ : X ⟶ subobj.Ω) :
  classifies subobj.truth h χ₁ → classifies subobj.truth h χ₂ → χ₁ = χ₂ :=
@has_subobject_classifier.uniq' _ 𝒞 _ _ _ _ _ h χ₁ χ₂

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
      { X := subobj.Ω₀
      , π := {app := λ p, pempty.elim p}
      }
    , is_limit := 
      { lift := 
        begin
          intro s, 
          have mid: mono (𝟙 s.X),
            split, intros, simp at w, assumption,
          exact (subobj.classifies mid).2.1
        end
      , fac' := λ s j, j.elim
      , uniq' :=
        begin
          intros s m J, dsimp at m, clear J, 
          have mid: mono (𝟙 s.X),
            split, intros, simp at w, assumption,
          obtain ⟨χ₁, r⟩ := subobj.classifies mid,
          set k := r.1,
          show m = k,
          rw ← cancel_mono subobj.truth, 
          apply subobj.classifies_uniquely mid, swap, rwa [r.2.1, id_comp], 
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

instance: has_pullbacks.{u} (Type u) := ⟨limits.has_limits_of_shape_of_has_limits⟩

-- this is a bit weird... need to look at the maths proof that we can classify in Set
instance: has_subobject_classifier Type :=
{ Ω := Prop
, Ω₀ := unit
, truth := λ _, true
, true_mono' := ⟨λ A f g _, begin ext i, apply subsingleton.elim end⟩
, classifies' := λ A B f mon, ⟨λ b, ∃ (a : A), f a = b, -- is this the right prop to use?
  begin
    refine ⟨λ _, unit.star, _, _⟩, 
    funext, simp, use x, 
    refine ⟨λ c i, _, sorry, sorry⟩, 
    show A,
    set π₁ := pullback_cone.fst c,
    set π₂ := pullback_cone.snd c,
    have: π₁ ≫ _ = π₂ ≫ _ := pullback_cone.condition c, 
    have: (π₂ ≫ (λ (b : B), ∃ (a : A), f a = b)) i,
    rw ← this, dsimp, trivial,
    dsimp at this, sorry, -- can do it with classical...
  end
⟩
, uniq' := _
}


end category_theory