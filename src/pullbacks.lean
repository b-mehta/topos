/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/

import category_theory.limits.shapes
import category_theory.limits.preserves
import .comma

/-!
# Pullbacks

Many, many lemmas to work with pullbacks.
-/
open category_theory category_theory.category category_theory.limits

universes u v
variables {C : Type u} [𝒞 : category.{v} C]
variables {J : Type v} [small_category J]
include 𝒞

variables {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

@[simp] lemma pullback_cone.simp_left {L : C} {lx : L ⟶ X} {ly : L ⟶ Y} {e : lx ≫ f = ly ≫ g} :
  ((pullback_cone.mk lx ly e).π).app walking_cospan.left = lx := rfl
@[simp] lemma pullback_cone.simp_right {L : C} {lx : L ⟶ X} {ly : L ⟶ Y} {e : lx ≫ f = ly ≫ g} :
  ((pullback_cone.mk lx ly e).π).app walking_cospan.right = ly := rfl

lemma pi_app {W : C} {h : X ⟶ Z} {k : Y ⟶ Z} {c₁ c₂ : cone (cospan h k)} {f : W ⟶ c₁.X} {g : W ⟶ c₂.X}
  (h1 : f ≫ pullback_cone.fst c₁ = g ≫ pullback_cone.fst c₂)
  (h2 : f ≫ pullback_cone.snd c₁ = g ≫ pullback_cone.snd c₂) :
  ∀ (j : walking_cospan), f ≫ c₁.π.app j = g ≫ c₂.π.app j :=
begin
  intro j, cases j, exact h1, exact h2,
  rw ← cone.w c₂ walking_cospan.hom.inl,
  rw ← cone.w c₁ walking_cospan.hom.inl,
  rw ← assoc, rw ← assoc, rw h1
end

/-- This is often useful in proving we have a limit for a pullback. -/
lemma pi_app_left {h : X ⟶ Z} {k : Y ⟶ Z} (c₁ c₂ : cone (cospan h k)) (f : c₂.X ⟶ c₁.X)
  (h1 : f ≫ pullback_cone.fst c₁ = pullback_cone.fst c₂)
  (h2 : f ≫ pullback_cone.snd c₁ = pullback_cone.snd c₂) :
  ∀ (j : walking_cospan), f ≫ c₁.π.app j = c₂.π.app j :=
begin
  convert @pi_app C _ _ _ _ _ _ _ c₁ c₂ f (𝟙 _) _ _,
  simp, simpa, simpa
end

lemma pullback_cone.hom_ext {t : pullback_cone f g} (h : is_limit t) {W : C} {f₁ f₂ : W ⟶ t.X}
  (h1 : f₁ ≫ pullback_cone.fst t = f₂ ≫ pullback_cone.fst t)
  (h2 : f₁ ≫ pullback_cone.snd t = f₂ ≫ pullback_cone.snd t) :
  f₁ = f₂ :=
is_limit.hom_ext h (pi_app h1 h2)

lemma pullback.hom_ext {X Y Z A : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  (a b : A ⟶ pullback f g)
  (h1 : a ≫ pullback.fst = b ≫ pullback.fst)
  (h2 : a ≫ pullback.snd = b ≫ pullback.snd)
    : a = b :=
pullback_cone.hom_ext (limit.is_limit _) h1 h2

@[simp] lemma pullback.lift_self_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] :
  pullback.lift pullback.fst pullback.snd pullback.condition = 𝟙 (pullback f g) :=
begin
  apply pullback.hom_ext,
  rw limit.lift_π, rw id_comp, refl,
  rw limit.lift_π, rw id_comp, refl
end

def iso_apex_of_iso_cone {F : J ⥤ C} {c₁ c₂ : cone F} (h : c₁ ≅ c₂) : c₁.X ≅ c₂.X :=
{ hom := h.hom.hom,
  inv := h.inv.hom,
  hom_inv_id' :=
  begin
    show (h.hom ≫ h.inv).hom = 𝟙 (c₁.X),
    have: h.hom ≫ h.inv = 𝟙 c₁ := h.hom_inv_id',
    rw this, refl
  end,
  inv_hom_id' :=
  begin
    show (h.inv ≫ h.hom).hom = 𝟙 (c₂.X),
    have: h.inv ≫ h.hom = 𝟙 c₂ := h.inv_hom_id',
    rw this, refl
  end,
}

-- The pasting lemma for pullbacks.
lemma pasting {C : Type u} [𝒞 : category.{v} C] {U V W X Y Z : C}
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
      have coned := entire.fac new_cone,
      apply pi_app_left (pullback_cone.mk f h left_comm),
      { apply pullback_cone.hom_ext right,
        { rw assoc, exact coned walking_cospan.left },
        { rw assoc, conv_lhs {congr, skip, erw left_comm}, rw ← assoc,
          erw [pullback_cone.condition c, coned walking_cospan.right], refl } },
      { exact coned walking_cospan.right }},
    { intros c r j,
      have new_cone_comm: (pullback_cone.fst c ≫ g) ≫ l = pullback_cone.snd c ≫ m ≫ n,
        rw assoc, rw ← pullback_cone.condition_assoc, rw right_comm,
      set new_cone := pullback_cone.mk (pullback_cone.fst c ≫ g) (pullback_cone.snd c) new_cone_comm,
      apply entire.uniq new_cone r, -- BM: here
      apply pi_app_left (pullback_cone.mk (f ≫ g) h _) new_cone _,
      { show r ≫ f ≫ g = _ ≫ g, rw ← assoc, congr, exact j walking_cospan.left },
      { show r ≫ h = (new_cone.π).app walking_cospan.right, exact j walking_cospan.right },
    }
  end,
  inv :=
  begin
    intro left,
    refine ⟨λ c, _, λ c, _, λ c, _⟩,
    { have new_cone_comm: pullback_cone.fst c ≫ l = (pullback_cone.snd c ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition,
      have new_cone2_comm: (right.lift (pullback_cone.mk _ _ new_cone_comm)) ≫ k = (pullback_cone.snd c : c.X ⟶ X) ≫ m :=
           right.fac (pullback_cone.mk _ _ new_cone_comm) walking_cospan.right,
      exact left.lift (pullback_cone.mk _ _ new_cone2_comm) },
    { set π₁ : c.X ⟶ W := pullback_cone.fst c,
      set π₂ : c.X ⟶ X := pullback_cone.snd c,
      have new_cone_comm: π₁ ≫ l = (π₂ ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition,
      have new_cone2_comm: (right.lift (pullback_cone.mk _ _ new_cone_comm)) ≫ k = π₂ ≫ m :=
            right.fac (pullback_cone.mk _ _ new_cone_comm) walking_cospan.right,
      set new_cone := pullback_cone.mk _ _ new_cone_comm,
      set new_cone2 := pullback_cone.mk _ _ new_cone2_comm,
      apply pi_app_left (pullback_cone.mk (f ≫ g) h _) c,
      erw [← assoc, left.fac' new_cone2 walking_cospan.left, right.fac' new_cone walking_cospan.left], refl,
      exact left.fac' new_cone2 walking_cospan.right },
    { set π₁ : c.X ⟶ W := pullback_cone.fst c,
      set π₂ : c.X ⟶ X := pullback_cone.snd c,
      have new_cone_comm: π₁ ≫ l = (π₂ ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition,
      set new_cone := pullback_cone.mk _ _ new_cone_comm,
      have new_cone2_comm: (right.lift new_cone) ≫ k = π₂ ≫ m := right.fac' new_cone walking_cospan.right,
      set new_cone2 := pullback_cone.mk _ _ new_cone2_comm,
      intros r J,
      show r = left.lift new_cone2,
      have Jr: r ≫ h = π₂ := J walking_cospan.right,
      apply left.uniq new_cone2, -- BM: here
      apply pi_app_left (pullback_cone.mk f h left_comm) new_cone2 _ _ Jr,
      { apply right.uniq new_cone, -- BM: here
        apply pi_app_left (pullback_cone.mk g k right_comm) new_cone,
        { rw assoc, exact J walking_cospan.left},
        { rw assoc, show r ≫ f ≫ k = π₂ ≫ m, rw ← Jr, conv_rhs {rw assoc}, congr, exact left_comm} } }
  end
, hom_inv_id' := subsingleton.elim _ _
, inv_hom_id' := subsingleton.elim _ _
}

def pullback.with_id_r' {X Y : C} (f : X ⟶ Y) :
  is_limit (pullback_cone.mk f (𝟙 X) (by simp) : pullback_cone (𝟙 Y) f) :=
{ lift := λ c, (c.π).app walking_cospan.right,
  fac' := λ c j,
  begin
    cases j, -- BM: triple case
    { erw ← pullback_cone.condition c, simp },
    { erw comp_id },
    show _ ≫ f ≫ 𝟙 Y = _,
    erw [comp_id, ← c.π.naturality walking_cospan.hom.inr, id_comp],
  end,
  uniq' := λ _ _ J, by erw ← J walking_cospan.right; exact (comp_id _ _).symm
}

@[reducible]
def cospan_cone.flip {f : X ⟶ Z} {g : Y ⟶ Z} (c : cone (cospan f g)) : cone (cospan g f) :=
pullback_cone.mk (pullback_cone.snd c) (pullback_cone.fst c) (pullback_cone.condition c).symm

def flip_mk {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (comm : f ≫ h = g ≫ k) :
  cospan_cone.flip (pullback_cone.mk f g comm) ≅ pullback_cone.mk g f comm.symm :=
by apply cones.ext (iso.refl _) (λ j, _); erw id_comp

def flip_twice {f : X ⟶ Z} {g : Y ⟶ Z} (c : cone (cospan f g)) : cospan_cone.flip (cospan_cone.flip c) ≅ c :=
begin
  apply cones.ext _ _, exact iso.refl _,
  intros j, erw id_comp, cases j, -- BM: triple case
  refl, refl,
  apply cone.w c walking_cospan.hom.inl
end

def flip_hom {f : X ⟶ Z} {g : Y ⟶ Z} {c₁ c₂ : cone (cospan f g)} (h : c₁ ⟶ c₂) : cospan_cone.flip c₁ ⟶ cospan_cone.flip c₂ :=
{ hom := h.hom,
  w' := begin rintro (_ | _ | _), apply h.w, apply h.w, erw [← assoc, h.w], refl end} -- BM: triple case

def pullback.flip {Y Z W : C} {h : Y ⟶ W} {k : Z ⟶ W} {c : cone (cospan h k)} (z : is_limit c) :
  is_limit (cospan_cone.flip c) :=
{ lift := λ s, z.lift (cospan_cone.flip s),
  fac' := λ s j, walking_cospan.cases_on j (z.fac' (cospan_cone.flip s) walking_cospan.right)
                                           (z.fac' (cospan_cone.flip s) walking_cospan.left)
        (begin
            show _ ≫ _ ≫ _ = _, rw ← cone.w s walking_cospan.hom.inr,
            rw ← pullback_cone.condition c, rw ← assoc,
            erw z.fac', refl
          end), -- BM: triple case
  uniq' := λ s m J,
  begin
    apply z.uniq (cospan_cone.flip s),
    apply pi_app_left c (cospan_cone.flip s),
    erw J walking_cospan.right, refl,
    erw J walking_cospan.left, refl,
  end
}
def pullback.flip'' {Y Z W : C} {h : Y ⟶ W} {k : Z ⟶ W} {c : cone (cospan h k)} :
  is_limit c ≅ is_limit (cospan_cone.flip c) :=
{ hom := pullback.flip, inv := pullback.flip ≫ (λ l, is_limit.of_iso_limit l (flip_twice _))}

def flip_limit_cone [@has_pullbacks C 𝒞] (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan_cone.flip (limit.cone (cospan g f)) ≅ limit.cone (cospan f g) :=
{ hom := limit.cone_morphism _,
  inv := ((flip_twice _).inv ≫ flip_hom (limit.cone_morphism _)),
  hom_inv_id' :=
  begin
    ext, simp, dunfold flip_hom flip_twice cones.ext, erw [id_comp, limit.lift_π],
    { erw limit.lift_π, refl },
    { simp, erw limit.lift_π, dunfold flip_twice cospan_cone.flip, simp,
      erw [id_comp, limit.lift_π], refl }
  end,
  inv_hom_id' := is_limit.uniq_cone_morphism (limit.is_limit _) }

def pullback.flip' [@has_pullbacks C 𝒞] (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ≅ pullback g f :=
iso_apex_of_iso_cone (flip_limit_cone f g).symm

def pullback.with_id_l' {X Y : C} (f : X ⟶ Y) :
  is_limit (pullback_cone.mk (𝟙 X) f (show (𝟙 X) ≫ f = f ≫ (𝟙 Y), by simp)) :=
is_limit.of_iso_limit (pullback.flip (pullback.with_id_r' f)) (flip_mk _)

def identify_limit_apex {F : J ⥤ C} [has_limit F] {a : cone F} (t : is_limit a) :
  (limit.cone F).X ≅ a.X :=
iso_apex_of_iso_cone (is_limit.unique_up_to_iso (limit.is_limit _) t)

/- Note that we need `has_pullbacks` even though this particular pullback always exists, because here we are showing that the
constructive limit derived using has_pullbacks has to be iso to this simple definition.  -/
def pullback.with_id_r [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback (𝟙 Y) f ≅ X :=
identify_limit_apex (pullback.with_id_r' f)

def pullback.with_id_l [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback f (𝟙 Y) ≅ X :=
pullback.flip' _ _ ≪≫ pullback.with_id_r f

lemma make_pullback [has_limit (cospan f g)] :
  pullback_cone.mk pullback.fst pullback.snd pullback.condition ≅ limit.cone (cospan f g) :=
begin
  apply cones.ext _ (λ j, _), refl, erw id_comp, cases j, refl, refl,
  apply (limit.cone (cospan f g)).w walking_cospan.hom.inl
end

-- todo: use pasting here
lemma pullback.comp_l {W X Y Z : C} {xz : X ⟶ Z} {yz : Y ⟶ Z} {wx : W ⟶ X} [@has_pullbacks C 𝒞]:
pullback (wx ≫ xz) yz ≅ pullback wx (@pullback.fst _ _ _ _ _ xz yz _) :=
begin
  apply iso.mk _ _ _ _,
  { refine pullback.lift pullback.fst (pullback.lift (pullback.fst ≫ wx) pullback.snd _) _, simp, rw pullback.condition,  simp},
  { refine pullback.lift pullback.fst (pullback.snd ≫ pullback.snd) _, rw ← category.assoc, rw pullback.condition, simp, rw pullback.condition },
  {apply pullback.hom_ext, simp, simp },
  {apply pullback.hom_ext, simp, simp, apply pullback.hom_ext, simp, apply pullback.condition, simp},
end

lemma test [has_pullbacks.{v} C] {X Y Z : C} {xz : X ⟶ Z} {yz : Y ⟶ Z} :
  is_limit (pullback_cone.mk pullback.fst pullback.snd pullback.condition : pullback_cone yz xz) :=
(limit.is_limit _).of_iso_limit make_pullback.symm

lemma pullback.comp_r {W X Y Z : C} {xz : X ⟶ Z} {yz : Y ⟶ Z} {wx : W ⟶ X} [@has_pullbacks C 𝒞]:
  pullback yz (wx ≫ xz) ≅ pullback (@pullback.snd _ _ _ _ _ yz xz _) wx :=
identify_limit_apex ((pasting _ _ _ _ _ _ _ _ _ test).inv test) ≪≫ iso_apex_of_iso_cone make_pullback

-- Show
-- D × A ⟶ B × A
--   |       |
--   v       v
--   D   ⟶   B
-- is a pullback (needed in over/exponentiable_in_slice)
def pullback_prod (xy : X ⟶ Y) (Z : C) [has_binary_products.{v} C] :
  is_limit (pullback_cone.mk limits.prod.fst (limits.prod.map xy (𝟙 Z)) (by simp) : pullback_cone xy limits.prod.fst) :=
{ lift := λ s, prod.lift (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.snd),
  fac' := λ s,
    begin
      apply pi_app_left (pullback_cone.mk limits.prod.fst (limits.prod.map xy (𝟙 Z)) _) s, dsimp,
        dunfold pullback_cone.fst, simp, -- this should have been just simp
      apply limit.hom_ext, intro j, cases j, simp, dsimp, -- this should be easy.
        dunfold pullback_cone.snd, rw pullback_cone.simp_right, simp, exact pullback_cone.condition s,
      simp, dunfold pullback_cone.snd, simp, dsimp, simp -- look here ed
    end,
  uniq' := λ s m J,
    begin
      ext, cases j, simp, apply J walking_cospan.left, simp, dunfold pullback_cone.snd, erw ← J walking_cospan.right,
      simp, dsimp, simp
    end
}

def pullback_prod' (xy : X ⟶ Y) (Z : C) [has_binary_products.{v} C] :
  is_limit (pullback_cone.mk limits.prod.snd (limits.prod.map (𝟙 Z) xy) (by simp) : pullback_cone xy limits.prod.snd) :=
{ lift := λ s, prod.lift (pullback_cone.snd s ≫ limits.prod.fst) (pullback_cone.fst s),
  fac' := λ s,
    begin
      apply pi_app_left (pullback_cone.mk limits.prod.snd (limits.prod.map (𝟙 Z) xy) _) s, dsimp,
        dunfold pullback_cone.fst, simp,
      apply limit.hom_ext, intro j, cases j, simp, dsimp,
        dunfold pullback_cone.snd, rw pullback_cone.simp_right, simp, dsimp, simp,
      simp, dunfold pullback_cone.snd, simp, dsimp, rw pullback_cone.condition s,
    end,
  uniq' := λ s m J,
    begin
      ext, cases j, simp, dunfold pullback_cone.snd, erw ← J walking_cospan.right, simp, dsimp, simp,
      simp, dsimp, dunfold pullback_cone.fst, erw ← J walking_cospan.left, simp,
    end
}

@[reducible]
def pullback_of_iso {U V W X : C} {f : U ⟶ X} {g : V ⟶ X} {h : W ⟶ X} (z : V ≅ W) (hyp : z.hom ≫ h = g) (c : pullback_cone f g) :
  pullback_cone f h :=
pullback_cone.mk c.fst (c.snd ≫ z.hom) (by rw [pullback_cone.condition c, assoc, hyp])

set_option pp.implicit false

lemma pullback_of_iso_is_limit {U V W X : C} (f : U ⟶ X) {g : V ⟶ X} {h : W ⟶ X} (z : V ≅ W)
  (hyp : z.hom ≫ h = g) (c : pullback_cone f g) :
is_limit c ≅ is_limit (pullback_of_iso z hyp c) :=
{ hom := λ t,
  { lift :=
    begin
      intro s, apply t.lift (pullback_of_iso z.symm _ s), rw [iso.symm_hom, iso.inv_comp_eq, hyp],
    end,
    fac' :=
    begin
      intro s, apply pi_app_left (pullback_of_iso z hyp c) s,
      apply t.fac,
      erw ← assoc, rw t.fac, erw assoc, simp
    end,
    uniq' :=
    begin
      intros s m J, apply t.uniq (pullback_of_iso z.symm _ s),
      apply pi_app_left c (pullback_of_iso _ _ _),
      erw J walking_cospan.left, refl,
      erw ← iso.comp_inv_eq, rw assoc, exact J walking_cospan.right
    end },
  inv := λ t,
  { lift := λ s, t.lift (pullback_of_iso z hyp s),
    fac' :=
    begin
      intro s,
      apply pi_app_left c s,
        exact t.fac (pullback_of_iso z hyp s) walking_cospan.left,
      have := t.fac (pullback_of_iso z hyp s) walking_cospan.right, simp at this,
      rw ← assoc at this,
      rw cancel_mono at this, assumption
    end,
    uniq' := λ s m J,
    begin
      apply t.uniq (pullback_of_iso z hyp s),
      apply pi_app_left (pullback_of_iso z hyp c) (pullback_of_iso z hyp s),
      apply J walking_cospan.left,
      erw ← assoc, erw J walking_cospan.right, refl
    end},
  hom_inv_id' := subsingleton.elim _ _,
  inv_hom_id' := subsingleton.elim _ _}

/--
If V and W are isomorphic, and g : V ⟶ X, h : W ⟶ X respect the isomorphism, then
the pullback of f along g is isomorphic to the pullback of f along h
-/
lemma pullback_of_iso_apex [has_pullbacks.{v} C] {U V W X : C} {f : U ⟶ X} {g : V ⟶ X} {h : W ⟶ X} (z : V ≅ W) (hyp : z.hom ≫ h = g) :
  pullback f g ≅ pullback f h :=
(identify_limit_apex ((pullback_of_iso_is_limit f z hyp (limit.cone _)).hom (limit.is_limit _))).symm

lemma pullback.comp_l' {W X Y Z : C} {xz : X ⟶ Z} {yz : Y ⟶ Z} {wx : W ⟶ X} [@has_pullbacks C 𝒞]:
pullback (wx ≫ xz) yz ≅ pullback wx (@pullback.fst _ _ _ _ _ xz yz _) :=
pullback.flip' _ _ ≪≫ pullback.comp_r ≪≫ pullback.flip' _ _ ≪≫
begin
  show pullback wx (@pullback.snd _ _ _ _ _ yz xz _ : pullback yz xz ⟶ X) ≅ pullback wx (@pullback.fst _ _ _ _ _ xz yz _ : pullback xz yz ⟶ X),
  apply pullback_of_iso_apex (pullback.flip' _ _),
  -- XXX: this goal should probably be its own lemma
  dunfold pullback.flip' iso_apex_of_iso_cone flip_limit_cone flip_twice flip_hom,
  show (𝟙 _ ≫ _) ≫ _ = _,
  erw id_comp,
  erw [limit.lift_π], refl
end

-- [todo] comp_r; I was hoping there would be a cool way of lifting the isomorphism `(cospan f g).cones ≅ (cospan g f).cones` but can't see it.

/-- Pullback of a monic is monic. -/
lemma pullback.preserve_mono [@has_pullbacks C 𝒞]
  {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (hm : mono f) : @mono _ _ (pullback f g) _ pullback.snd :=
begin
  split, intros A a b e,
  have c : pullback.fst ≫ f = pullback.snd ≫ g, apply pullback.condition,
  apply pullback.hom_ext,
    show a ≫ pullback.fst = b ≫ pullback.fst,
    apply hm.1, simp,
    rw c, rw ← category.assoc,  rw e, simp,
  show a ≫ pullback.snd = b ≫ pullback.snd, assumption,
end

def over.pullback [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) (g : over Y) : over X :=
over.mk (@pullback.fst _ _ _ _ _ f g.hom _)

@[simp] lemma over_pullback_def [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) (g : over Y) :
  (over.pullback f g).hom = pullback.fst := rfl

lemma mono_of_pullback (X Y : C) (f : X ⟶ Y)
  (hl : is_limit (pullback_cone.mk (𝟙 X) (𝟙 X) (by simp) : pullback_cone f f)) : mono f :=
begin
  split, intros,
  set new_cone : pullback_cone f f := pullback_cone.mk g h w,
  exact (hl.fac new_cone walking_cospan.left).symm.trans (hl.fac new_cone walking_cospan.right),
end

lemma pullback_of_mono (X Y : C) (f : X ⟶ Y) (hf : mono f) :
  is_limit (pullback_cone.mk (𝟙 X) (𝟙 X) (by simp) : pullback_cone f f) :=
{ lift := λ s, pullback_cone.fst s,
  fac' := λ s, begin apply pi_app_left (pullback_cone.mk (𝟙 X) (𝟙 X) _) s, erw comp_id, erw comp_id, rw ← cancel_mono f, exact pullback_cone.condition s end,
  uniq' := λ s m J, (comp_id _ m).symm.trans (J walking_cospan.left) }

universe u₂

lemma cospan_comp {D : Type u₂} [category.{v} D] (F : C ⥤ D) : cospan (F.map f) (F.map g) = cospan f g ⋙ F :=
begin
  apply category_theory.functor.ext, intros, cases f_1, simp, simp, simp, dsimp, simp,
  intro j, cases j, simp, simp, simp
end

lemma preserves_mono_of_preserves_pullback {D : Type u₂} [category.{v} D] (F : C ⥤ D)
  (hF : preserves_limits_of_shape walking_cospan F) (X Y : C) (f : X ⟶ Y) (hf : mono f) :
  mono (F.map f) :=
begin
  apply mono_of_pullback,
  have that: is_limit _ := preserves_limit.preserves F (pullback_of_mono _ _ f hf),
  have: cospan (F.map f) (F.map f) = cospan f f ⋙ F := cospan_comp _,
  convert that,
  dsimp [functor.map_cone, cones.functoriality, pullback_cone.mk],
  congr, assumption, assumption, refine function.hfunext rfl _, intros, tactic.case_bash, simp, simp, simp,
  apply proof_irrel_heq
end
