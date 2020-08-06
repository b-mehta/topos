/-
Copyright (c) 2020 Bhavik Mehta, Edward Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Edward Ayers
-/

import category_theory.limits.shapes
import category_theory.limits.preserves
import category_theory.limits.over
import category_theory.limits.shapes.constructions.over
import tactic

/-!
# Pullbacks

Many, many lemmas to work with pullbacks.
-/
open category_theory category_theory.category category_theory.limits

universes u v
variables {C : Type u} [category.{v} C]
variables {J : Type v} [small_category J]

variables {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- A supremely useful structure for elementary topos theory. -/
structure has_pullback_top (left : W ⟶ Y) (bottom : Y ⟶ Z) (right : X ⟶ Z) :=
(top : W ⟶ X)
(comm : top ≫ right = left ≫ bottom)
(is_pb : is_limit (pullback_cone.mk _ _ comm))

attribute [reassoc] has_pullback_top.comm

instance subsingleton_hpb (left : W ⟶ Y) (bottom : Y ⟶ Z) (right : X ⟶ Z) [mono right] :
  subsingleton (has_pullback_top left bottom right) :=
⟨begin
  intros P Q,
  cases P,
  cases Q,
  congr,
  rw ← cancel_mono right,
  rw P_comm, rw Q_comm
end⟩

def has_pullback_top_of_is_pb {U V W X : C}
  {f : U ⟶ V} {g : V ⟶ W} {h : U ⟶ X} {k : X ⟶ W}
  {comm : f ≫ g = h ≫ k}
  (pb : is_limit (pullback_cone.mk _ _ comm)) :
  has_pullback_top h k g :=
{ top := f,
  comm := comm,
  is_pb := pb }

def is_limit.mk' (t : pullback_cone f g)
  (create : Π (s : pullback_cone f g), {l : s.X ⟶ t.X // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧ ∀ {m : s.X ⟶ t.X}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l}) :
is_limit t :=
pullback_cone.is_limit_aux t
  (λ s, (create s).1)
  (λ s, (create s).2.1)
  (λ s, (create s).2.2.1)
  (λ s m w, (create s).2.2.2 (w walking_cospan.left) (w walking_cospan.right))

def is_limit.mk'' (t : pullback_cone f g) [mono f]
  (create : Π (s : pullback_cone f g), {l : s.X ⟶ t.X // l ≫ t.snd = s.snd ∧ ∀ {m : s.X ⟶ t.X}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l}) :
is_limit t :=
is_limit.mk' t $
begin
  intro s,
  refine ⟨(create s).1, _, (create s).2.1, λ m m₁ m₂, (create s).2.2 m₁ m₂⟩,
  rw [← cancel_mono f, assoc, t.condition, s.condition, reassoc_of (create s).2.1]
end

def is_limit.mk''' (t : pullback_cone f g) [mono f] (q : mono t.snd)
  (create : Π (s : pullback_cone f g), {l : s.X ⟶ t.X // l ≫ t.snd = s.snd}) :
is_limit t :=
is_limit.mk' t $
begin
  intro s,
  refine ⟨(create s).1, _, (create s).2, λ m _ m₂, _⟩,
  rw [← cancel_mono f, assoc, t.condition, s.condition, reassoc_of (create s).2],
  rw [← cancel_mono t.snd, m₂, (create s).2],
end

def construct_type_pb {W X Y Z : Type u} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ _} {k} (comm : h ≫ f = k ≫ g) :
  (∀ (x : X) (y : Y), f x = g y → {t // h t = x ∧ k t = y ∧ ∀ t', h t' = x → k t' = y → t' = t}) → is_limit (pullback_cone.mk _ _ comm) :=
begin
  intro z,
  apply is_limit.mk' _ _,
  intro s,
  refine ⟨λ t, _, _, _, _⟩,
  refine (z (s.fst t) (s.snd t) (congr_fun s.condition t)).1,
  ext t,
  apply (z (s.fst t) (s.snd t) (congr_fun s.condition t)).2.1,
  ext t,
  apply (z (s.fst t) (s.snd t) (congr_fun s.condition t)).2.2.1,
  intros m m₁ m₂,
  ext t,
  apply (z (s.fst t) (s.snd t) (congr_fun s.condition t)).2.2.2,
  apply congr_fun m₁ t,
  apply congr_fun m₂ t,
end

def pullback_mono_is_mono (c : pullback_cone f g) [mono f] (t : is_limit c) : mono c.snd :=
⟨λ Z h k eq,
begin
  apply t.hom_ext,
  apply pullback_cone.equalizer_ext,
  rw [← cancel_mono f, assoc, c.condition, reassoc_of eq, assoc, c.condition],
  assumption
end⟩

def cone_is_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (cospan f g)] :
  is_limit (pullback_cone.mk _ _ pullback.condition : pullback_cone f g) :=
is_limit.mk' _ $ λ s,
⟨ pullback.lift _ _ s.condition,
  pullback.lift_fst _ _ _,
  pullback.lift_snd _ _ _,
  λ m m₁ m₂, pullback.hom_ext (by simpa using m₁) (by simpa using m₂) ⟩

def is_limit_as_pullback_cone_mk (s : pullback_cone f g) (t : is_limit (pullback_cone.mk s.fst s.snd s.condition)) :
  is_limit s :=
{ lift := λ c, t.lift c,
  fac' := λ c j,
  begin
    cases j,
    simp [← t.fac c none, ← s.w walking_cospan.hom.inl],
    cases j,
    exact t.fac c walking_cospan.left,
    exact t.fac c walking_cospan.right,
  end,
  uniq' := λ c m w,
  begin
    apply t.uniq,
    intro j,
    rw ← w,
    cases j,
    simp [← t.fac c none, ← s.w walking_cospan.hom.inl],
    cases j; refl,
  end }

def has_pullback_top_of_pb [has_limit (cospan f g)] :
  has_pullback_top (pullback.snd : pullback f g ⟶ Y) g f :=
{ top := pullback.fst,
  comm := pullback.condition,
  is_pb := cone_is_pullback f g }

def left_pb_to_both_pb {U V W X Y Z : C}
  (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ X) (k : V ⟶ Y) (l : W ⟶ Z) (m : X ⟶ Y) (n : Y ⟶ Z)
  (left_comm : f ≫ k = h ≫ m)
  (right_comm : g ≫ l = k ≫ n)
  (left_pb : is_limit (pullback_cone.mk f h left_comm))
  (right_pb : is_limit (pullback_cone.mk g k right_comm)) :
is_limit (pullback_cone.mk (f ≫ g) h (begin rw [assoc, right_comm, reassoc_of left_comm]end)) :=
is_limit.mk' _ $
begin
  intro s,
  let t : s.X ⟶ V := right_pb.lift (pullback_cone.mk s.fst (s.snd ≫ m) (by rw [assoc, s.condition])),
  have l_comm : t ≫ k = s.snd ≫ m := right_pb.fac _ walking_cospan.right,
  let u : s.X ⟶ U := left_pb.lift (pullback_cone.mk _ _ l_comm),
  have uf : u ≫ f = t := left_pb.fac _ walking_cospan.left,
  have tg : t ≫ g = s.fst := right_pb.fac _ walking_cospan.left,
  refine ⟨u, _, left_pb.fac _ walking_cospan.right, _⟩,
  { rw [← tg, ← uf, assoc u f g], refl },
  { intros m' m₁ m₂,
    apply left_pb.hom_ext,
    apply (pullback_cone.mk f h left_comm).equalizer_ext,
    { apply right_pb.hom_ext,
      apply (pullback_cone.mk g k right_comm).equalizer_ext,
      { erw [uf, assoc, tg], exact m₁ },
      { erw [uf, assoc, left_comm, reassoc_of m₂, l_comm] } },
    { erw [left_pb.fac _ walking_cospan.right], exact m₂ } }
end

def both_pb_to_left_pb {U V W X Y Z : C}
  (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ X) (k : V ⟶ Y) (l : W ⟶ Z) (m : X ⟶ Y) (n : Y ⟶ Z)
  (left_comm : f ≫ k = h ≫ m)
  (right_comm : g ≫ l = k ≫ n)
  (right_pb : is_limit (pullback_cone.mk g k right_comm))
  (entire_pb : is_limit (pullback_cone.mk (f ≫ g) h (begin rw [assoc, right_comm, reassoc_of left_comm] end))) :
is_limit (pullback_cone.mk f h left_comm) :=
is_limit.mk' _ $
begin
  intro s,
  let u : s.X ⟶ U := entire_pb.lift (pullback_cone.mk (s.fst ≫ g) s.snd (by rw [assoc, right_comm, s.condition_assoc])),
  have uf : u ≫ f = s.fst,
  { apply right_pb.hom_ext,
    apply (pullback_cone.mk g k right_comm).equalizer_ext,
    { rw [assoc], exact entire_pb.fac _ walking_cospan.left },
    { erw [assoc, left_comm, ← assoc, entire_pb.fac _ walking_cospan.right, s.condition], refl } },
  refine ⟨u, uf, entire_pb.fac _ walking_cospan.right, _⟩,
  { intros m' m₁ m₂,
    apply entire_pb.hom_ext,
    apply (pullback_cone.mk (f ≫ g) h _).equalizer_ext,
    { erw [reassoc_of uf, reassoc_of m₁] },
    { rwa entire_pb.fac _ walking_cospan.right } }
end

def left_hpb_right_pb_to_both_hpb {U V W X Y Z : C}
  (g : V ⟶ W) (h : U ⟶ X) (k : V ⟶ Y) (l : W ⟶ Z) (m : X ⟶ Y) (n : Y ⟶ Z)
  (left : has_pullback_top h m k)
  (right_comm : g ≫ l = k ≫ n)
  (right_pb : is_limit (pullback_cone.mk g k right_comm)) :
  has_pullback_top h (m ≫ n) l :=
{ top := left.top ≫ g,
  comm := by rw [assoc, right_comm, reassoc_of left.comm],
  is_pb := left_pb_to_both_pb left.top g h k l m n left.comm right_comm left.is_pb right_pb }

def right_both_hpb_to_left_hpb {U V W X Y Z : C}
  {h : U ⟶ X} {k : V ⟶ Y} (l : W ⟶ Z) {m : X ⟶ Y} (n : Y ⟶ Z)
  (both : has_pullback_top h (m ≫ n) l)
  (right : has_pullback_top k n l) :
  has_pullback_top h m k :=
begin
  let t : U ⟶ V := right.is_pb.lift (pullback_cone.mk both.top (h ≫ m) (by rw [assoc, both.comm])),
  refine ⟨t, right.is_pb.fac _ walking_cospan.right, _⟩,
  apply both_pb_to_left_pb t right.top h k l m n _ _ right.is_pb,
  convert both.is_pb,
  apply right.is_pb.fac _ walking_cospan.left,
end

def left_right_hpb_to_both_hpb {U V W X Y Z : C}
  {h : U ⟶ X} (k : V ⟶ Y) {l : W ⟶ Z} {m : X ⟶ Y} {n : Y ⟶ Z}
  (left : has_pullback_top h m k)
  (right : has_pullback_top k n l) :
  has_pullback_top h (m ≫ n) l :=
{ top := left.top ≫ right.top,
  comm := by rw [assoc, right.comm, reassoc_of left.comm],
  is_pb := left_pb_to_both_pb left.top right.top h k l m n left.comm right.comm left.is_pb right.is_pb }

def vpaste {U V W X Y Z : C} (f : U ⟶ V) (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z)
  (up_comm : f ≫ h = g ≫ k) (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm))
  (up_pb : is_limit (pullback_cone.mk _ _ up_comm)) :
  is_limit (pullback_cone.mk f (g ≫ l) (by rw [reassoc_of up_comm, down_comm, assoc]) : pullback_cone (h ≫ m) n):=
is_limit.mk' _ $
begin
  intro s,
  let c' : pullback_cone m n := pullback_cone.mk (pullback_cone.fst s ≫ h) (pullback_cone.snd s) (by simp [pullback_cone.condition s]),
  let t : s.X ⟶ W := down_pb.lift c',
  have tl : t ≫ l = pullback_cone.snd s := down_pb.fac c' walking_cospan.right,
  have tk : t ≫ k = pullback_cone.fst s ≫ h := down_pb.fac c' walking_cospan.left,
  let c'' : pullback_cone h k := pullback_cone.mk (pullback_cone.fst s) t (down_pb.fac c' walking_cospan.left).symm,
  let u : s.X ⟶ U := up_pb.lift c'',
  have uf : u ≫ f = pullback_cone.fst s := up_pb.fac c'' walking_cospan.left,
  have ug : u ≫ g = t := up_pb.fac c'' walking_cospan.right,
  refine ⟨u, uf, by erw [reassoc_of ug, tl], _⟩,
  intros m' m₁ m₂,
  apply up_pb.hom_ext,
  apply (pullback_cone.mk f g up_comm).equalizer_ext,
  change m' ≫ f = u ≫ f,
  erw [m₁, uf],
  erw ug,
  apply down_pb.hom_ext,
  apply (pullback_cone.mk _ _ down_comm).equalizer_ext,
  { change (m' ≫ g) ≫ k = t ≫ k,
    slice_lhs 2 3 {rw ← up_comm},
    slice_lhs 1 2 {erw m₁},
    rw tk },
  { change (m' ≫ g) ≫ l = t ≫ l,
    erw [assoc, m₂, tl] }
end

def stretch_hpb_down {U V W X Y Z : C} (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z)
  (up : has_pullback_top g k h)
  (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm)) :
has_pullback_top (g ≫ l) n (h ≫ m) :=
{ top := up.top,
  comm := by rw [up.comm_assoc, down_comm, assoc],
  is_pb := vpaste up.top g h k l m n up.comm down_comm down_pb up.is_pb }

def vpaste' {U V W X Y Z : C} (f : U ⟶ V) (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z)
  (up_comm : f ≫ h = g ≫ k) (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm))
  (entire_pb : is_limit (pullback_cone.mk f (g ≫ l) (by rw [reassoc_of up_comm, down_comm, assoc]) : pullback_cone (h ≫ m) n)) :
  is_limit (pullback_cone.mk _ _ up_comm) :=
is_limit.mk' _ $
begin
  intro s,
  let c' : pullback_cone (h ≫ m) n := pullback_cone.mk (pullback_cone.fst s) (pullback_cone.snd s ≫ l) (by simp [pullback_cone.condition_assoc s, down_comm]),
  let t : s.X ⟶ U := entire_pb.lift c',
  have t₁ : t ≫ f = pullback_cone.fst s := entire_pb.fac c' walking_cospan.left,
  have t₂ : t ≫ g ≫ l = pullback_cone.snd s ≫ l := entire_pb.fac c' walking_cospan.right,
  have t₃ : t ≫ g = pullback_cone.snd s,
    apply down_pb.hom_ext,
    apply pullback_cone.equalizer_ext (pullback_cone.mk k l down_comm) _ _,
    erw [assoc, ← up_comm, reassoc_of t₁, pullback_cone.condition s], refl,
    rwa [assoc],
  refine ⟨t, t₁, t₃, _⟩,
  intros m' m₁ m₂,
  apply entire_pb.hom_ext,
  apply pullback_cone.equalizer_ext (pullback_cone.mk f (g ≫ l) _) _ _,
  exact m₁.trans t₁.symm,
  refine trans _ t₂.symm,
  erw [reassoc_of m₂]
end

-- The mono isn't strictly necessary but this version is convenient.
-- XXX: It's to ensure g is unique - the alternate solution is to take g ≫ l as one of the arguments and calculate g
def cut_hpb_up {U V W X Y Z : C} (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z) [mono m]
  (all : has_pullback_top (g ≫ l) n (h ≫ m))
  (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm)) :
has_pullback_top g k h :=
{ top := all.top,
  comm := by rw [← cancel_mono m, assoc, all.comm, assoc, ← down_comm, assoc],
  is_pb := vpaste' _ _ _ _ _ _ _ _ _ down_pb all.is_pb }

def cut_hpb_up' {U V W X Y Z : C} (g : U ⟶ W) (h : V ⟶ X) (k : W ⟶ X) (l : W ⟶ Y) (m : X ⟶ Z) (n : Y ⟶ Z)
  (all : has_pullback_top (g ≫ l) n (h ≫ m))
  (up_comm : all.top ≫ h = g ≫ k)
  (down_comm : k ≫ m = l ≫ n)
  (down_pb : is_limit (pullback_cone.mk _ _ down_comm)) :
has_pullback_top g k h :=
{ top := all.top,
  comm := up_comm,
  is_pb := vpaste' _ _ _ _ _ _ _ _ _ down_pb all.is_pb }

-- Show
-- D × A ⟶ B × A
--   |       |
--   v       v
--   D   ⟶   B
-- is a pullback (needed in over/exponentiable_in_slice)
def pullback_prod (xy : X ⟶ Y) (Z : C) [has_binary_products.{v} C] :
  is_limit (pullback_cone.mk limits.prod.fst (limits.prod.map xy (𝟙 Z)) (limits.prod.map_fst _ _).symm) :=
is_limit.mk' _ $
begin
  intro s,
  refine ⟨prod.lift (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.snd), limit.lift_π _ _, _, _⟩,
  { change limits.prod.lift (pullback_cone.fst s) (pullback_cone.snd s ≫ limits.prod.snd) ≫
      limits.prod.map xy (𝟙 Z) = pullback_cone.snd s,
    apply prod.hom_ext,
    rw [assoc, limits.prod.map_fst, prod.lift_fst_assoc, pullback_cone.condition s],
    rw [assoc, limits.prod.map_snd, prod.lift_snd_assoc, comp_id] },
  { intros m m₁ m₂,
    apply prod.hom_ext,
    simpa using m₁,
    erw [prod.lift_snd, ← m₂, assoc, limits.prod.map_snd, comp_id] },
end

def pullback_prod' (xy : X ⟶ Y) (Z : C) [has_binary_products.{v} C] :
  is_limit (pullback_cone.mk limits.prod.snd (limits.prod.map (𝟙 Z) xy) (limits.prod.map_snd _ _).symm) :=
is_limit.mk' _ $
begin
  intro s,
  refine ⟨prod.lift (pullback_cone.snd s ≫ limits.prod.fst) (pullback_cone.fst s), limit.lift_π _ _, _, _⟩,
  { apply prod.hom_ext,
    erw [assoc, limits.prod.map_fst, prod.lift_fst_assoc, comp_id],
    slice_lhs 2 3 {erw limits.prod.map_snd},
    rw [prod.lift_snd_assoc, pullback_cone.condition s] },
  { intros m m₁ m₂,
    apply prod.hom_ext,
    erw [prod.lift_fst, ← m₂, assoc, limits.prod.map_fst, comp_id],
    simpa using m₁ }
end

def pullback_flip {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z} {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk _ _ comm.symm)) :
  is_limit (pullback_cone.mk _ _ comm) :=
is_limit.mk' _ $ λ s,
begin
  refine ⟨(pullback_cone.is_limit.lift' t _ _ s.condition.symm).1,
          (pullback_cone.is_limit.lift' t _ _ _).2.2,
          (pullback_cone.is_limit.lift' t _ _ _).2.1, λ m m₁ m₂, t.hom_ext _⟩,
  apply (pullback_cone.mk g f _).equalizer_ext,
  { rw (pullback_cone.is_limit.lift' t _ _ _).2.1,
    exact m₂ },
  { rw (pullback_cone.is_limit.lift' t _ _ _).2.2,
    exact m₁ },
end

def pullback_square_iso {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [mono h] [is_iso g] (comm : f ≫ h = g ≫ k) :
  is_limit (pullback_cone.mk _ _ comm) :=
is_limit.mk''' _ (by dsimp [pullback_cone.mk]; apply_instance) $
  λ s, ⟨s.snd ≫ inv g, by erw [assoc, is_iso.inv_hom_id g, comp_id] ⟩

def left_iso_has_pullback_top {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [mono h] [is_iso g] (comm : f ≫ h = g ≫ k) :
  has_pullback_top g k h :=
{ top := f,
  comm := comm,
  is_pb := pullback_square_iso f g h k comm }

def pullback_square_iso' {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [is_iso f] [mono k] (comm : f ≫ h = g ≫ k) :
  is_limit (pullback_cone.mk _ _ comm) :=
is_limit.mk' _ $
begin
  intro s,
  refine ⟨pullback_cone.fst s ≫ inv f, _, _, _⟩,
  erw [assoc, is_iso.inv_hom_id, comp_id],
  erw [← cancel_mono k, assoc, ← comm, assoc, is_iso.inv_hom_id_assoc, pullback_cone.condition s],
  intros m m₁ m₂,
  erw [(as_iso f).eq_comp_inv, m₁]
end

def top_iso_has_pullback_top {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (k : Y ⟶ Z) [is_iso f] [mono k] (comm : f ≫ h = g ≫ k) :
  has_pullback_top g k h :=
{ top := f,
  comm := comm,
  is_pb := pullback_square_iso' f g h k comm }

lemma mono_of_pullback (X Y : C) (f : X ⟶ Y)
  (hl : is_limit (pullback_cone.mk (𝟙 X) (𝟙 X) (by simp) : pullback_cone f f)) : mono f :=
begin
  split, intros,
  set new_cone : pullback_cone f f := pullback_cone.mk g h w,
  exact (hl.fac new_cone walking_cospan.left).symm.trans (hl.fac new_cone walking_cospan.right),
end

def pullback_of_mono {X Y : C} (f : X ⟶ Y) [hf : mono f] :
  is_limit (pullback_cone.mk (𝟙 X) (𝟙 X) rfl : pullback_cone f f) :=
pullback_square_iso' _ _ _ _ _

def mono_self_has_pullback_top {X Y : C} (f : X ⟶ Y) [hf : mono f] :
  has_pullback_top (𝟙 _) f f :=
{ top := 𝟙 _,
  comm := by simp,
  is_pb := pullback_of_mono f }

universe u₂
variables {D : Type u₂} [category.{v} D] (F : C ⥤ D)


def cone_cospan_equiv :
  cone (cospan (F.map f) (F.map g)) ≌ cone (cospan f g ⋙ F) :=
cones.postcompose_equivalence (iso.symm (diagram_iso_cospan _))

local attribute [tidy] tactic.case_bash

def convert_pb
  {W X Y Z : C}
  {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z} (comm : f ≫ g = h ≫ k) :
(cones.postcompose (diagram_iso_cospan _).hom).obj (F.map_cone (pullback_cone.mk _ _ comm)) ≅
    (pullback_cone.mk (F.map f) (F.map h) (by rw [← F.map_comp, comm, F.map_comp]) : pullback_cone (F.map g) (F.map k)) :=
cones.ext (iso.refl _) (by { dsimp [diagram_iso_cospan], tidy })

def thing2
  {W X Y Z : C}
  {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z} (comm : f ≫ g = h ≫ k) :
is_limit (F.map_cone (pullback_cone.mk _ _ comm)) ≅ is_limit (pullback_cone.mk (F.map f) (F.map h) (by rw [← F.map_comp, comm, F.map_comp]) : pullback_cone (F.map g) (F.map k)) :=
{ hom := λ p,
  begin
    apply is_limit.of_iso_limit _ (convert_pb F comm),
    apply is_limit.of_right_adjoint (cones.postcompose_equivalence ((diagram_iso_cospan _).symm)).inverse p,
  end,
  inv := λ p,
  begin
    have := is_limit.of_right_adjoint (cones.postcompose_equivalence (diagram_iso_cospan (cospan g k ⋙ F))).inverse p,
    apply is_limit.of_iso_limit this _,
    refine cones.ext (iso.refl _) _,
    dsimp [diagram_iso_cospan],
    simp_rw [id_comp],
    rintro (_ | _ | _),
    { dsimp, rw [comp_id, F.map_comp] },
    { dsimp, rw [comp_id] },
    { dsimp, rw [comp_id] },
  end,
  hom_inv_id' := subsingleton.elim _ _,
  inv_hom_id' := subsingleton.elim _ _ }

def preserves_pullback_cone
  [preserves_limits_of_shape walking_cospan F] {W X Y Z : C}
  (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (comm : f ≫ g = h ≫ k)
  (t : is_limit (pullback_cone.mk _ _ comm)) :
is_limit (pullback_cone.mk (F.map f) (F.map h) (by rw [← F.map_comp, comm, F.map_comp]) : pullback_cone (F.map g) (F.map k)) :=
(thing2 F comm).hom (preserves_limit.preserves t)

def reflects_pullback_cone
  [reflects_limits_of_shape walking_cospan F] {W X Y Z : C}
  {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z} (comm : f ≫ g = h ≫ k)
  (t : is_limit (pullback_cone.mk (F.map f) (F.map h) (by rw [← F.map_comp, comm, F.map_comp]) : pullback_cone (F.map g) (F.map k))) :
is_limit (pullback_cone.mk _ _ comm) :=
reflects_limit.reflects ((thing2 F comm).inv t)

lemma preserves_mono_of_preserves_pullback
  [preserves_limits_of_shape walking_cospan F] (X Y : C) (f : X ⟶ Y) [mono f] :
  mono (F.map f) :=
begin
  apply mono_of_pullback,
  have : 𝟙 (F.obj X) = F.map (𝟙 X),
    rw F.map_id,
  convert preserves_pullback_cone F (𝟙 _) f (𝟙 _) f rfl (pullback_of_mono f),
end

def preserves_walking_cospan_of_preserves_pb_cone {h : W ⟶ _} {k} (comm : h ≫ f = k ≫ g) (is_lim : is_limit (pullback_cone.mk _ _ comm))
  (t : is_limit (pullback_cone.mk (F.map h) (F.map k) (by rw [← F.map_comp, comm, F.map_comp]) : pullback_cone (F.map f) (F.map g))) :
  preserves_limit (cospan f g) F :=
begin
  apply preserves_limit_of_preserves_limit_cone is_lim,
  apply ((thing2 _ _).inv t),
end

def preserves_hpb [preserves_limits_of_shape walking_cospan F] {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z} (t : has_pullback_top h k g) :
has_pullback_top (F.map h) (F.map k) (F.map g) :=
{ top := F.map t.top,
  comm := by rw [← F.map_comp, t.comm, F.map_comp],
  is_pb := preserves_pullback_cone F _ _ _ _ t.comm t.is_pb }

def fully_faithful_reflects_hpb [reflects_limits_of_shape walking_cospan F] [full F] [faithful F] {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
  (t : has_pullback_top (F.map h) (F.map k) (F.map g)) :
has_pullback_top h k g :=
{ top := F.preimage t.top,
  comm := by { apply F.map_injective, simp [t.comm] },
  is_pb :=
  begin
    refine reflects_pullback_cone F _ _,
    convert t.is_pb,
    simp,
  end }

-- Strictly we don't need the assumption that C has pullbacks but oh well
def over_forget_preserves_hpb [has_pullbacks.{v} C] {B : C} {X Y Z W : over B} (g : X ⟶ Z) (h : Z ⟶ W) (k : Y ⟶ W) (t : has_pullback_top g h k) :
  has_pullback_top g.left h.left k.left :=
preserves_hpb over.forget t

def over_forget_reflects_hpb {B : C} {X Y Z W : over B} {g : X ⟶ Z} {h : Z ⟶ W} {k : Y ⟶ W}
  (t : has_pullback_top g.left h.left k.left ) :
  has_pullback_top g h k :=
{ top :=
  begin
    apply over.hom_mk t.top _,
    simp only [auto_param_eq, ← over.w k, t.comm_assoc, over.w h, over.w g],
  end,
  comm := by { ext1, exact t.comm },
  is_pb :=
  begin
    apply reflects_pullback_cone over.forget,
    apply t.is_pb,
    refine ⟨λ K, by apply_instance⟩,
  end }