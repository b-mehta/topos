import category_theory.limits.shapes
import .comma

open category_theory category_theory.category category_theory.limits

universes u v
variables {C : Type u} [𝒞 : category.{v} C]
variables {J : Type v} [small_category J]
include 𝒞

variables {L X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {lx : L ⟶ X} {ly : L ⟶ Y} {e : lx ≫ f = ly ≫ g}
@[simp] lemma pullback_cone.simp_left : ((pullback_cone.mk lx ly e).π).app walking_cospan.left = lx := rfl
@[simp] lemma pullback_cone.simp_right : ((pullback_cone.mk lx ly e).π).app walking_cospan.right = ly := rfl

@[simp] lemma limit.lift_self_id (F : J ⥤ C) [has_limit F] :
  limit.lift F (limit.cone F) = 𝟙 (limit F) :=
begin
  symmetry, refine is_limit.uniq _ _ _ _,
  intro j, erw [id_comp _ (limit.π F j)], refl,
end

lemma pullback.hom_ext {X Y Z A : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
  (a b : A ⟶ pullback f g)
  (h1 : a ≫ pullback.fst = b ≫ pullback.fst)
  (h2 : a ≫ pullback.snd = b ≫ pullback.snd)
    : a = b :=
begin
  apply limit.hom_ext,
  intro j, cases j,
  apply h1, apply h2,
  rw ← limit.w (cospan f g) walking_cospan.hom.inl,
  rw ← assoc, rw h1, rw assoc
end

@[simp] lemma pullback.lift_self_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)] :
  pullback.lift pullback.fst pullback.snd pullback.condition = 𝟙 (pullback f g) :=
begin
  apply pullback.hom_ext,
  rw limit.lift_π, rw id_comp, refl,
  rw limit.lift_π, rw id_comp, refl
end

lemma iso_apex_of_iso_cone {F : J ⥤ C} {c₁ c₂ : cone F} (h : c₁ ≅ c₂) : c₁.X ≅ c₂.X :=
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

-- The pasting lemma for pullbacks. Something like this will invariably be useful
lemma pasting (C : Type u) [𝒞 : category.{v} C] {U V W X Y Z : C}
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
  end,
  inv :=
  begin
    intro left,
    refine ⟨λ c, _, λ c, _, λ c, _⟩,
    { have new_cone_comm: pullback_cone.fst c ≫ l = (pullback_cone.snd c ≫ m) ≫ n,
        rw assoc, rw pullback_cone.condition,
      have new_cone2_comm: (right.lift (pullback_cone.mk _ _ new_cone_comm)) ≫ k = (pullback_cone.snd c : c.X ⟶ X) ≫ m := right.fac' (pullback_cone.mk _ _ new_cone_comm) walking_cospan.right,
      exact left.lift (pullback_cone.mk _ _ new_cone2_comm) },
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

lemma pullback.with_id_r' {X Y : C} (f : X ⟶ Y) :
  is_limit (pullback_cone.mk f (𝟙 X) (by simp) : pullback_cone (𝟙 Y) f) :=
{ lift := λ c, (c.π).app walking_cospan.right,
  fac' := λ c j,
  begin
    cases j, -- BM: note triple cases
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

lemma flip_mk {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} (comm : f ≫ h = g ≫ k) :
  cospan_cone.flip (pullback_cone.mk f g comm) ≅ pullback_cone.mk g f comm.symm :=
by apply cones.ext (iso.refl _) (λ j, _); erw id_comp

lemma flip_twice {f : X ⟶ Z} {g : Y ⟶ Z} (c : cone (cospan f g)) : cospan_cone.flip (cospan_cone.flip c) ≅ c :=
begin
  apply cones.ext _ _, exact iso.refl _,
  intros j, erw id_comp, cases j, -- BM: triple case
  refl, refl,
  apply cone.w c walking_cospan.hom.inl
end

def flip_hom {f : X ⟶ Z} {g : Y ⟶ Z} {c₁ c₂ : cone (cospan f g)} (h : c₁ ⟶ c₂) : cospan_cone.flip c₁ ⟶ cospan_cone.flip c₂ :=
{ hom := h.hom,
  w' := begin rintro (_ | _ | _), apply h.w, apply h.w, erw [← assoc, h.w], refl end} -- BM: triple case

lemma pullback.flip {Y Z W : C} {h : Y ⟶ W} {k : Z ⟶ W} {c : cone (cospan h k)} :
  is_limit c ⟶ is_limit (cospan_cone.flip c) := λ z,
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
    intro j, cases j, -- BM: triple case
    erw J walking_cospan.right, refl,
    erw J walking_cospan.left, refl,
    erw [← cone.w c walking_cospan.hom.inl, ← assoc, J walking_cospan.right], refl
  end
}


lemma thing [@has_pullbacks C 𝒞] (f : X ⟶ Z) (g : Y ⟶ Z) :
  cospan_cone.flip (limit.cone (cospan g f)) ≅ limit.cone (cospan f g) :=
{ hom := limit.cone_morphism _, inv := ((flip_twice _).inv ≫ flip_hom (limit.cone_morphism _)),
  hom_inv_id' :=
  begin
    ext, simp, dunfold flip_hom flip_twice cones.ext, erw [id_comp, limit.lift_π],
    cases j, -- BM: triple case
    { erw limit.lift_π, refl },
    { erw limit.lift_π, refl },
    rw ← limit.w (cospan g f) walking_cospan.hom.inl,
    rw ← cone.w (cospan_cone.flip _) walking_cospan.hom.inl,
    rw ← assoc, congr, erw limit.lift_π, refl
  end,
  inv_hom_id' := is_limit.uniq_cone_morphism (limit.is_limit _) }

lemma pullback.flip' [@has_pullbacks C 𝒞] (f : X ⟶ Z) (g : Y ⟶ Z) : pullback f g ≅ pullback g f :=
begin
  dunfold pullback limit, have := pullback.flip (limit.is_limit (cospan g f)),
  have := @iso_apex_of_iso_cone _ _ _ _ _ (limit.cone (cospan f g)) (cospan_cone.flip (limit.cone (cospan g f))) _,
  apply iso.trans this, refl,
  dunfold limit.cone, apply (thing _ _).symm
end

lemma pullback.with_id_l' {X Y : C} (f : X ⟶ Y) :
  is_limit (pullback_cone.mk (𝟙 X) f (show (𝟙 X) ≫ f = f ≫ (𝟙 Y), by simp)) :=
is_limit.of_iso_limit (pullback.flip (pullback.with_id_r' f)) (flip_mk _)

/- Note that we need `has_pullbacks` even though this particular pullback always exists, because here we are showing that the
constructive limit derived using has_pullbacks has to be iso to this simple definition.  -/
lemma pullback.with_id_r [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback (𝟙 Y) f ≅ X :=
iso_apex_of_iso_cone (is_limit.unique_up_to_iso (limit.is_limit _) (pullback.with_id_r' f))

lemma pullback.with_id_l [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback f (𝟙 Y) ≅ X :=
pullback.flip' _ _ ≪≫ pullback.with_id_r f

lemma make_pullback [has_limit (cospan f g)] :
  pullback_cone.mk pullback.fst pullback.snd pullback.condition ≅ limit.cone (cospan f g) :=
begin
  apply cones.ext _ (λ j, _), refl, erw id_comp, cases j, refl, refl,
  show _ ≫ _ = _, rw limit.cone_π, rw ← limit.w (cospan f g) walking_cospan.hom.inl,
  refl
end

lemma pullback.comp_l {W X Y Z : C} {xz : X ⟶ Z} {yz : Y ⟶ Z} {wx : W ⟶ X} [@has_pullbacks C 𝒞]:
pullback (wx ≫ xz) yz ≅ pullback wx (@pullback.fst _ _ _ _ _ xz yz _) :=
begin
  apply iso.mk _ _ _ _ ,
  { refine pullback.lift pullback.fst (pullback.lift (pullback.fst ≫ wx) pullback.snd _) _, simp, rw pullback.condition,  simp},
  { refine pullback.lift pullback.fst (pullback.snd ≫ pullback.snd) _, rw ← category.assoc, rw pullback.condition,  simp, rw pullback.condition },
  {apply pullback.hom_ext, simp, simp },
  {apply pullback.hom_ext, simp, simp, apply pullback.hom_ext, simp, apply pullback.condition, simp},
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