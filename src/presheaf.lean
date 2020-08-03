import category_theory.monad.algebra
import pullbacks

namespace category_theory

open category_theory category_theory.category category_theory.limits comonad

universes v u

def mk_coalgebra_iso {D : Type u} [category.{v} D] {W : D ⥤ D} [comonad.{v} W] {x y : coalgebra W}
  (h : x.A ≅ y.A) (k : x.a ≫ W.map h.hom = h.hom ≫ y.a) : x ≅ y :=
begin
  apply as_iso _,
  refine ⟨h.1, k⟩,
  refine ⟨⟨h.2, _⟩, _, _⟩,
  dsimp,
  rw [h.eq_inv_comp, ← reassoc_of k, ← W.map_comp, h.hom_inv_id, W.map_id, comp_id],
  ext1,
  simp,
  ext1,
  simp,
end

variables {C : Type u} [small_category C]

@[simps]
def inner_functor (Y : Type u) : Cᵒᵖ ⥤ Type u :=
{ obj := λ X, Π T, (T ⟶ X.unop) → Y,
  map := λ X Z f t T g, t T (g ≫ f.unop) }

variable (C)
@[simps]
def W : Type u ⥤ Type u :=
{ obj := λ Y, Σ (x : Cᵒᵖ), (inner_functor Y).obj x,
  map := λ Y Z f Ue, ⟨Ue.1, λ T g, f (Ue.2 T g)⟩ }.

instance : comonad (W C) :=
{ ε := { app := λ Y Ue, Ue.2 Ue.1.unop (𝟙 _) },
  δ := { app := λ Y Ue, ⟨Ue.1, λ T f, ⟨opposite.op T, λ S g, Ue.2 S (g ≫ f)⟩⟩ },
  -- left_counit' := sorry,
  right_counit' :=
  begin
    intro Y,
    ext1 ⟨U, e⟩,
    dsimp [W],
    simp,
  end,
  coassoc' :=
  begin
    intro Y,
    ext1 ⟨U, e⟩,
    dsimp [W],
    congr' 1,
    ext T f : 2,
    congr' 1,
    ext S g : 2,
    congr' 1,
    dsimp,
    ext k,
    simp,
  end }.

def presheaf_to_coalgebra : (Cᵒᵖ ⥤ Type u) ⥤ coalgebra (W C) :=
{ obj := λ F,
  { A := sigma F.obj,
    a := λ y, ⟨y.1, λ x f, ⟨opposite.op x, F.map f.op y.2⟩⟩,
    counit' :=
    begin
      ext1 ⟨y, hy⟩,
      refine sigma.eq rfl _,
      change F.map (𝟙 y) hy = hy,
      rw F.map_id,
      refl,
    end,
    coassoc' :=
    begin
      ext1 ⟨Y, hY⟩,
      dsimp [W, comonad.δ],
      congr' 1,
      ext X f : 2,
      congr' 1,
      ext Z g : 2,
      congr' 1,
      rw F.map_comp,
      refl,
    end },
  map := λ F G α,
  { f := λ a, ⟨a.1, α.app a.1 a.2⟩,
    h' :=
    begin
      ext1 ⟨Y, hY⟩,
      dsimp [W],
      congr' 1,
      ext X f : 2,
      congr' 1,
      apply congr_fun (α.naturality f.op),
    end } }.

variables {C} (bar : coalgebra (W C)) (F : Cᵒᵖ ⥤ Type u)

-- Thanks to Chris Hughes for this idea!
lemma blah {α α' : Sort*} {β : α → Sort*} {β' : α' → Sort*} {γ : Sort*}
  {f : Π a, β a → γ} {f' : Π a, β' a → γ} {a : α} {a' : α'} {b : β a} {b' : β' a'}
  (hf : f == f')
  (hα : α = α') (hβ : β == β') (ha : a == a') (hb : b == b') :
  f a b = f' a' b' :=
by { subst hα, subst hβ, subst ha, subst hf, subst hb }

lemma heq_eq_to_hom {X Y Z : C} (hYZ : Y = Z) (g : X ⟶ Y) : g == g ≫ eq_to_hom hYZ :=
by { subst hYZ, simp }

@[simps]
def coalgebra_to_presheaf_obj (w : coalgebra (W C)) : Cᵒᵖ ⥤ Type u :=
{ obj := λ X, {i : _ // (w.a i).1 = X},
  map := λ X Y f a,
  begin
    refine ⟨_, _⟩,
    apply (w.a a.1).2 _ (f.unop ≫ eq_to_hom (opposite.op_injective a.2.symm)),
    have t := congr_fun w.coassoc a.1,
    dsimp [comonad.δ, W] at t,
    injection t with t₁ t₂,
    rw heq_iff_eq at t₂,
    replace t₂ := congr_fun t₂ Y.unop,
    replace t₂ := congr_fun t₂ (f.unop ≫ eq_to_hom (opposite.op_injective a.2.symm)),
    replace t₂ := congr_arg sigma.fst t₂,
    apply t₂.symm
  end,
  map_id' := λ X,
  begin
    ext1 ⟨a, ha⟩,
    dsimp,
    congr' 1,
    cases ha,
    rw id_comp,
    exact congr_fun w.counit a,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext1 ⟨a, ha⟩,
    subst ha,
    dsimp,
    rw comp_id,
    rw comp_id,
    congr' 1,
    have t := congr_fun w.coassoc a,
    dsimp [comonad.δ, W] at t,
    injection t with t₁ t₂,
    rw heq_iff_eq at t₂,
    replace t₂ := congr_fun t₂ Y.unop,
    replace t₂ := congr_fun t₂ f.unop,
    dsimp at t₂,
    rw ← sigma.eta (w.a ((w.a a).snd Y.unop f.unop)) at t₂,
    have := sigma.mk.inj t₂,
    rcases this with ⟨t₃, t₄⟩,
    refine blah t₄ rfl (heq_of_eq (by conv_lhs { rw t₃ })) (heq.refl _) _,
    apply heq_eq_to_hom,
  end,

}

@[simps]
def coalgebra_to_presheaf : coalgebra (W C) ⥤ Cᵒᵖ ⥤ Type u :=
{ obj := λ w, coalgebra_to_presheaf_obj w,
  map := λ X Y f,
  { app := λ Z a,
    begin
      refine ⟨f.f a.1, _⟩,
      have := congr_fun f.h a.1,
      dsimp at *,
      rw ← this,
      apply a.2,
    end,
    naturality' :=
    begin
      intros A B g,
      ext1 ⟨X, hX⟩,
      dsimp [coalgebra_to_presheaf_obj],
      congr' 1,
      have := f.h,
      dsimp [W] at this,
      have := congr_fun this X,
      dsimp at this,
      rw ← sigma.eta (Y.a (f.f X)) at this_1,
      injection this_1,
      cases hX,
      rw eq_to_hom_refl,
      rw comp_id,
      cases hX,
      refine blah h_2 rfl _ (heq.refl _) _,
      rw heq_iff_eq,
      funext,
      rw h_1,
      apply heq_eq_to_hom,
    end },
  map_id' := λ w,
  begin
    ext X ⟨_, _⟩,
    refl,
  end,
  map_comp' := λ w₁ w₂ w₃ f g,
  begin
    ext X ⟨_, _⟩,
    dsimp,
    refl,
  end }.

def presheaf_equiv_coalgebra : (Cᵒᵖ ⥤ Type u) ≌ coalgebra (W C) :=
equivalence.mk (presheaf_to_coalgebra C) (coalgebra_to_presheaf)
  (begin
    refine nat_iso.of_components _ _,
    { intro P,
      apply nat_iso.of_components _ _,
      { intro X,
        refine ⟨λ x, ⟨⟨X, x⟩, rfl⟩, λ a, P.map (eq_to_hom a.2) a.1.2, _, _⟩,
        { ext1 x,
          exact congr_fun (P.map_id _) x },
        { dsimp,
          ext1 ⟨⟨_, _⟩, hx⟩,
          cases hx,
          dsimp,
          congr,
          apply congr_fun (P.map_id _) } },
      { intros X Y f,
        ext : 2,
        change (⟨Y, P.map (f) x⟩ : Σ (x : _), _) = ⟨Y, P.map (𝟙 X ≫ f) x⟩,
        rw id_comp } },
    { intros P Q α,
      ext : 2,
      refl }
  end)
  (begin
    refine nat_iso.of_components _ _,
    { intro w,
      apply mk_coalgebra_iso _ _,
      { refine ⟨λ i, i.2.1, _, _, _⟩,
        { intro i,
          refine ⟨_, _, rfl⟩,
          apply i },
        { ext1 ⟨i, hi, t⟩,
          cases t,
          refl },
        { ext x,
          refl } },
      { ext1 ⟨i, hi, t⟩,
        cases t,
        dsimp [W, presheaf_to_coalgebra],
        conv_rhs {rw ← sigma.eta (w.a hi)},
        congr' 1,
        ext : 2,
        change (w.a hi).snd x (x_1 ≫ 𝟙 _) = (w.a hi).snd x x_1,
        rw comp_id } },
    { intros w₁ w₂ f,
      ext ⟨i, hi, t⟩ : 2,
      refl },
    end)

def tag (n : ℕ) (α : Sort*) (x : α) := x

def nice_pb {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : Type u := {i : X × Y // f i.1 = g i.2}
def proj₁ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : nice_pb f g ⟶ X := λ (i : nice_pb _ _), i.1.1
def proj₂ {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : nice_pb f g ⟶ Y := λ (i : nice_pb _ _), i.1.2
lemma square {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : proj₁ f g ≫ f = proj₂ f g ≫ g :=
begin
  ext ⟨i, hi⟩,
  apply hi,
end
def is_lim {X Y Z : Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : is_limit (pullback_cone.mk _ _ (square f g)) :=
is_limit.mk' _ $ λ s,
begin
  refine ⟨λ i, _, _, _, _⟩,
  refine ⟨⟨s.fst i, s.snd i⟩, congr_fun s.condition i⟩,
  ext i,
  refl,
  ext i,
  refl,
  intros m m₁ m₂,
  ext,
  dsimp, rw ← m₁, refl,
  dsimp, rw ← m₂, refl,
end

def construct_pb {W X Y Z : Type u} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ _} {k} (comm : h ≫ f = k ≫ g) :
  (Π Q (π₁ : Q ⟶ _) π₂, π₁ ≫ f = π₂ ≫ g → {l // l ≫ h = π₁ ∧ l ≫ k = π₂ ∧ ∀ m, m ≫ h = π₁ → m ≫ k = π₂ → m = l}) → is_limit (pullback_cone.mk _ _ comm) :=
begin
  intro q,
  apply is_limit.mk' _ _,
  intro s,
  exact q s.X s.fst s.snd s.condition,
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

def W_preserves_cospan {X Y Z : Type u} {f : X ⟶ Z} {g : Y ⟶ Z} : preserves_limit (cospan f g) (W C) :=
begin
  apply preserves_walking_cospan_of_preserves_pb_cone _ _ (is_lim _ _),
  apply construct_type_pb,
  rintros ⟨A, A'⟩ ⟨B, B'⟩ c,
  dsimp [inner_functor] at A' B',
  dsimp [W] at c,
  injection c with c₁ c₂,
  subst c₁,
  clear c,
  rw heq_iff_eq at c₂,
  have : ∀ (T : C) (h : T ⟶ A.unop), f (A' T h) = g (B' T h),
    intros T h,
    exact congr_fun (congr_fun c₂ T) h,
  clear c₂,
  refine ⟨⟨A, λ T h, ⟨⟨A' T h, B' T h⟩, this T h⟩⟩, rfl, rfl, _⟩,
  rintros ⟨M, M'⟩ m₁ m₂,
  dsimp [W, proj₁, proj₂] at m₁ m₂,
  injection m₁ with m₃ m₄,
  subst m₃,
  rw heq_iff_eq at m₄,
  cases m₄,
  injection m₂ with m₅ m₆,
  rw heq_iff_eq at m₆,
  cases m₆,
  congr' 1,
  ext T h;
  refl,
end

def W_preserves_pullbacks : preserves_limits_of_shape walking_cospan (W C) :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (diagram_iso_cospan _).symm,
    apply W_preserves_cospan,
  end }

def weird_functor : (Cᵒᵖ ⥤ Type u) ⥤ Type u :=
presheaf_to_coalgebra C ⋙ comonad.forget _

lemma weird_functor_obj (P : Cᵒᵖ ⥤ Type u) : weird_functor.obj P = sigma P.obj :=
rfl

end category_theory
