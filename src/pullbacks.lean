import category_theory.limits.shapes.pullbacks
namespace  category_theory.limits
open category_theory
universes u v
variables {C : Type u} [𝒞 : category.{v} C]
variables {J K : Type v} [small_category J] [small_category K]
include 𝒞

lemma cone.ext {F : J ⥤ C} : Π (c₁ c₂: cone F), (c₁.X = c₂.X) → (c₁.π == c₂.π) → c₁ = c₂ :=
begin
  rintros ⟨X₁,π₁⟩ ⟨X₂,π₂⟩ h₁ h₂,
  cases h₁, cases h₂, refl,
end

variables {L X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {lx : L ⟶ X} {ly : L ⟶ Y} {e : lx ≫ f = ly ≫ g}
@[simp] def pullback_cone.simp_left : ((pullback_cone.mk lx ly e).π).app walking_cospan.left = lx := by refl
@[simp] def pullback_cone.simp_right : ((pullback_cone.mk lx ly e).π).app walking_cospan.right = ly := by refl

@[simp] lemma limit.lift_self_id (F : J ⥤ C) [has_limit F] :
  limit.lift F (limit.cone F) = 𝟙 (limit F) :=
begin
  symmetry,
  refine is_limit.uniq' _ _ _ _,
  intro j, simp, rw [category.id_comp _ (limit.π F j)]
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
  have c, apply @pullback.condition _ _ _ _ _ f g _,
  have xx : _ ≫ _ = limits.limit.π (cospan f g) walking_cospan.one,
    apply limits.limit.w (cospan f g) walking_cospan.hom.inl,
  rw ← xx,
  rw ← category.assoc,
  rw h1, simp,
end

@[simp] lemma pullback.lift_self_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_limit (cospan f g)]
: @pullback.lift _ _ _ X Y Z f g _ pullback.fst pullback.snd pullback.condition = 𝟙 _ :=
begin
  rw ←  limit.lift_self_id (cospan f g),
  dunfold pullback.lift limits.limit.cone pullback pullback_cone.mk pullback.fst pullback.snd limits.has_limit.cone limits.limit,
  congr, apply cone.ext, refl,
  simp, ext, cases x, refl, refl, apply limits.limit.w (cospan f g) walking_cospan.hom.inl,
end

/- Note that we need `has_pullbacks` even though this particular pullback always exists, because here we are showing that the
constructive limit derived using has_pullbacks has to be iso to this simple definition.  -/
lemma pullback.with_id_l [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback f (𝟙 Y) ≅ X :=
begin
  refine iso.mk (pullback.fst) (pullback.lift (𝟙 X) f (by simp)) _ _,
  apply pullback.hom_ext, simp, simp, rw pullback.condition, simp,
  simp,
end

/- [todo] find a way of showing this is iso to `pullback (𝟙 Y) f` -/
lemma pullback.with_id_r [@has_pullbacks C 𝒞] {X Y : C} (f : X ⟶ Y) :
  pullback (𝟙 Y) f ≅ X :=
begin
  refine iso.mk (pullback.snd) (pullback.lift f (𝟙 X) (by simp)) _ _,
  apply pullback.hom_ext, simp, rw ←pullback.condition, simp, simp,
  simp,
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
  {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (hm : @mono _ 𝒞 _ _ f) : @mono C 𝒞 (pullback f g) _ (pullback.snd) :=
begin
  split, intros A a b e,
  have c : pullback.fst ≫ f = pullback.snd ≫ g, apply pullback.condition,
  apply pullback.hom_ext,
    show a ≫ pullback.fst = b ≫ pullback.fst,
    apply hm.1, simp,
    rw c, rw ← category.assoc,  rw e, simp,
  show a ≫ pullback.snd = b ≫ pullback.snd, assumption,
end

end category_theory.limits