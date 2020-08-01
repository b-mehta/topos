/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.opposites
import category_theory.limits.lattice
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.full_subcategory
import category_theory.limits.shapes.regular_mono
import category_theory.closed.cartesian
import category_theory.limits.shapes.pullbacks
import category_theory.limits.over
import category_theory.monad.adjunction
import category_theory.currying
import category_theory.adjunction.fully_faithful
import sparse_skeleton
import over
import adjunction

universes v v₂ u u₂

namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

/--
The subobject category as a full subcategory of the over category. In particular this isn't
skeletal, so it's not a partial order. The quotient is taken in `subq` instead, it's useful to be
able to work with both.
It's reducible for now to get instances to happen quickly, marked semireducible again later.
-/
@[derive category]
def sub (X : C) := {f : over X // mono f.hom}
/-- The inclusion arrow from subobjects to the over category. -/
def forget_sub (X : C) : sub X ⥤ over X := full_subcategory_inclusion _
@[simp]
lemma forget_sub_obj_left {f} : ((forget_sub X).obj f).left = f.val.left := rfl
/-- Convenience notation for the underlying arrow of a subobject. -/
abbreviation sub.arrow (f : sub X) : _ ⟶ X := ((forget_sub X).obj f).hom
@[simp]
lemma forget_sub_obj_hom {f} : ((forget_sub X).obj f).hom = f.arrow := rfl

instance : full (forget_sub X) := full_subcategory.full _
instance : faithful (forget_sub X) := full_subcategory.faithful _

instance sub_mono (f : sub X) : mono f.arrow := f.property

/-- The subobject category is a thin category, which makes defining its skeleton easy. -/
instance is_thin {X : C} (f g : sub X) : subsingleton (f ⟶ g) :=
⟨begin
  intros h₁ h₂,
  ext1,
  erw [← cancel_mono g.arrow, over.w h₁, over.w h₂],
end⟩

@[reassoc] lemma sub.w {f g : sub X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow := over.w _

/-- Convience constructor for a morphism in the subobject category. -/
abbreviation sub.hom_mk {f g : sub X} (h : f.val.left ⟶ g.val.left) (w : h ≫ g.arrow = f.arrow) : f ⟶ g :=
over.hom_mk h w

@[derive [partial_order, category]]
def subq (X : C) := skel (sub X)

@[simps]
def sub.mk' {X A : C} (f : A ⟶ X) [hf : mono f] : sub X := { val := over.mk f, property := hf }
@[simp] lemma sub_mk'_arrow {X A : C} (f : A ⟶ X) [hf : mono f] : (sub.mk' f).arrow = f := rfl

@[simps]
def restrict_to_sub {Y : D} (F : over Y ⥤ over X)
  (h : ∀ (f : sub Y), mono (F.obj ((forget_sub Y).obj f)).hom) : sub Y ⥤ sub X :=
{ obj := λ f, ⟨_, h f⟩,
  map := λ _ _ k, (forget_sub X).preimage ((forget_sub Y ⋙ F).map k), }

def restrict_to_sub_iso {Y : D} {F₁ F₂ : over Y ⥤ over X} (h₁ h₂) (i : F₁ ≅ F₂) :
  restrict_to_sub F₁ h₁ ≅ restrict_to_sub F₂ h₂ :=
faithful_functor_right_cancel (forget_sub X) (iso_whisker_left (forget_sub Y) i)

def restrict_to_sub_comp {X Z : C} {Y : D} (F : over X ⥤ over Y) (G : over Y ⥤ over Z) (h₁ h₂) :
  restrict_to_sub F h₁ ⋙ restrict_to_sub G h₂ ≅ restrict_to_sub (F ⋙ G) (λ f, h₂ ⟨_, h₁ f⟩) :=
faithful_functor_right_cancel (forget_sub _) (iso.refl _)

def restrict_to_sub_id :
  restrict_to_sub (𝟭 (over X)) (λ f, f.2) ≅ 𝟭 _ :=
faithful_functor_right_cancel (forget_sub _) (iso.refl _)

@[simp]
lemma restrict_comm (F : over Y ⥤ over X)
  (h : ∀ (f : sub Y), mono (F.obj ((forget_sub Y).obj f)).hom) :
  restrict_to_sub F h ⋙ forget_sub X = forget_sub Y ⋙ F :=
rfl

def lower_sub {Y : D} (F : sub Y ⥤ sub X) : subq Y ⥤ subq X := skel_map F

lemma lower_sub_iso (F₁ F₂ : sub X ⥤ sub Y) (h : F₁ ≅ F₂) : lower_sub F₁ = lower_sub F₂ := skel_map_eq h

def lower_sub₂ (F : sub X ⥤ sub Y ⥤ sub Z) : subq X ⥤ subq Y ⥤ subq Z :=
skel_map₂ F

@[simp]
lemma lower_comm (F : sub Y ⥤ sub X) :
  skel_quotient _ ⋙ lower_sub F = F ⋙ skel_quotient _ :=
skel_quotient_map _

def sub.pullback [has_pullbacks.{v} C] (f : X ⟶ Y) : sub Y ⥤ sub X :=
restrict_to_sub (real_pullback f)
begin
  intro g,
  apply @pullback.snd_of_mono _ _ _ _ _ _ _ _ _,
  change mono g.arrow,
  apply_instance,
end

def sub.pullback_comp [has_pullbacks.{v} C] (f : X ⟶ Y) (g : Y ⟶ Z) :
  sub.pullback (f ≫ g) ≅ sub.pullback g ⋙ sub.pullback f :=
restrict_to_sub_iso _ _ (pullback_comp _ _) ≪≫ (restrict_to_sub_comp _ _ _ _).symm

def sub.pullback_id [has_pullbacks.{v} C] :
  sub.pullback (𝟙 X) ≅ 𝟭 _ :=
restrict_to_sub_iso _ _ pullback_id ≪≫ restrict_to_sub_id

@[simp] lemma sub.pullback_obj_arrow [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub Y) :
((sub.pullback f).obj g).arrow = pullback.snd :=
rfl

def subq.pullback [has_pullbacks.{v} C] (f : X ⟶ Y) : subq Y ⥤ subq X :=
lower_sub (sub.pullback f)

attribute [instance] mono_comp

def sub.post (f : X ⟶ Y) [mono f] : sub X ⥤ sub Y :=
restrict_to_sub (over.map f)
(λ g, by apply mono_comp g.arrow f)

def sub.post_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  sub.post (f ≫ g) ≅ sub.post f ⋙ sub.post g :=
restrict_to_sub_iso _ _ (over_map_comp _ _) ≪≫ (restrict_to_sub_comp _ _ _ _).symm

def sub.post_id : sub.post (𝟙 X) ≅ 𝟭 _ :=
restrict_to_sub_iso _ _ over_map_id ≪≫ restrict_to_sub_id

@[simp]
lemma sub.post_obj_arrow (f : X ⟶ Y) [mono f] (g : sub X) :
((sub.post f).obj g).arrow = g.arrow ≫ f := rfl

instance sub.full_post (f : X ⟶ Y) [mono f] : full (sub.post f) :=
{ preimage := λ g h e,
  begin
    refine sub.hom_mk e.left _,
    rw [← cancel_mono f, assoc],
    apply sub.w e,
  end }

instance sub.faithful_post (f : X ⟶ Y) [mono f] : faithful (sub.post f) := {}.

def subq.post (f : X ⟶ Y) [mono f] : subq X ⥤ subq Y :=
lower_sub (sub.post f)

@[simps]
def sub.image [has_images C] : over X ⥤ sub X :=
{ obj := λ f, sub.mk' (image.ι f.hom),
  map := λ f g k,
  begin
    apply (forget_sub X).preimage _,
    apply over.hom_mk _ _,
    refine image.lift {I := image _, m := image.ι g.hom, e := k.left ≫ factor_thru_image g.hom},
    apply image.lift_fac,
  end }

def image_forget_adj [has_images C] : sub.image ⊣ forget_sub X :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ f g,
  { to_fun := λ k,
    begin
      apply over.hom_mk (factor_thru_image f.hom ≫ k.left) _,
      change (factor_thru_image f.hom ≫ k.left) ≫ _ = f.hom,
      rw [assoc, over.w k],
      apply image.fac
    end,
    inv_fun := λ k,
    begin
      refine over.hom_mk _ _,
      refine image.lift {I := g.val.left, m := g.arrow, e := k.left, fac' := over.w k},
      apply image.lift_fac,
    end,
    left_inv := λ k, subsingleton.elim _ _,
    right_inv := λ k,
    begin
      ext1,
      change factor_thru_image _ ≫ image.lift _ = _,
      rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom],
      exact (over.w k).symm,
    end } }

instance [has_images C] : is_right_adjoint (forget_sub X) :=
{ left := sub.image, adj := image_forget_adj }

instance sub.reflective [has_images C] : reflective (forget_sub X) := {}.

def forget_image [has_images C] : forget_sub X ⋙ sub.image ≅ 𝟭 (sub X) :=
as_iso (adjunction.counit image_forget_adj)

def sub.exists [has_images C] (f : X ⟶ Y) : sub X ⥤ sub Y :=
forget_sub _ ⋙ over.map f ⋙ sub.image

def exists_iso_post [has_images C] (f : X ⟶ Y) [mono f] : sub.exists f ≅ sub.post f :=
nat_iso.of_components
begin
  intro Z,
  suffices : (forget_sub _).obj ((sub.exists f).obj Z) ≅ (forget_sub _).obj ((sub.post f).obj Z),
    apply preimage_iso this,
  apply over_iso _ _,
  apply image_mono_iso_source (Z.arrow ≫ f),
  apply image_mono_iso_source_hom_self,
end
begin
  intros Z₁ Z₂ g,
  ext1,
  change image.lift ⟨_, _, _, _⟩ ≫ (image_mono_iso_source (Z₂.arrow ≫ f)).hom =
         (image_mono_iso_source (Z₁.arrow ≫ f)).hom ≫ g.left,
  rw [← cancel_mono (Z₂.arrow ≫ f), assoc, assoc, sub.w_assoc g, image_mono_iso_source_hom_self,
      image_mono_iso_source_hom_self],
  apply image.lift_fac,
end

/-- post is adjoint to pullback for monos -/
def pull_post_adj (f : X ⟶ Y) [mono f] [has_pullbacks C] : sub.post f ⊣ sub.pullback f :=
restrict_adjunction (forget_sub X) (forget_sub Y) (radj f) (iso.refl _) (iso.refl _)

/-- image is adjoint to pullback if images exist -/
-- I really think there should be a high-level proof of this but not sure what it is...
def exists_pull_adj (f : X ⟶ Y) [has_images C] [has_pullbacks C] : sub.exists f ⊣ sub.pullback f :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g h,
  { to_fun := λ k,
    sub.hom_mk
      (begin
        refine pullback.lift (factor_thru_image _ ≫ k.1) g.arrow _,
        rw [assoc, sub.w k],
        apply image.fac,
       end)
      (pullback.lift_snd _ _ _),
    inv_fun := λ k, sub.hom_mk (image.lift ⟨_, h.arrow, k.left ≫ pullback.fst, by { rw [assoc, pullback.condition], apply sub.w_assoc }⟩) (image.lift_fac _),
    left_inv := λ k, subsingleton.elim _ _,
    right_inv := λ k, subsingleton.elim _ _ } }

-- Is this actually necessary?
def factors_through {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop := nonempty (over.mk f ⟶ over.mk g)

instance {X : C} : has_top (sub X) :=
{ top := sub.mk' (𝟙 _) }

def to_top (f : sub X) : f ⟶ ⊤ :=
sub.hom_mk f.arrow (comp_id _)

instance subq.order_top {X : C} : order_top (subq X) :=
{ top := ⟦⊤⟧,
  le_top :=
  begin
    refine quotient.ind _,
    exact λ f, ⟨to_top f⟩,
  end,
  ..category_theory.subq.partial_order X}

@[simp] lemma top_left (X : C) : (⊤ : sub X).val.left = X := rfl
@[simp] lemma top_arrow (X : C) : (⊤ : sub X).arrow = 𝟙 X := rfl

def sub.post_top (f : X ⟶ Y) [mono f] : (sub.post f).obj ⊤ ≅ sub.mk' f :=
iso_of_both_ways (sub.hom_mk (𝟙 _) rfl) (sub.hom_mk (𝟙 _) (by simp [id_comp f]))

def subq.post_top (f : X ⟶ Y) [mono f] : (subq.post f).obj ⊤ = ⟦sub.mk' f⟧ :=
quotient.sound ⟨sub.post_top f⟩

def sub.pullback_top (f : X ⟶ Y) [has_pullbacks C] : (sub.pullback f).obj ⊤ ≅ ⊤ :=
iso_of_both_ways (to_top _) (sub.hom_mk (pullback.lift f (𝟙 _) (by tidy)) (pullback.lift_snd _ _ _))

def subq.pullback_top (f : X ⟶ Y) [has_pullbacks C] : (subq.pullback f).obj ⊤ = ⊤ :=
quotient.sound ⟨sub.pullback_top f⟩

-- iso_of_both_ways (sub.hom_mk (𝟙 _) rfl) (sub.hom_mk (𝟙 _) (by simp [id_comp f]))

-- @[simp] lemma pullback_sub'_arrow_hom [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub'.{v} Y) :
-- (pullback_sub' f g).arrow.hom = pullback.snd := rfl

-- @[mono] lemma pullback_preserves_le' [has_pullbacks.{v} C] (f : X ⟶ Y) {g₁ g₂ : sub'.{v} Y} (h : g₁ ≤ g₂) :
--   pullback_sub' f g₁ ≤ pullback_sub' f g₂ :=
-- begin
--   rcases h with ⟨h₁, h₂⟩,
--   refine ⟨pullback.lift (pullback.fst ≫ h₁) pullback.snd (by simp [h₂, pullback.condition]), pullback.lift_snd _ _ _⟩,
-- end

-- lemma pullback_sub'_monotone [has_pullbacks.{v} C] (f : X ⟶ Y) : monotone (pullback_sub' f) := λ _ _, pullback_preserves_le' f


-- def postcompose_sub' (f : X ⟶ Y) [mono.{v} f] (g : sub'.{v} X) : sub'.{v} Y :=
-- sub'.mk' (g.arrow.hom ≫ f)

-- @[simp] lemma postcompose_sub'_arrow_hom (f : X ⟶ Y) [mono.{v} f] (g : sub'.{v} X) :
-- (postcompose_sub' f g).arrow.hom = g.arrow.hom ≫ f := rfl

-- @[mono] lemma postcompose_preserves_le' (f : X ⟶ Y) [mono f] {g₁ g₂ : sub'.{v} X} (h : g₁ ≤ g₂) :
--   postcompose_sub' f g₁ ≤ postcompose_sub' f g₂ :=
-- begin
--   rcases h with ⟨h₁, h₂⟩,
--   refine ⟨h₁, _⟩,
--   apply reassoc_of h₂,
-- end

-- lemma pullback_is_le' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} Y} : postcompose_sub' f (pullback_sub' f g₁) ≤ g₁ :=
-- ⟨pullback.fst, pullback.condition⟩

-- lemma pullback_is_le'' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} X} : pullback_sub' f (postcompose_sub' f g₁) ≤ g₁ :=
-- begin
--   refine ⟨pullback.fst, _⟩,
--   change pullback.fst ≫ g₁.arrow.hom = (pullback.snd : pullback (g₁.arrow.hom ≫ f) f ⟶ X),
--   rw [← cancel_mono f, assoc, pullback.condition],
-- end
-- lemma pullback_is_le''' [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] {g₁ : sub'.{v} X} : g₁ ≤ pullback_sub' f (postcompose_sub' f g₁) :=
-- begin
--   refine ⟨pullback.lift (𝟙 _) g₁.arrow.hom _, pullback.lift_snd _ _ _⟩,
--   rw [id_comp], refl,
-- end

-- def equiv (X : C) : sub'.{v} X → sub'.{v} X → Prop := λ f g, f ≤ g ∧ g ≤ f

-- lemma equiv_is_equivalence : _root_.equivalence (@equiv _ _ X) :=
-- ⟨λ f, ⟨le_refl _, le_refl _⟩, λ f g, and.symm, λ f g h a b, ⟨le_trans a.1 b.1, le_trans b.2 a.2⟩⟩

-- instance : setoid (sub' X) := ⟨equiv X, equiv_is_equivalence⟩

-- lemma pullback_sub'_id [has_pullbacks.{v} C] (x) : pullback_sub' (𝟙 X) x ≈ x :=
-- ⟨⟨pullback.fst, by simp [pullback.condition]⟩, ⟨pullback.lift (𝟙 _) x.arrow.hom (by simp), pullback.lift_snd _ _ _⟩⟩

-- lemma pullback_sub'_comp [has_pullbacks.{v} C] {Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (a) :
--   pullback_sub' (f ≫ g) a ≈ pullback_sub' f (pullback_sub' g a) :=
-- begin
--   split,
--   { refine ⟨pullback.lift (pullback.lift pullback.fst (pullback.snd ≫ _) _) _ (pullback.lift_snd _ _ _), pullback.lift_snd _ _ _⟩,
--     rw [pullback.condition, assoc] },
--   { refine ⟨pullback.lift (pullback.fst ≫ pullback.fst) _ _, pullback.lift_snd _ _ _⟩,
--     dsimp, rw [assoc, pullback.condition], apply pullback.condition_assoc, },
-- end

-- lemma postcompose_sub'_id (x) : postcompose_sub' (𝟙 X) x ≈ x :=
-- by split; exact ⟨𝟙 _, by {dsimp, simp}⟩

-- local attribute [instance] mono_comp

-- lemma postcompose_sub'_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (a) : postcompose_sub' (f ≫ g) a ≈ postcompose_sub' g (postcompose_sub' f a) :=
-- by split; exact ⟨𝟙 _, by {dsimp, simp}⟩

-- def sub (X : C) := quotient ⟨equiv X, equiv_is_equivalence⟩
-- def sub.mk {X A : C} (f : A ⟶ X) [hf : mono f] : sub X := ⟦sub'.mk' f⟧

-- instance : has_le (sub X) :=
-- ⟨ quotient.lift₂ (≤)
-- begin
--   intros a₁ a₂ b₁ b₂ h₁ h₂,
--   apply propext,
--   refine ⟨λ a₁a₂, le_trans h₁.2 (le_trans a₁a₂ h₂.1), λ b₁b₂, le_trans h₁.1 (le_trans b₁b₂ h₂.2)⟩,
-- end ⟩

-- def preorder_sub : preorder (sub X) :=
-- { le := has_le.le,
--   le_refl := λ Y, quotient.ind le_refl Y,
--   le_trans := λ A B C, quotient.induction_on₃ A B C (λ a b c, le_trans) }

-- instance sub_partial : partial_order (sub X) :=
-- { le_antisymm := λ a b, quotient.induction_on₂ a b (λ _ _ h k, quotient.sound ⟨h, k⟩),
--   ..preorder_sub }

-- @[simps]
-- def sub.quotient (A : C) : sub' A ⥤ sub A :=
-- { obj := quotient.mk,
--   map := λ X Y f, f }

-- -- instance (A : C) : full (sub.quotient A) :=
-- -- { preimage := λ X Y f, f }

-- -- instance (A : C) : faithful (sub.quotient A) := {}.

-- @[simps]
-- def lower_functor {A B : C} (F : sub' A ⥤ sub' B) :
--   sub A ⥤ sub B :=
-- { obj :=
--   begin
--     apply quotient.map F.obj _,
--     rintros _ _ ⟨q, r⟩,
--     exact ⟨(F.map ⟨⟨q⟩⟩).down.down, (F.map ⟨⟨r⟩⟩).down.down⟩,
--   end,
--   map :=
--   begin
--     rintros _ _ le,
--     refine ⟨⟨_⟩⟩,
--     rcases le with ⟨⟨_⟩⟩,
--     revert le,
--     apply quotient.induction_on₂ X Y,
--     intros _ _ q,
--     exact (F.map ⟨⟨q⟩⟩).1.1,
--   end }

-- def lower_func_quot {A B : C} (F : sub' A ⥤ sub' B) :
--   F ⋙ sub.quotient B ≅ sub.quotient A ⋙ lower_functor F :=
-- nat_iso.of_components (λ _, iso.refl _) (λ _ _ _, by ext)

-- def lower_functor₂ {A B c : C} (F : sub' A ⥤ sub' B ⥤ sub' c) :
--   sub A ⥤ sub B ⥤ sub c :=
-- { obj :=
--   begin
--     refine quotient.lift _ _,
--     intro x,
--     apply lower_functor (F.obj x),
--     rintros a b ⟨q, r⟩,
--     apply functor.ext _ _,
--     apply quotient.ind,
--     intro z,
--     apply quotient.sound,
--     refine ⟨((F.map ⟨⟨q⟩⟩).app z).1.1, ((F.map ⟨⟨r⟩⟩).app z).1.1⟩,
--     intros, ext,
--   end,
--   map :=
--   begin
--     intros X Y le,
--     refine { app := _, naturality' := _ },
--     intro Z,
--     refine ⟨⟨_⟩⟩,
--     revert le,
--     apply quotient.induction_on₃ X Y Z,
--     intros _ _ _ q,
--     exact ((F.map q).app c_1).1.1,
--     intros,
--     ext,
--   end }

-- --   begin
-- --     apply quotient.map F.obj _,
-- --     rintros _ _ ⟨q, r⟩,
-- --     exact ⟨(F.map ⟨⟨q⟩⟩).down.down, (F.map ⟨⟨r⟩⟩).down.down⟩,
-- --   end,
-- --   map :=
-- --   begin
-- --     rintros _ _ le,
-- --     refine ⟨⟨_⟩⟩,
-- --     rcases le with ⟨⟨_⟩⟩,
-- --     revert le,
-- --     apply quotient.induction_on₂ X Y,
-- --     intros _ _ q,
-- --     exact (F.map ⟨⟨q⟩⟩).1.1,
-- --   end }

-- def sub.unquotient' {A : C} (esc : sub A → sub' A) (valid : quotient.mk ∘ esc = id) : sub A ⥤ sub' A :=
-- { obj := esc,
--   map := λ x y f,
--   begin
--     refine ⟨⟨_⟩⟩,
--     have hx := congr_fun valid x,
--     have hy := congr_fun valid y,
--     dsimp at hx hy,
--     rcases f with ⟨⟨_⟩⟩,
--     rw [← hx, ← hy] at f,
--     exact f,
--   end }

-- def pullback_sub [has_pullbacks.{v} C] {Y : C} (f : X ⟶ Y) : sub Y → sub X :=
-- quotient.map (pullback_sub' f) $ λ a b ⟨_, _⟩, by split; mono

-- lemma sub.pullback_id [has_pullbacks.{v} C] (x : sub X) : (sub.pullback (𝟙 X)).obj x ≈ x :=
-- begin

--   -- apply equiv_of_both_ways,
--   -- refine sub.hom_mk pullback.fst _,
--   -- erw [pullback.condition, category.comp_id], refl,
--   -- refine sub.hom_mk (pullback.lift (𝟙 _) x.arrow _) _,
--   -- rw [id_comp, comp_id], refl,
--   -- apply pullback.lift_snd,
-- end
-- lemma pullback_sub'_comp [has_pullbacks.{v} C] {Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (a) :
--   (sub.pullback (f ≫ g)).obj a ≈ (sub.pullback f).obj ((sub.pullback g).obj a) :=
-- begin
--   apply equiv_of_both_ways,
--   refine sub.hom_mk (pullback.lift (pullback.lift pullback.fst (pullback.snd ≫ f) _) _ _) _,

--   -- refine sub.hom_mk pullback.fst _,
--   -- erw [pullback.condition, category.comp_id], refl,
--   -- refine sub.hom_mk (pullback.lift (𝟙 _) x.arrow _) _,
--   -- rw [id_comp, comp_id], refl,
--   -- apply pullback.lift_snd,
-- end
lemma subq.pullback_id [has_pullbacks.{v} C] (x : subq X) : (subq.pullback (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on x,
  intro f,
  apply quotient.sound,
  exact ⟨sub.pullback_id.app f⟩,
end
lemma subq.pullback_comp [has_pullbacks.{v} C] (f : X ⟶ Y) (g : Y ⟶ Z) (x : subq Z) : (subq.pullback (f ≫ g)).obj x = (subq.pullback f).obj ((subq.pullback g).obj x) :=
begin
  apply quotient.induction_on x,
  intro t,
  apply quotient.sound,
  refine ⟨(sub.pullback_comp _ _).app t⟩,
end

variable (C)

@[simps]
def subq.functor [has_pullbacks.{v} C] : Cᵒᵖ ⥤ Type (max u v) :=
{ obj := λ X, subq X.unop,
  map := λ X Y f, (subq.pullback f.unop).obj,
  map_id' := λ X, funext subq.pullback_id,
  map_comp' := λ X Y Z f g, funext (subq.pullback_comp _ _) }

variable {C}

-- def postcompose {X Y : C} (f : X ⟶ Y) [mono f] : sub X → sub Y :=
-- quotient.map (postcompose_sub' f) $ λ a b ⟨_, _⟩, by split; mono

-- lemma postcompose_map_id : ∀ g, postcompose (𝟙 X) g = g :=
-- begin
--   apply quotient.ind,
--   intro a,
--   apply quotient.sound (postcompose_sub'_id a),
-- end

-- lemma postcompose_map_comp {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] : ∀ h, postcompose (f ≫ g) h = postcompose g (postcompose f h) :=
-- begin
--   apply quotient.ind,
--   intro a,
--   apply quotient.sound (postcompose_sub'_comp _ _ _),
-- end

-- @[simps]
-- def postcompose_sub_equiv_of_iso (e : X ≅ Y) : sub X ≃ sub Y :=
-- { to_fun := postcompose e.hom,
--   inv_fun := postcompose e.inv,
--   left_inv := λ g, by simp_rw [← postcompose_map_comp, e.hom_inv_id, postcompose_map_id],
--   right_inv := λ g, by simp_rw [← postcompose_map_comp, e.inv_hom_id, postcompose_map_id] }

lemma postcompose_pullback_comm' [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk f g comm)) (a) :
  (sub.post g).obj ((sub.pullback f).obj a) ≈ (sub.pullback k).obj ((sub.post h).obj a) :=
begin
  apply equiv_of_both_ways,
  { refine sub.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
    rw [assoc, ← comm, pullback.condition_assoc] },
  { refine sub.hom_mk (pullback.lift pullback.fst
                       (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
                       (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
    { rw [← pullback.condition, assoc], refl },
    { erw [pullback.lift_snd_assoc], apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
end

lemma postcompose_pullback_comm [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) :
  ∀ p, (subq.post g).obj ((subq.pullback f).obj p) = (subq.pullback k).obj ((subq.post h).obj p) :=
begin
  apply quotient.ind,
  intro a,
  apply quotient.sound (postcompose_pullback_comm' t a),
end

lemma sub.pull_post_self [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] (g₁ : sub X) :
  sub.post f ⋙ sub.pullback f ≅ 𝟭 _ :=
(as_iso (pull_post_adj f).unit).symm

lemma subq.pull_post_self [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] :
  ∀ g₁, (subq.pullback f).obj ((subq.post f).obj g₁) = g₁ :=
begin
  apply quotient.ind,
  intro g,
  apply quotient.sound,
  exact ⟨(sub.pull_post_self f g).app _⟩,
end

instance over_mono {B : C} {f g : over B} (m : f ⟶ g) [mono m] : mono m.left :=
⟨λ A h k e,
begin
  let A' : over B := over.mk (k ≫ f.hom),
  have: h ≫ f.hom = k ≫ f.hom,
    rw ← over.w m, rw reassoc_of e,
  let h' : A' ⟶ f := over.hom_mk h,
  let k' : A' ⟶ f := over.hom_mk k,
  have : h' ≫ m = k' ≫ m := over.over_morphism.ext e,
  rw cancel_mono m at this,
  injection this
end⟩

def over_mono' {B : C} {f g : over B} (m : f ⟶ g) [mono m.left] : mono m :=
{right_cancellation := λ A h k e, over.over_morphism.ext ((cancel_mono m.left).1 (congr_arg comma_morphism.left e))}

@[simps]
def preorder_functor {α β : Type*} [preorder α] [preorder β] (f : α → β) (hf : monotone f) : α ⥤ β :=
{ obj := f,
  map := λ X Y ⟨⟨h⟩⟩, ⟨⟨hf h⟩⟩ }

@[simps]
def preorder_equivalence {α β : Type*} [preorder α] [preorder β] (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop))
  : α ≌ β :=
{ functor := preorder_functor f (λ x y, f.ord.1),
  inverse := preorder_functor f.symm (λ a b h, by rwa [f.ord, f.apply_symm_apply, f.apply_symm_apply]),
  unit_iso := nat_iso.of_components (λ X, eq_to_iso (f.left_inv _).symm) (λ X Y f, rfl),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso (f.right_inv _)) (λ X Y f, rfl) }

instance iso_term (A : C) [has_terminal (over A)] : is_iso (⊤_ over A).hom :=
begin
  let := (⊤_ over A).hom,
  dsimp at this,
  let ident : over A := over.mk (𝟙 A),
  let k : ident ⟶ (⊤_ over A) := default _,
  haveI : split_epi (⊤_ over A).hom := ⟨k.left, over.w k⟩,
  let l : (⊤_ over A) ⟶ ident := over.hom_mk (⊤_ over A).hom (comp_id _),
  haveI : mono l := ⟨λ _ _ _ _, subsingleton.elim _ _⟩,
  haveI : mono (⊤_ over A).hom := category_theory.over_mono l,
  apply is_iso_of_mono_of_split_epi,
end

def sub_iso {A B : C} (e : A ≅ B) : sub A ≌ sub B :=
{ functor := sub.post e.hom,
  inverse := sub.post e.inv,
  unit_iso := ((sub.post_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ sub.post_id).symm,
  counit_iso := ((sub.post_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ sub.post_id) }

def sub_slice {A : C} {f : over A} (h₁ h₂) : sub f ≌ sub f.left :=
{ functor := restrict_to_sub f.iterated_slice_equiv.functor h₁,
  inverse := restrict_to_sub f.iterated_slice_equiv.inverse h₂,
  unit_iso := restrict_to_sub_id.symm ≪≫ restrict_to_sub_iso _ _ f.iterated_slice_equiv.unit_iso ≪≫ (restrict_to_sub_comp _ _ _ _).symm,
  counit_iso := restrict_to_sub_comp _ _ _ _ ≪≫ restrict_to_sub_iso _ _ f.iterated_slice_equiv.counit_iso ≪≫ restrict_to_sub_id }

def subq.equiv {A : C} {B : D} (e : sub A ≌ sub B) : subq A ≌ subq B :=
{ functor := lower_sub e.functor,
  inverse := lower_sub e.inverse,
  unit_iso := skel_map_id.symm ≪≫ skel_map_iso e.unit_iso ≪≫ skel_map_comp _ _,
  counit_iso := (skel_map_comp _ _).symm ≪≫ skel_map_iso e.counit_iso ≪≫ skel_map_id }

def sub_one_over (A : C) [has_terminal (over A)] : subq A ≌ subq (⊤_ (over A)) :=
begin
  refine subq.equiv ((sub_iso (as_iso (⊤_ over A).hom).symm).trans (sub_slice _ _).symm),
  intro f, dsimp, apply_instance,
  intro f,
  apply over_mono' _,
  dsimp,
  apply_instance,
end

@[simps]
def sub.intersection [has_pullbacks.{v} C] {A : C} : sub A ⥤ sub A ⥤ sub A :=
{ obj := λ f, sub.pullback f.arrow ⋙ sub.post f.arrow,
  map := λ f₁ f₂ k,
  { app := λ g,
    begin
      apply sub.hom_mk _ _,
      apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _,
      rw [pullback.condition, assoc, sub.w k],
      dsimp,
      rw [pullback.lift_snd_assoc, assoc, sub.w k],
    end } }.

def sub.inter_le_left [has_pullbacks.{v} C] {A : C} (f g : sub A) :
  (sub.intersection.obj f).obj g ⟶ f :=
sub.hom_mk _ rfl

def sub.inter_le_right [has_pullbacks.{v} C] {A : C} (f g : sub A) :
  (sub.intersection.obj f).obj g ⟶ g :=
sub.hom_mk _ pullback.condition

def sub.le_inter [has_pullbacks.{v} C] {A : C} (f g h : sub A) :
  (h ⟶ f) → (h ⟶ g) → (h ⟶ (sub.intersection.obj f).obj g) :=
begin
  intros k₁ k₂,
  refine sub.hom_mk (pullback.lift k₂.left k₁.left _) _,
  rw [sub.w k₁, sub.w k₂],
  erw [pullback.lift_snd_assoc, sub.w k₁],
end

def subq.intersection [has_pullbacks.{v} C] {A : C} : subq A ⥤ subq A ⥤ subq A :=
skel_map₂ sub.intersection

lemma subq.inf_le_left [has_pullbacks.{v} C] {A : C} (f g : subq A) :
  (subq.intersection.obj f).obj g ≤ f :=
quotient.induction_on₂ f g (λ a b, ⟨sub.inter_le_left _ _⟩)

lemma subq.inf_le_right [has_pullbacks.{v} C] {A : C} (f g : subq A) :
  (subq.intersection.obj f).obj g ≤ g :=
quotient.induction_on₂ f g (λ a b, ⟨sub.inter_le_right _ _⟩)

lemma subq.le_inf [has_pullbacks.{v} C] {A : C} (h f g : subq A) :
  h ≤ f → h ≤ g → h ≤ (subq.intersection.obj f).obj g :=
quotient.induction_on₃ h f g
begin
  rintros f g h ⟨k⟩ ⟨l⟩,
  exact ⟨sub.le_inter _ _ _ k l⟩,
end

@[simps]
def over.coprod' [has_coproducts.{v} C] {A : C} : over A → over A ⥤ over A := λ f,
{ obj := λ g, over.mk (coprod.desc f.hom g.hom),
  map := λ g₁ g₂ k, over.hom_mk (coprod.map (𝟙 _) k.left) }

@[simps]
def over.coprod [has_coproducts.{v} C] {A : C} : over A ⥤ over A ⥤ over A :=
{ obj := λ f, over.coprod' f,
  map := λ f₁ f₂ k,
  { app := λ g, over.hom_mk (coprod.map k.left (𝟙 _)) (by { dsimp, rw [coprod.map_desc, id_comp, over.w k] }) } }.

def sub.union [has_images.{v} C] [has_coproducts.{v} C] {A : C} : sub A ⥤ sub A ⥤ sub A :=
curry_obj ((forget_sub A).prod (forget_sub A) ⋙ uncurry.obj over.coprod ⋙ sub.image)

def sub.le_union_left [has_images.{v} C] [has_coproducts.{v} C] {A : C} (f g : sub A) :
  f ⟶ (sub.union.obj f).obj g :=
begin
  refine sub.hom_mk (coprod.inl ≫ factor_thru_image _) _,
  erw [assoc, image.fac, coprod.inl_desc],
  refl,
end

def sub.le_union_right [has_images.{v} C] [has_coproducts.{v} C] {A : C} (f g : sub A) :
  g ⟶ (sub.union.obj f).obj g :=
begin
  refine sub.hom_mk (coprod.inr ≫ factor_thru_image _) _,
  erw [assoc, image.fac, coprod.inr_desc],
  refl,
end

def sub.union_le [has_images.{v} C] [has_coproducts.{v} C] {A : C} (f g h : sub A) :
  (f ⟶ h) → (g ⟶ h) → ((sub.union.obj f).obj g ⟶ h) :=
begin
  intros k₁ k₂,
  refine sub.hom_mk _ _,
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩,
  { dsimp,
    ext1,
    { simp [sub.w k₁] },
    { simp [sub.w k₂] } },
  { apply image.lift_fac }
end

def subq.union [has_images.{v} C] [has_coproducts.{v} C] {A : C} : subq A ⥤ subq A ⥤ subq A :=
skel_map₂ sub.union

-- def intersection' [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub A) : sub A :=
-- postcompose_sub' f₂.arrow.hom (pullback_sub' f₂.arrow.hom f₁)

-- lemma intersection'_le_left [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub'.{v} A) : intersection' f₁ f₂ ≤ f₁ :=
-- pullback_is_le' f₂.arrow.hom

-- lemma intersection'_le_right [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub'.{v} A) : intersection' f₁ f₂ ≤ f₂ :=
-- ⟨pullback.snd, rfl⟩

-- lemma le_intersection' [has_pullbacks.{v} C] {A : C} {f₁ f₂ f₃ : sub'.{v} A} (h₁ : f₃ ≤ f₁) (h₂ : f₃ ≤ f₂) : f₃ ≤ intersection' f₁ f₂ :=
-- begin
--   cases h₁, cases h₂,
--   refine ⟨pullback.lift h₁_w h₂_w (by simp [h₁_h, h₂_h]), _⟩,
--   erw [pullback.lift_snd_assoc, h₂_h],
-- end

-- def intersection [has_pullbacks.{v} C] {A : C} : sub A → sub A → sub A :=
-- begin
--   refine quotient.map₂ intersection' _,
--   rintros a₁ a₂ ⟨a₁₂, a₂₁⟩ b₁ b₂ ⟨b₁₂, b₂₁⟩,
--   split;
--   refine le_intersection' (le_trans (intersection'_le_left _ _) ‹_›) (le_trans (intersection'_le_right _ _) ‹_›),
-- end

lemma sub.intersection_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub A) :
  (sub.intersection.obj f₁).obj f₂ = (sub.post f₁.arrow).obj ((sub.pullback f₁.arrow).obj f₂) :=
rfl
lemma subq.intersection_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ : sub A) (f₂ : subq A) :
  (subq.intersection.obj ⟦f₁⟧).obj f₂ = (subq.post f₁.arrow).obj ((subq.pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on f₂,
  intro f₂,
  refl,
end

-- def sub'_top (A : C) : sub'.{v} A := sub'.mk' (𝟙 _)

-- @[simp]
-- lemma sub'_top_arrow_hom (A : C) : (sub'_top A).arrow.hom = 𝟙 _ := rfl

-- lemma sub'_le_top {A : C} (f : sub'.{v} A) : f ≤ sub'_top A :=
-- ⟨f.arrow.hom, comp_id _⟩

-- def sub_top (A : C) : sub A := ⟦sub'_top A⟧

-- instance sub_order_top {A : C} : order_top (sub A) :=
-- { top := sub_top A,
--   le_top := λ f, quotient.induction_on f sub'_le_top,
--   ..category_theory.sub_partial }

instance [has_pullbacks.{v} C] {B : C} : semilattice_inf_top (subq B) :=
{ le := (≤),
  inf := λ m n, (subq.intersection.obj m).obj n,
  inf_le_left := subq.inf_le_left,
  inf_le_right := subq.inf_le_right,
  le_inf := subq.le_inf,
  ..category_theory.subq.order_top }

lemma prod_eq_inter {A : C} {f₁ f₂ : subq A} [has_pullbacks.{v} C] : (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
begin
  change f₁ ⊓ (f₂ ⊓ ⊤) = f₁ ⊓ f₂,
  rw inf_top_eq,
end

lemma inf_eq_intersection {B : C} (m m' : subq B) [has_pullbacks.{v} C] :
  m ⊓ m' = (subq.intersection.obj m).obj m' := rfl

lemma top_eq_id {B : C} : (⊤ : subq B) = ⟦sub.mk' (𝟙 B)⟧ := rfl

/-- Intersection plays well with pullback. -/
lemma inf_pullback [has_pullbacks.{v} C] {X Y : C} (g : X ⟶ Y) (f₂) :
  ∀ f₁, (subq.pullback g).obj (f₁ ⊓ f₂) = (subq.pullback g).obj f₁ ⊓ (subq.pullback g).obj f₂ :=
quotient.ind begin
  intro f₁,
  erw [inf_eq_intersection, inf_eq_intersection, subq.intersection_eq_post_pull,
       subq.intersection_eq_post_pull, ← subq.pullback_comp,
       ← postcompose_pullback_comm pullback.condition (cone_is_pullback f₁.arrow g),
       ← subq.pullback_comp, pullback.condition],
  refl,
end

def sub.top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (⊤ : sub A) ⟶ (sub.pullback f).obj (sub.mk' f) :=
sub.hom_mk _ (pullback.lift_snd _ _ rfl)

def sub.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (sub.pullback f).obj (sub.mk' f) ≅ ⊤ :=
iso_of_both_ways (to_top _) (sub.top_le_pullback_self _)

lemma subq.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (subq.pullback f).obj ⟦sub.mk' f⟧ = ⊤ :=
quotient.sound ⟨sub.pullback_self f⟩

-- lemma pullback_self_eq_top {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] : pullback_sub f (sub.mk f) = ⊤ :=
-- quotient.sound (pullback_self'_eq_top f)

-- lemma top_le_pullback'_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : sub'_top _ ≤ pullback_sub' f (sub'_top _) :=
-- ⟨pullback.lift _ _ (by { dsimp, simp }), pullback.lift_snd _ _ _⟩

-- lemma pullback'_top_eq_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : pullback_sub' f (sub'_top _) ≈ sub'_top _ :=
-- ⟨sub'_le_top _, top_le_pullback'_top f⟩

-- lemma pullback_top {A B : C} (f : A ⟶ B) [has_pullbacks.{v} C] : pullback_sub f ⊤ = ⊤ :=
-- quotient.sound (pullback'_top_eq_top f)

local attribute [instance] has_pullbacks_of_has_finite_limits

variable [has_finite_limits.{v} C]

instance mono_prod_lift_of_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono f] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.fst,
  simp at this,
  rwa cancel_mono at this,
end

instance mono_prod_lift_of_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono g] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.snd,
  simp at this,
  rwa cancel_mono at this,
end

instance subterminal_ideal {A B : C} [exponentiable B] [mono (default (A ⟶ ⊤_ C))] :
  mono (default (A^^B ⟶ ⊤_ C)) :=
⟨λ Z f g eq, begin
  apply uncurry_injective,
  rw ← cancel_mono (default (A ⟶ ⊤_ C)),
  apply subsingleton.elim,
end⟩

/-- Auxiliary def for the exponential in the subobject category `sub 1`. -/
def sub.exp_aux (A : C) [exponentiable A] : sub (⊤_ C) ⥤ sub (⊤_ C) :=
{ obj := λ f,
  { val := over.mk (default (f.val.left^^A ⟶ ⊤_ C)),
    property :=
    ⟨λ Z g h eq, uncurry_injective (by { rw ← cancel_mono f.arrow, apply subsingleton.elim })⟩ },
  map := λ f₁ f₂ h, sub.hom_mk ((exp A).map h.left) (subsingleton.elim _ _) }

@[simps]
def sub.exp_aux_left {A₁ A₂ : C} [exponentiable A₁] [exponentiable A₂] (f : A₁ ⟶ A₂) :
  sub.exp_aux A₂ ⟶ sub.exp_aux A₁ :=
{ app := λ g, sub.hom_mk (pre _ f) (subsingleton.elim _ _) }

lemma sub_exp_aux_left_comp {A₁ A₂ A₃ : C} [cartesian_closed C] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
  sub.exp_aux_left (f ≫ g) = sub.exp_aux_left g ≫ sub.exp_aux_left f :=
begin
  ext : 3,
  apply pre_map,
end
lemma sub_exp_aux_left_id {A₁ : C} [cartesian_closed C] :
  sub.exp_aux_left (𝟙 A₁) = 𝟙 _ :=
begin
  ext : 3,
  apply pre_id,
end

/-- Candidate for the exponential functor in sub 1. -/
def sub.exp (f : sub (⊤_ C)) [cartesian_closed C] : sub (⊤_ C) ⥤ sub (⊤_ C) :=
sub.exp_aux f.val.left

def sub.exp_equiv (f₁ f₂ f₃ : sub (⊤_ C)) [cartesian_closed C] :
  ((sub.intersection.obj f₂).obj f₁ ⟶ f₃) ≃ (f₁ ⟶ (sub.exp f₂).obj f₃) :=
{ to_fun := λ k,
  begin
    refine sub.hom_mk (cartesian_closed.curry _) (subsingleton.elim _ _),
    apply (pullback.lift limits.prod.snd limits.prod.fst _) ≫ k.left,
    dsimp,
    apply subsingleton.elim,
  end,
  inv_fun := λ k, sub.hom_mk (prod.lift pullback.snd pullback.fst ≫ cartesian_closed.uncurry k.left) (subsingleton.elim _ _),
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _ }

def subq.exp_aux [cartesian_closed C] (f : sub (⊤_ C)) : subq (⊤_ C) ⥤ subq (⊤_ C) :=
lower_sub (sub.exp f)

def subq.exp (f : subq (⊤_ C)) [cartesian_closed C] : subq (⊤_ C) ⥤ subq (⊤_ C) :=
begin
  apply quotient.lift_on f subq.exp_aux _,
  rintros f₁ f₂ ⟨h⟩,
  apply lower_sub_iso,
  have hi : h.hom.left ≫ h.inv.left = 𝟙 _,
    change (h.hom ≫ h.inv).left = _,
    rw h.hom_inv_id, refl,
  have ih : h.inv.left ≫ h.hom.left = 𝟙 _,
    change (h.inv ≫ h.hom).left = _,
    rw h.inv_hom_id, refl,
  refine ⟨sub.exp_aux_left h.inv.left, sub.exp_aux_left h.hom.left, _, _⟩,
  rw [← sub_exp_aux_left_comp, hi, sub_exp_aux_left_id], exact rfl,
  rw [← sub_exp_aux_left_comp, ih, sub_exp_aux_left_id], exact rfl,
end

instance [cartesian_closed C] : cartesian_closed (subq (⊤_ C)) :=
{ closed := λ f₁,
  { is_adj :=
    { right := subq.exp f₁,
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ f₂ f₃,
        begin
          change (_ ⨯ _ ⟶ _) ≃ (_ ⟶ _),
          rw prod_eq_inter,
          apply quotient.rec_on_subsingleton₂ f₁ f₂,
          intros f₁ f₂,
          apply quotient.rec_on_subsingleton f₃,
          intro f₃,
          refine ⟨_, _, _, _⟩,
          { rintro k,
            refine ⟨⟨_⟩⟩,
            rcases k with ⟨⟨⟨k⟩⟩⟩,
            refine ⟨sub.exp_equiv _ _ _ k⟩ },
          { rintro k,
            refine ⟨⟨_⟩⟩,
            rcases k with ⟨⟨⟨k⟩⟩⟩,
            refine ⟨(sub.exp_equiv _ _ _).symm k⟩ },
          { tidy },
          { tidy },
          { tidy },
          { tidy }
        end } } } }

-- def exponentiate' (B : C) [exponentiable B] (A : sub'.{v} (⊤_ C)) : sub'.{v} (⊤_ C) :=
-- { arrow := over.mk (default (B ⟹ A.1.left ⟶ ⊤_ C)),
--   is_mono :=
--   ⟨begin
--     intros Z f g eq,
--     apply uncurry_injective,
--     haveI := A.is_mono,
--     rw ← cancel_mono (A.1.hom),
--     change (_ : B ⨯ Z ⟶ ⊤_ C) = _,
--     apply subsingleton.elim,
--   end⟩ }

-- @[mono] def exponentiate'_le (B : C) [exponentiable B] {A₁ A₂ : sub'.{v} (⊤_ C)} (h : A₁ ≤ A₂) : exponentiate' B A₁ ≤ exponentiate' B A₂ :=
-- begin
--   cases h,
--   refine ⟨(exp B).map h_w, _⟩,
--   change (_ : _ ⟶ ⊤_ C) = _,
--   apply subsingleton.elim,
-- end

-- def exponentiate₂' [cartesian_closed C] (B A : sub'.{v} (⊤_ C)) : sub' (⊤_ C) :=
-- exponentiate' B.1.left A

-- lemma universal [cartesian_closed C] {A₁ A₂ A₃ : sub'.{v} (⊤_ C)} : intersection' A₁ A₂ ≤ A₃ ↔ A₂ ≤ exponentiate₂' A₁ A₃ :=
-- begin
--   refine ⟨λ k, _, λ k, _⟩,
--   { cases k,
--     dsimp [intersection'] at k_w k_h,
--     refine ⟨cartesian_closed.curry (pullback.lift limits.prod.fst limits.prod.snd _ ≫ k_w), _⟩,
--     change (_ : _ ⟶ ⊤_ C) = _,
--     apply subsingleton.elim,
--     change (_ : _ ⟶ ⊤_ C) = _,
--     apply subsingleton.elim },
--   { cases k,
--     refine ⟨prod.lift pullback.fst pullback.snd ≫ cartesian_closed.uncurry k_w, _⟩,
--     change (_ : _ ⟶ ⊤_ C) = _,
--     apply subsingleton.elim }
-- end

-- @[mono] def exponentiate₂'_ge [cartesian_closed C] {B₁ B₂ A : sub'.{v} (⊤_ C)} (h : B₁ ≤ B₂) :
--   exponentiate₂' B₂ A ≤ exponentiate₂' B₁ A :=
-- begin
--   cases h,
--   refine ⟨pre _ h_w, _⟩,
--   change (_ : _ ⟶ ⊤_ C) = _,
--   apply subsingleton.elim,
-- end

-- def exponential [cartesian_closed C] : sub (⊤_ C) → sub (⊤_ C) → sub (⊤_ C) :=
-- begin
--   refine quotient.map₂ exponentiate₂' _,
--   rintros a₁ a₂ ⟨a₁₂, a₂₁⟩ b₁ b₂ ⟨b₁₂, b₂₁⟩,
--   split;
--   refine (le_trans (exponentiate'_le _ ‹_›) (exponentiate₂'_ge ‹_›)),
-- end

-- def exp_e [cartesian_closed C] (B X Y : sub (⊤_ C)) : ((prod_functor.obj B).obj X ⟶ Y) ≃ (X ⟶ exponential B Y) :=
-- { to_fun := λ k,
--   ⟨⟨begin
--     rcases k with ⟨⟨_⟩⟩,
--     revert k,
--     dsimp [prod_functor],
--     rw [prod_eq_inter],
--     apply quotient.induction_on₃ B X Y,
--     introv,
--     apply universal.1,
--   end⟩⟩,
--   inv_fun := λ k,
--   ⟨⟨begin
--       rcases k with ⟨⟨_⟩⟩,
--       dsimp [prod_functor],
--       rw [prod_eq_inter],
--       revert k,
--       apply quotient.induction_on₃ B X Y,
--       introv,
--       apply universal.2,
--   end⟩⟩,
--   left_inv := λ f, by ext,
--   right_inv := λ f, by ext }

-- def exp_e_nat [cartesian_closed C] (B : sub (⊤_ C)) (X' X Y : sub (⊤_ C)) (f : X' ⟶ X) (g : (prod_functor.obj B).obj X ⟶ Y) :
--     (exp_e B X' Y).to_fun ((prod_functor.obj B).map f ≫ g) = f ≫ (exp_e B X Y).to_fun g :=
-- by ext

-- def exponentiable_sub [cartesian_closed C] (B : sub (⊤_ C)) : exponentiable B :=
-- { is_adj :=
--   { right := adjunction.right_adjoint_of_equiv (exp_e B) (λ _ _ _ _ _, subsingleton.elim _ _),
--     adj := adjunction.adjunction_of_equiv_right _ _ } }

-- variable (C)
-- instance cart_closed_one [cartesian_closed C] : cartesian_closed (sub (⊤_ C)) :=
-- { closed := exponentiable_sub }

end category_theory
