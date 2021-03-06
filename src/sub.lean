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
import category_theory.skeletal
import over

universes v v₂ u u₂

noncomputable theory
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
@[derive [category, λ t, has_coe t (over X)]]
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

def sub.iso_mk {f g : sub X} (h : f.val.left ≅ g.val.left) (w : h.hom ≫ g.arrow = f.arrow) : f ≅ g :=
{ hom := sub.hom_mk h.hom w,
  inv := sub.hom_mk h.inv (by rw [h.inv_comp_eq, w]) }

@[derive [partial_order, category]]
def subq (X : C) := thin_skeleton (sub X)

@[simps]
def sub.mk' {X A : C} (f : A ⟶ X) [hf : mono f] : sub X := { val := over.mk f, property := hf }
@[simp] lemma sub_mk'_arrow {X A : C} (f : A ⟶ X) [hf : mono f] : (sub.mk' f).arrow = f := rfl

abbreviation subq.mk {X A : C} (f : A ⟶ X) [mono f] : subq X := (to_thin_skeleton _).obj (sub.mk' f)

@[simps]
def restrict_to_sub {Y : D} (F : over Y ⥤ over X)
  (h : ∀ (f : sub Y), mono (F.obj ((forget_sub Y).obj f)).hom) : sub Y ⥤ sub X :=
{ obj := λ f, ⟨_, h f⟩,
  map := λ _ _ k, (forget_sub X).preimage ((forget_sub Y ⋙ F).map k), }

def restrict_to_sub_iso {Y : D} {F₁ F₂ : over Y ⥤ over X} (h₁ h₂) (i : F₁ ≅ F₂) :
  restrict_to_sub F₁ h₁ ≅ restrict_to_sub F₂ h₂ :=
fully_faithful_cancel_right (forget_sub X) (iso_whisker_left (forget_sub Y) i)

def restrict_to_sub_comp {X Z : C} {Y : D} (F : over X ⥤ over Y) (G : over Y ⥤ over Z) (h₁ h₂) :
  restrict_to_sub F h₁ ⋙ restrict_to_sub G h₂ ≅ restrict_to_sub (F ⋙ G) (λ f, h₂ ⟨_, h₁ f⟩) :=
fully_faithful_cancel_right (forget_sub _) (iso.refl _)

def restrict_to_sub_id :
  restrict_to_sub (𝟭 (over X)) (λ f, f.2) ≅ 𝟭 _ :=
fully_faithful_cancel_right (forget_sub _) (iso.refl _)

@[simp]
lemma restrict_comm (F : over Y ⥤ over X)
  (h : ∀ (f : sub Y), mono (F.obj ((forget_sub Y).obj f)).hom) :
  restrict_to_sub F h ⋙ forget_sub X = forget_sub Y ⋙ F :=
rfl

def lower_sub {Y : D} (F : sub Y ⥤ sub X) : subq Y ⥤ subq X := thin_skeleton.map F

lemma lower_sub_iso (F₁ F₂ : sub X ⥤ sub Y) (h : F₁ ≅ F₂) : lower_sub F₁ = lower_sub F₂ :=
thin_skeleton.map_iso_eq h

def lower_sub₂ (F : sub X ⥤ sub Y ⥤ sub Z) : subq X ⥤ subq Y ⥤ subq Z :=
thin_skeleton.map₂ F

@[simp]
lemma lower_comm (F : sub Y ⥤ sub X) :
  to_thin_skeleton _ ⋙ lower_sub F = F ⋙ to_thin_skeleton _ :=
rfl

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

@[simp] lemma sub.pullback_obj_left [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub Y) :
(↑((sub.pullback f).obj g) : over X).left = pullback g.arrow f :=
rfl

@[simp] lemma sub.pullback_obj_arrow [has_pullbacks.{v} C] (f : X ⟶ Y) (g : sub Y) :
((sub.pullback f).obj g).arrow = pullback.snd :=
rfl

def subq.pullback [has_pullbacks.{v} C] (f : X ⟶ Y) : subq Y ⥤ subq X :=
lower_sub (sub.pullback f)

lemma subq.pullback_id [has_pullbacks.{v} C] (x : subq X) : (subq.pullback (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨sub.pullback_id.app f⟩,
end
lemma subq.pullback_comp [has_pullbacks.{v} C] (f : X ⟶ Y) (g : Y ⟶ Z) (x : subq Z) :
  (subq.pullback (f ≫ g)).obj x = (subq.pullback f).obj ((subq.pullback g).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(sub.pullback_comp _ _).app t⟩,
end

attribute [instance] mono_comp

def sub.post (f : X ⟶ Y) [mono f] : sub X ⥤ sub Y :=
restrict_to_sub (over.map f)
(λ g, by apply mono_comp g.arrow f)

def sub.post_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  sub.post (f ≫ g) ≅ sub.post f ⋙ sub.post g :=
restrict_to_sub_iso _ _ (over_map_comp _ _) ≪≫ (restrict_to_sub_comp _ _ _ _).symm

def sub.post_id : sub.post (𝟙 X) ≅ 𝟭 _ :=
restrict_to_sub_iso _ _ over_map_id ≪≫ restrict_to_sub_id

@[simp] lemma sub.post_obj_left (f : X ⟶ Y) [mono f] (g : sub X) :
(↑((sub.post f).obj g) : over Y).left = g.val.left :=
rfl

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

lemma subq.post_id (x : subq X) : (subq.post (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨sub.post_id.app f⟩,
end
lemma subq.post_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (x : subq X) :
  (subq.post (f ≫ g)).obj x = (subq.post g).obj ((subq.post f).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(sub.post_comp _ _).app t⟩,
end

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

def subq.exists [has_images C] (f : X ⟶ Y) : subq X ⥤ subq Y :=
lower_sub (sub.exists f)

instance sub.faithful_pullback (f : X ⟶ Y) [has_pullbacks C] : faithful (sub.pullback f) := {}.

instance sub.faithful_exists (f : X ⟶ Y) [has_images C] : faithful (sub.exists f) := {}.

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
def sub.pull_post_adj (f : X ⟶ Y) [mono f] [has_pullbacks C] : sub.post f ⊣ sub.pullback f :=
adjunction.restrict_fully_faithful (forget_sub X) (forget_sub Y) (radj f) (iso.refl _) (iso.refl _)

def thin_skeleton.lower_adjunction
  [∀ (X Y : C), subsingleton (X ⟶ Y)] [∀ (X Y : D), subsingleton (X ⟶ Y)]
  (R : D ⥤ C) (L : C ⥤ D) (h : L ⊣ R) :
  thin_skeleton.map L ⊣ thin_skeleton.map R :=
adjunction.mk_of_unit_counit
{ unit :=
  { app := λ X,
    begin
      letI := is_isomorphic_setoid C,
      refine quotient.rec_on_subsingleton X (λ x, hom_of_le ⟨h.unit.app x⟩),
      -- TODO: make quotient.rec_on_subsingleton' so the letI isn't needed
    end },
  counit :=
  { app := λ X,
    begin
      letI := is_isomorphic_setoid D,
      refine quotient.rec_on_subsingleton X (λ x, hom_of_le ⟨h.counit.app x⟩),
    end } }

def subq.lower_adjunction {A : C} {B : D} {R : sub B ⥤ sub A} {L : sub A ⥤ sub B} (h : L ⊣ R) :
  lower_sub L ⊣ lower_sub R :=
thin_skeleton.lower_adjunction _ _ h

def subq.pull_post_adj (f : X ⟶ Y) [mono f] [has_pullbacks C] : subq.post f ⊣ subq.pullback f :=
subq.lower_adjunction (sub.pull_post_adj f)

/-- image is adjoint to pullback if images exist -/
-- I really think there should be a high-level proof of this but not sure what it is...
def sub.exists_pull_adj (f : X ⟶ Y) [has_images C] [has_pullbacks C] : sub.exists f ⊣ sub.pullback f :=
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

def subq.exists_pull_adj (f : X ⟶ Y) [has_pullbacks C] [has_images C] : subq.exists f ⊣ subq.pullback f :=
subq.lower_adjunction (sub.exists_pull_adj f)

-- Is this actually necessary?
def factors_through {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop := nonempty (over.mk f ⟶ over.mk g)
lemma factors_through_iff_le {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [mono f] [mono g] :
  factors_through f g ↔ subq.mk f ≤ subq.mk g :=
iff.rfl

instance {X : C} : has_top (sub X) :=
{ top := sub.mk' (𝟙 _) }

def to_top (f : sub X) : f ⟶ ⊤ :=
sub.hom_mk f.arrow (comp_id _)

instance subq.order_top {X : C} : order_top (subq X) :=
{ top := quotient.mk' ⊤,
  le_top :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨to_top f⟩,
  end,
  ..category_theory.subq.partial_order X}

@[simp] lemma top_left (X : C) : (⊤ : sub X).val.left = X := rfl
@[simp] lemma top_arrow (X : C) : (⊤ : sub X).arrow = 𝟙 X := rfl

def sub.post_top (f : X ⟶ Y) [mono f] : (sub.post f).obj ⊤ ≅ sub.mk' f :=
iso_of_both_ways (sub.hom_mk (𝟙 _) rfl) (sub.hom_mk (𝟙 _) (by simp [id_comp f]))

def subq.post_top (f : X ⟶ Y) [mono f] : (subq.post f).obj ⊤ = quotient.mk' (sub.mk' f) :=
quotient.sound' ⟨sub.post_top f⟩

def sub.pullback_top (f : X ⟶ Y) [has_pullbacks C] : (sub.pullback f).obj ⊤ ≅ ⊤ :=
iso_of_both_ways (to_top _) (sub.hom_mk (pullback.lift f (𝟙 _) (by tidy)) (pullback.lift_snd _ _ _))

def subq.pullback_top (f : X ⟶ Y) [has_pullbacks C] : (subq.pullback f).obj ⊤ = ⊤ :=
quotient.sound' ⟨sub.pullback_top f⟩

variable (C)

@[simps]
def subq.functor [has_pullbacks.{v} C] : Cᵒᵖ ⥤ Type (max u v) :=
{ obj := λ X, subq X.unop,
  map := λ X Y f, (subq.pullback f.unop).obj,
  map_id' := λ X, funext subq.pullback_id,
  map_comp' := λ X Y Z f g, funext (subq.pullback_comp _ _) }

variable {C}

@[simps]
def postcompose_sub_equiv_of_iso (e : X ≅ Y) : subq X ≃ subq Y :=
{ to_fun := (subq.post e.hom).obj,
  inv_fun := (subq.post e.inv).obj,
  left_inv := λ g, by simp_rw [← subq.post_comp, e.hom_inv_id, subq.post_id],
  right_inv := λ g, by simp_rw [← subq.post_comp, e.inv_hom_id, subq.post_id] }

-- lemma postcompose_pullback_comm' [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
--   {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk f g comm)) (a) :
--   (sub.post g).obj ((sub.pullback f).obj a) ≈ (sub.pullback k).obj ((sub.post h).obj a) :=
-- begin
--   apply equiv_of_both_ways,
--   { refine sub.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
--     change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
--     rw [assoc, ← comm, pullback.condition_assoc] },
--   { refine sub.hom_mk (pullback.lift pullback.fst
--                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
--                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
--     { rw [← pullback.condition, assoc], refl },
--     { erw [pullback.lift_snd_assoc], apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
-- end

lemma postcompose_pullback_comm [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) :
  ∀ p, (subq.post g).obj ((subq.pullback f).obj p) = (subq.pullback k).obj ((subq.post h).obj p) :=
begin
  apply quotient.ind',
  intro a,
  apply quotient.sound,
  apply thin_skeleton.equiv_of_both_ways,
  { refine sub.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
    rw [assoc, ← comm, pullback.condition_assoc] },
  { refine sub.hom_mk (pullback.lift pullback.fst
                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
    { rw [← pullback.condition, assoc], refl },
    { dsimp, rw [pullback.lift_snd_assoc],
      apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
end

lemma sub.pull_post_self [has_pullbacks.{v} C] (f : X ⟶ Y) [mono f] (g₁ : sub X) :
  sub.post f ⋙ sub.pullback f ≅ 𝟭 _ :=
(as_iso (sub.pull_post_adj f).unit).symm

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
def preorder_equivalence {α β : Type*} [preorder α] [preorder β] (f : α ≃o β) : α ≌ β :=
{ functor := preorder_functor f (λ x y h, by rwa [← rel_iso.map_rel_iff f]),
  inverse := preorder_functor f.symm (λ x y h, by rwa [← rel_iso.map_rel_iff f.symm]),
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

@[simps]
def subq.equiv {A : C} {B : D} (e : sub A ≌ sub B) : subq A ≌ subq B :=
{ functor := lower_sub e.functor,
  inverse := lower_sub e.inverse,
  unit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.unit_iso,
    { exact thin_skeleton.map_id_eq.symm },
    { exact (thin_skeleton.map_comp_eq _ _).symm },
  end,
  counit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.counit_iso,
    { exact (thin_skeleton.map_comp_eq _ _).symm },
    { exact thin_skeleton.map_id_eq.symm },
  end }

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
thin_skeleton.map₂ sub.intersection

lemma subq.inf_le_left [has_pullbacks.{v} C] {A : C} (f g : subq A) :
  (subq.intersection.obj f).obj g ≤ f :=
quotient.induction_on₂' f g (λ a b, ⟨sub.inter_le_left _ _⟩)

lemma subq.inf_le_right [has_pullbacks.{v} C] {A : C} (f g : subq A) :
  (subq.intersection.obj f).obj g ≤ g :=
quotient.induction_on₂' f g (λ a b, ⟨sub.inter_le_right _ _⟩)

lemma subq.le_inf [has_pullbacks.{v} C] {A : C} (h f g : subq A) :
  h ≤ f → h ≤ g → h ≤ (subq.intersection.obj f).obj g :=
quotient.induction_on₃' h f g
begin
  rintros f g h ⟨k⟩ ⟨l⟩,
  exact ⟨sub.le_inter _ _ _ k l⟩,
end

@[simps]
def over.coprod' [has_finite_coproducts.{v} C] {A : C} : over A → over A ⥤ over A := λ f,
{ obj := λ g, over.mk (coprod.desc f.hom g.hom),
  map := λ g₁ g₂ k, over.hom_mk (coprod.map (𝟙 _) k.left) }

@[simps]
def over.coprod [has_finite_coproducts.{v} C] {A : C} : over A ⥤ over A ⥤ over A :=
{ obj := λ f, over.coprod' f,
  map := λ f₁ f₂ k,
  { app := λ g, over.hom_mk (coprod.map k.left (𝟙 _)) (by { dsimp, rw [coprod.map_desc, id_comp, over.w k] }),
    naturality' := λ f g k, -- tidy can do this but it takes ages
    begin
      ext1,
      dsimp,
      simp,
    end },
  map_id' := λ X,
  begin
    ext; dsimp; simp,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext; dsimp; simp
  end }.

def sub.union [has_images.{v} C] [has_finite_coproducts.{v} C] {A : C} : sub A ⥤ sub A ⥤ sub A :=
curry_obj ((forget_sub A).prod (forget_sub A) ⋙ uncurry.obj over.coprod ⋙ sub.image)

def sub.le_union_left [has_images.{v} C] [has_finite_coproducts.{v} C] {A : C} (f g : sub A) :
  f ⟶ (sub.union.obj f).obj g :=
begin
  refine sub.hom_mk (coprod.inl ≫ factor_thru_image _) _,
  erw [assoc, image.fac, coprod.inl_desc],
  refl,
end

def sub.le_union_right [has_images.{v} C] [has_finite_coproducts.{v} C] {A : C} (f g : sub A) :
  g ⟶ (sub.union.obj f).obj g :=
begin
  refine sub.hom_mk (coprod.inr ≫ factor_thru_image _) _,
  erw [assoc, image.fac, coprod.inr_desc],
  refl,
end

def sub.union_le [has_images.{v} C] [has_finite_coproducts.{v} C] {A : C} (f g h : sub A) :
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

def subq.union [has_images.{v} C] [has_finite_coproducts.{v} C] {A : C} : subq A ⥤ subq A ⥤ subq A :=
thin_skeleton.map₂ sub.union

lemma sub.intersection_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ f₂ : sub A) :
  (sub.intersection.obj f₁).obj f₂ = (sub.post f₁.arrow).obj ((sub.pullback f₁.arrow).obj f₂) :=
rfl
lemma subq.intersection_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ : sub A) (f₂ : subq A) :
  (subq.intersection.obj (quotient.mk' f₁)).obj f₂ = (subq.post f₁.arrow).obj ((subq.pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on' f₂,
  intro f₂,
  refl,
end

instance [has_pullbacks.{v} C] {B : C} : semilattice_inf_top (subq B) :=
{ inf := λ m n, (subq.intersection.obj m).obj n,
  inf_le_left := subq.inf_le_left,
  inf_le_right := subq.inf_le_right,
  le_inf := subq.le_inf,
  ..category_theory.subq.order_top }

lemma subq.inf_eq_post_pull [has_pullbacks.{v} C] {A : C} (f₁ : sub A) (f₂ : subq A) :
  (quotient.mk' f₁ ⊓ f₂ : subq A) = (subq.post f₁.arrow).obj ((subq.pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on' f₂,
  intro f₂,
  refl,
end

instance [has_finite_coproducts.{v} C] [has_images.{v} C] {B : C} : semilattice_sup (subq B) :=
{ sup := λ m n, (subq.union.obj m).obj n,
  le_sup_left := λ m n, quotient.induction_on₂' m n (λ a b, ⟨sub.le_union_left _ _⟩),
  le_sup_right := λ m n, quotient.induction_on₂' m n (λ a b, ⟨sub.le_union_right _ _⟩),
  sup_le := λ m n k, quotient.induction_on₃' m n k (λ a b c ⟨i⟩ ⟨j⟩, ⟨sub.union_le _ _ _ i j⟩),
  ..category_theory.subq.partial_order B }

lemma prod_eq_inter {A : C} [has_pullbacks.{v} C] {f₁ f₂ : subq A} : (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
le_antisymm
  (le_inf
    (le_of_hom limits.prod.fst)
    (le_of_hom limits.prod.snd))
  (le_of_hom
    (prod.lift
      (hom_of_le inf_le_left)
      (hom_of_le inf_le_right)))

lemma inf_eq_intersection {B : C} (m m' : subq B) [has_pullbacks.{v} C] :
  m ⊓ m' = (subq.intersection.obj m).obj m' := rfl

lemma top_eq_id {B : C} : (⊤ : subq B) = subq.mk (𝟙 B) := rfl

/-- Intersection plays well with pullback. -/
lemma inf_pullback [has_pullbacks.{v} C] {X Y : C} (g : X ⟶ Y) (f₂) :
  ∀ f₁, (subq.pullback g).obj (f₁ ⊓ f₂) = (subq.pullback g).obj f₁ ⊓ (subq.pullback g).obj f₂ :=
quotient.ind' begin
  intro f₁,
  erw [inf_eq_intersection, inf_eq_intersection, subq.intersection_eq_post_pull,
       subq.intersection_eq_post_pull, ← subq.pullback_comp,
       ← postcompose_pullback_comm pullback.condition (cone_is_pullback f₁.arrow g),
       ← subq.pullback_comp, pullback.condition],
  refl,
end

lemma inf_post [has_pullbacks.{v} C] {X Y : C} (g : Y ⟶ X) [mono g] (f₂) :
  ∀ f₁, (subq.post g).obj (f₁ ⊓ f₂) = (subq.post g).obj f₁ ⊓ (subq.post g).obj f₂ :=
quotient.ind' begin
  intro f₁,
  erw [inf_eq_intersection, inf_eq_intersection, subq.intersection_eq_post_pull,
       subq.intersection_eq_post_pull, ← subq.post_comp],
  dsimp,
  rw [subq.pullback_comp, subq.pull_post_self],
end


def sub.top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (⊤ : sub A) ⟶ (sub.pullback f).obj (sub.mk' f) :=
sub.hom_mk _ (pullback.lift_snd _ _ rfl)

def sub.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (sub.pullback f).obj (sub.mk' f) ≅ ⊤ :=
iso_of_both_ways (to_top _) (sub.top_le_pullback_self _)

lemma subq.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks.{v} C] :
  (subq.pullback f).obj (subq.mk f) = ⊤ :=
quotient.sound' ⟨sub.pullback_self f⟩

section
variable [has_binary_products.{v} C]

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
end

section
variable [has_finite_products.{v} C]
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
end

variable [has_finite_limits.{v} C]
local attribute [instance] has_finite_products_of_has_finite_limits

def sub.exp_equiv [cartesian_closed C] (f₁ f₂ f₃ : sub (⊤_ C)) :
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
  apply quotient.lift_on' f subq.exp_aux _,
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

variable (C)
def top_cc [cartesian_closed C] : cartesian_closed (subq (⊤_ C)) :=
{ closed := λ f₁,
  { is_adj :=
    { right := subq.exp f₁,
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ f₂ f₃,
        begin
          change (_ ⨯ _ ⟶ _) ≃ (_ ⟶ _),
          rw prod_eq_inter,
          apply @@quotient.rec_on_subsingleton₂ (is_isomorphic_setoid _) (is_isomorphic_setoid _) _ _ f₁ f₂,
          intros f₁ f₂,
          apply @@quotient.rec_on_subsingleton (is_isomorphic_setoid _) _ _ f₃,
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

end category_theory
