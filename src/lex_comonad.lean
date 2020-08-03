-- import preserve_binary_products
import category_theory.monad.algebra
import category_theory.limits.creates
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.equalizers
import category_theory.comma
import category_theory.limits.over
import category_theory.limits.shapes.constructions.equalizers
import over

namespace category_theory

open category limits comonad

universes v u v₂ u₂

variables {C : Type u} [category.{v} C] [has_finite_limits.{v} C]
variables (G : C ⥤ C) [comonad.{v} G]

@[simps]
def apply_functor (A : C) : over A ⥤ over (G.obj A) :=
{ obj := λ f, over.mk (G.map f.hom),
  map := λ f g k,
  begin
    apply over.hom_mk _ _,
    apply G.map k.left,
    dsimp,
    rw [← over.w k, G.map_comp],
  end }

variables {G} (a : coalgebra G)

local attribute [instance] has_pullbacks_of_has_finite_limits
local attribute [instance] has_finite_wide_pullbacks_of_has_finite_limits

def G' : over a.A ⥤ over a.A :=
apply_functor G a.A ⋙ real_pullback a.a

def G'_preserves_term (A : C) : preserves_limits_of_shape (discrete pempty) (apply_functor G A) :=
{ preserves_limit := λ K,
  begin
    apply preserves_limit_of_iso _ (functor.unique_from_empty K).symm,
    clear K,
    sorry
    -- apply preserves_limit_of_preserves_limit_cone (limit.is_limit (functor.empty (over A))),
    -- apply preserves_limit_of_preserves_limit_cone (limit.is_limit (functor.empty (over A))),
    -- refine ⟨λ s, _, _, _⟩,
    -- apply over.hom_mk _ _,
    -- apply s.X.hom,
    -- dsimp,
    -- erw G.map_id,
    -- rw comp_id,
    -- rintros s ⟨⟩,
    -- intros s m w,
    -- ext1,
    -- dsimp,
    -- rw ← over.w m,
    -- dsimp,
    -- symmetry,
    -- change m.left ≫ G.map (𝟙 _) = _,
    -- rw G.map_id,
    -- apply comp_id,
  end }

variable [preserves_limits_of_shape walking_cospan G]

@[simps]
def counit : G' a ⟶ 𝟭 _ :=
{ app := λ f,
  begin
    apply over.hom_mk _ _,
    apply pullback.fst ≫ (ε_ G).app _,
    dsimp,
    erw [assoc, ← (ε_ G).naturality f.hom],
    dsimp,
    rw pullback.condition_assoc,
    rw comonad.coalgebra.counit,
    rw comp_id,
    refl,
  end,
  naturality' := λ f g k,
  begin
    ext1,
    dsimp [G'],
    rw [pullback.lift_fst_assoc, assoc, (ε_ G).naturality, assoc],
    refl,
  end }.

lemma comult_pb_comm (f : over a.A) :
  (pullback.fst ≫ G.map pullback.fst) ≫ G.map (G.map f.hom) = ((G' a).obj ((G' a).obj f)).hom ≫ a.a ≫ (δ_ G).app _ :=
begin
  erw [coalgebra.coassoc, assoc, ← G.map_comp, pullback.condition, G.map_comp, ← pullback.condition_assoc], refl,
end

def comult_pb (f : over a.A) :
  is_limit (pullback_cone.mk (pullback.fst ≫ G.map pullback.fst) _ (comult_pb_comm a f)) :=
begin
  have big_comm : (pullback.fst ≫ G.map pullback.fst) ≫ G.map (G.map f.hom) = ((G' a).obj ((G' a).obj f)).hom ≫ a.a ≫ G.map a.a,
    rw [comult_pb_comm, coalgebra.coassoc],
  have : is_limit (pullback_cone.mk _ _ big_comm),
    apply left_pb_to_both_pb _ _ _ _ _ _ _ pullback.condition _ (cone_is_pullback _ _) (preserves_pullback_cone G _ _ _ _ _ (cone_is_pullback _ _)),
  convert this using 2;
  rw coalgebra.coassoc,
end

def comult_hom (f : over a.A) : pullback (G.map f.hom) a.a ⟶ pullback (G.map ((G' a).obj f).hom) a.a :=
begin
  let fl := comult_pb a f,
  apply (limits.pullback_cone.is_limit.lift' fl (pullback.fst ≫ (δ_ G).app _) ((G' a).obj f).hom _).1,
  erw [assoc, ←(δ_ G).naturality, pullback.condition_assoc], refl,
end

@[reassoc]
lemma comult_hom₁ (f : over a.A) : comult_hom _ f ≫ pullback.fst ≫ G.map pullback.fst = pullback.fst ≫ (δ_ G).app f.left :=
(limits.pullback_cone.is_limit.lift' _ (pullback.fst ≫ (δ_ G).app _) ((G' a).obj f).hom _).2.1

@[reassoc]
lemma comult_hom₂ (f : over a.A) : comult_hom _ f ≫ ((G' a).obj ((G' a).obj f)).hom = ((G' a).obj f).hom :=
(limits.pullback_cone.is_limit.lift' _ (pullback.fst ≫ (δ_ G).app _) ((G' a).obj f).hom _).2.2

@[simps]
def comult : G' a ⟶ G' a ⋙ G' a :=
{ app := λ f,
  begin
    apply over.hom_mk _ _,
    apply comult_hom _ f,
    apply comult_hom₂,
  end,
  naturality' := λ f g k,
  begin
    ext1,
    let gl := comult_pb a g,
    change ((G' a).map k).left ≫ comult_hom _ _ = comult_hom _ _ ≫ ((G' a).map ((G' a).map k)).left,
    apply pullback_cone.is_limit.hom_ext gl,
    change (((G' a).map k).left ≫ comult_hom _ _) ≫ pullback.fst ≫ G.map pullback.fst = (comult_hom _ _ ≫ ((G' a).map ((G' a).map k)).left) ≫ pullback.fst ≫ G.map pullback.fst,
    simp_rw [assoc],
    rw comult_hom₁ _ g,
    dsimp [G'],
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, assoc, assoc, ← G.map_comp, pullback.lift_fst, G.map_comp, comult_hom₁_assoc, (δ_ G).naturality],
    refl,
    change (((G' a).map k).left ≫ comult_hom a g) ≫ ((G' a).obj ((G' a).obj g)).hom = (comult_hom a f ≫ ((G' a).map ((G' a).map k)).left) ≫ ((G' a).obj ((G' a).obj g)).hom,
    rw [assoc, comult_hom₂],
    dsimp [G'],
    rw [assoc, pullback.lift_snd, pullback.lift_snd],
    erw comult_hom₂, refl,
  end }

instance sliced_comonad : comonad (G' a) :=
{ ε := counit a,
  δ := comult a,
  left_counit' := λ f,
  begin
    ext1,
    apply pullback.hom_ext,
    { erw [id_comp, assoc, assoc, ←(ε_ G).naturality, comult_hom₁_assoc, comonad.left_counit, comp_id] },
    { erw [id_comp, assoc, assoc, ←(ε_ G).naturality, pullback.condition_assoc, comult_hom₂_assoc, coalgebra.counit, comp_id],
      refl }
  end,
  right_counit' := λ f,
  begin
    ext1,
    apply pullback.hom_ext,
    { erw [id_comp, assoc, pullback.lift_fst],
      dsimp,
      erw [G.map_comp, comult_hom₁_assoc, comonad.right_counit, comp_id] },
    { erw [id_comp, assoc, pullback.lift_snd, comult_hom₂], refl },
  end,
  coassoc' := λ f,
  begin
    -- ext1,
    -- dsimp,
    -- dsimp [G'],
    -- let Gfl := comult_pb _ ((G' a).obj f),
    -- let fl := comult_pb _ f,
    -- apply pullback_cone.is_limit.hom_ext Gfl,
    -- change _ ≫ pullback.fst ≫ _ = _ ≫ pullback.fst ≫ _,
    -- rw [assoc, pullback.lift_fst_assoc, assoc, assoc, comult_hom₁],
    -- dsimp,
    sorry
  end
   }.


def bijection (f : over a.A) : (f ⟶ (G' a).obj f) ≃ {β : f.left ⟶ G.obj f.left // β ≫ G.map f.hom = f.hom ≫ a.a} :=
{ to_fun := λ k,
  begin
    refine ⟨k.left ≫ pullback.fst, _⟩,
    erw [assoc, pullback.condition, over.w_assoc k],
  end,
  inv_fun := λ k, over.hom_mk (pullback.lift k.1 f.hom k.2) (pullback.lift_snd _ _ _),
  left_inv :=
  begin
    intro k,
    ext1,
    apply pullback.hom_ext,
    apply pullback.lift_fst,
    dsimp,
    rw [pullback.lift_snd],
    apply (over.w k).symm,
  end,
  right_inv :=
  begin
    intro k,
    apply subtype.ext_val,
    apply pullback.lift_fst
  end }

def restricted_bijection (f : over a.A) :
  {F : f ⟶ (G' a).obj f // F ≫ (ε_ (G' a)).app f = 𝟙 _ ∧ F ≫ (G' a).map F = F ≫ (δ _).app _} ≃
  {β : f.left ⟶ G.obj f.left // β ≫ G.map f.hom = f.hom ≫ a.a ∧ β ≫ (ε_ G).app _ = 𝟙 _ ∧ β ≫ G.map β = β ≫ (δ _).app _} :=
begin
  apply equiv.trans _ (equiv.subtype_subtype_equiv_subtype_inter _ _),
  apply equiv.subtype_congr (bijection a f),
  intro k,
  dsimp [bijection],
  rw [assoc, G.map_comp, assoc],
  split,
  { rintro ⟨k₁, k₂⟩,
    split,
    { exact congr_arg comma_morphism.left k₁ },
    { have := congr_arg comma_morphism.left k₂,
      dsimp [G', comonad.δ] at this,
      have := this =≫ (pullback.fst ≫ G.map pullback.fst),
      simp only [pullback.lift_fst_assoc, assoc, comult_hom₁] at this,
      simpa } },
  { rintro ⟨k₁, k₂⟩,
    split,
    ext1, exact k₁,
    ext1,
    dsimp [G', comonad.δ],
    let fl := comult_pb a f,
    apply pullback_cone.is_limit.hom_ext fl,
    rw [assoc, assoc],
    change k.left ≫ pullback.lift _ _ _ ≫ _ ≫ _ = _ ≫ _ ≫ _ ≫ _,
    rw [pullback.lift_fst_assoc, comult_hom₁, assoc, k₂, assoc],
    change (k.left ≫ pullback.lift (pullback.fst ≫ G.map k.left) pullback.snd _) ≫
      ((G' a).obj ((G' a).obj f)).hom =
    (k.left ≫ comult_hom a f) ≫ ((G' a).obj ((G' a).obj f)).hom,
    erw [assoc, pullback.lift_snd, assoc, comult_hom₂], refl },
end

def mk_coalgebra_iso {D : Type u} [category.{v} D] {W : D ⥤ D} [comonad.{v} W] {x y : coalgebra W}
  (h : x.A ≅ y.A) (k : x.a ≫ W.map h.hom = h.hom ≫ y.a) : x ≅ y :=
begin
  apply as_iso _,
  refine ⟨h.1, k⟩,
  refine ⟨⟨h.2, _⟩, _, _⟩,
  dsimp,
  rw [h.eq_inv_comp, ← reassoc_of k, ← W.map_comp, h.hom_inv_id, W.map_id, comp_id],
  apply_auto_param,
end

def coalgebra_to_over : coalgebra (G' a) ⥤ over a :=
{ obj := λ f,
  begin
    apply over.mk _,
    refine ⟨_, (restricted_bijection a _ ⟨f.a, f.counit, f.coassoc.symm⟩).1, (restricted_bijection a _ ⟨f.a, f.counit, f.coassoc.symm⟩).2.2.1, (restricted_bijection a _ ⟨f.a, f.counit, f.coassoc.symm⟩).2.2.2.symm⟩,
    refine ⟨_, (restricted_bijection a _ ⟨f.a, f.counit, f.coassoc.symm⟩).2.1⟩,
  end,
  map := λ f g k,
  begin
    apply over.hom_mk _ _,
    refine ⟨k.f.left, _⟩,
    change (f.a.left ≫ pullback.fst) ≫ G.map k.f.left = k.f.left ≫ g.a.left ≫ pullback.fst,
    rw ← assoc,
    change (f.a.left ≫ pullback.fst) ≫ G.map k.f.left = (k.f ≫ g.a).left ≫ pullback.fst,
    rw [← k.h, assoc],
    dsimp [G'],
    rw [assoc, pullback.lift_fst],
    ext1,
    apply over.w k.f,
  end }.

def over_to_coalgebra : over a ⥤ coalgebra (G' a) :=
{ obj := λ f,
  begin
    let t := (restricted_bijection a (over.mk f.hom.f)).symm ⟨f.left.a, f.hom.h, coalgebra.counit f.left, (coalgebra.coassoc f.left).symm⟩,
    refine ⟨_, t.1, t.2.1, t.2.2.symm⟩,
  end,
  map := λ f g k,
  begin
    refine ⟨over.hom_mk k.left.f _, _⟩,
    rw ← over.w k,
    dsimp,
    refl,
    ext1,
    dsimp [restricted_bijection, equiv.subtype_subtype_equiv_subtype_inter,
           bijection, equiv.subtype_congr, equiv.subtype_subtype_equiv_subtype_exists,
           equiv.subtype_congr_right, G'],
    apply pullback.hom_ext,
    simp,
    simp only [pullback.lift_snd, assoc],
    rw ← over.w k,
    refl,
  end }.

def isomorphic : coalgebra (G' a) ≌ over a :=
{ functor := coalgebra_to_over a,
  inverse := over_to_coalgebra a,
  unit_iso :=
  begin
    apply nat_iso.of_components _ _,
    intro f,
    apply mk_coalgebra_iso _ _,
    apply over_iso _ _,
    apply iso.refl _,
    apply id_comp,
    ext1,
    change (f.a.left ≫ pullback.lift (pullback.fst ≫ G.map (𝟙 f.A.left)) pullback.snd _) = 𝟙 f.A.left ≫ pullback.lift (f.a.left ≫ pullback.fst) f.A.hom _,
    rw [id_comp],
    apply pullback.hom_ext,
    erw [assoc, pullback.lift_fst, pullback.lift_fst, G.map_id, comp_id],
    simp only [pullback.lift_snd, assoc], exact over.w f.a,
    intros f g k,
    ext,
    dsimp [mk_coalgebra_iso],
    rw [id_comp, comp_id],
    refl,
  end,
  counit_iso :=
  begin
    apply nat_iso.of_components _ _,
    intro f,
    apply over_iso _ _,
    apply mk_coalgebra_iso _ _,
    apply iso.refl _,
    change (pullback.lift f.left.a f.hom.f _ ≫ pullback.fst) ≫ G.map (𝟙 f.left.A) = 𝟙 f.left.A ≫ f.left.a,
    rw [pullback.lift_fst, G.map_id, comp_id, id_comp],
    ext1,
    apply id_comp,
    intros f g k,
    ext,
    change k.left.f ≫ 𝟙 g.left.A = 𝟙 f.left.A ≫ k.left.f,
    rw [id_comp, comp_id],
  end,
  functor_unit_iso_comp' := λ X,
  begin
    ext : 2,
    exact comp_id _,
  end }

instance terminal_coalgebra : has_terminal.{v} (coalgebra G) :=
begin
  apply has_terminal_of_unique _,
  apply ((cofree G).obj (⊤_ C)),
  intro X,
  apply ((comonad.adj G).hom_equiv X (⊤_ C)).symm.unique,
end

def main : coalgebra G ≌ coalgebra (G' (⊤_ (coalgebra G))) :=
((isomorphic _).trans over_terminal).symm

end category_theory