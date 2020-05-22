import category_theory.limits.limits
import category_theory.monad.algebra
import category_theory.monad
import category_theory.limits.shapes.equalizers
import creates
import beck2
import adjunction

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
namespace monad

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞
variables {T : C ⥤ C} [monad.{v₁} T]

open monad limits

lemma thing (A : algebra T) : (η_ T).app ((forget T).obj A) ≫ (forget T).map ((adj T).counit.app A) = 𝟙 ((forget T).obj A) :=
begin
  dunfold forget adj adjunction.mk_of_hom_equiv, dsimp, rw T.map_id, rw category.id_comp,
  exact A.unit,
end

include 𝒟
variables {S : D ⥤ D} [monad.{v₂} S]

namespace lift_left_adjoint

variables (R : D ⥤ C) [ℛ : is_right_adjoint R]
include ℛ
variable {R' : algebra S ⥤ algebra T}

abbreviation L : C ⥤ D := left_adjoint R

def transport (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (B : algebra S) :
  (forget T).obj (R'.obj B) ≅ R.obj ((forget S).obj B) :=
iso.app comm_iso B

namespace part1

def f1 (B : D) : R.obj B ⟶ R.obj (S.obj B) :=
R.map ((adj S).unit.app B)

def f2 (B : D) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  (free T).obj (R.obj B) ⟶ R'.obj ((free S).obj B) :=
((adj T).hom_equiv _ _).inv_fun (f1 R B ≫ (transport R comm_iso ((free S).obj B)).inv)

def θ (B : D) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  T.obj (R.obj B) ⟶ R.obj (S.obj B) :=
(forget T).map (f2 R B comm_iso) ≫ (transport R comm_iso ((free S).obj B)).hom


lemma η_θ (B : D) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  (η_ T).app (R.obj B) ≫ θ R B comm_iso = f1 R B :=
begin
  rw [θ, f2],
  have: ((adj T).hom_equiv (R.obj B) (R'.obj ((free S).obj B))).inv_fun (f1 R B ≫ (transport R comm_iso ((free S).obj B)).inv) = _ := (adj T).hom_equiv_counit,
  rw this, clear this,
  rw (forget T).map_comp,
  slice_lhs 1 2 {erw ← (η_ T).naturality},
  change (((f1 R B ≫ (transport R comm_iso ((free S).obj B)).inv) ≫
            (η_ T).app ((forget T).obj (R'.obj ((free S).obj B)))) ≫
         (forget T).map ((adj T).counit.app (R'.obj ((free S).obj B)))) ≫
      (transport R comm_iso ((free S).obj B)).hom =
    f1 R B,
  slice_lhs 3 4 {rw thing (R'.obj ((free S).obj B))},
  rw category.id_comp,
  rw (transport R comm_iso ((free S).obj B)).inv_hom_id,
  erw category.comp_id
end

end part1

namespace part2
abbreviation γ (A : C) : A ⟶ R.obj ((L R).obj A) := is_right_adjoint.adj.unit.app A
abbreviation δ (B : D) : (L R).obj (R.obj B) ⟶ B := is_right_adjoint.adj.counit.app B

def φ (A : C) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  (L R).obj (T.obj A) ⟶ (forget S).obj ((free S).obj ((L R).obj A)) :=
(L R).map (T.map (γ R A)) ≫ (L R).map (part1.θ R ((L R).obj A) comm_iso) ≫ (δ R) (S.obj ((L R).obj A))

def φ' (A : C) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  (free S).obj ((L R).obj (T.obj A)) ⟶ (free S).obj ((L R).obj A) :=
((adj S).hom_equiv _ _).inv_fun (φ R A comm_iso)

end part2
namespace part3

def refl_pair (a : algebra T) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) :
  reflexive_pair ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso) :=
{ back := (free S).map ((L R).map ((η_ T).app a.A)),
  back_f :=
  begin
    ext1,
    dsimp, rw ← S.map_comp,
    rw ← (L R).map_comp,
    rw a.unit,
    rw (L R).map_id,
    rw S.map_id,
  end,
  back_g :=
  begin
    dunfold part2.φ',
    erw ← adjunction.hom_equiv_naturality_left_symm (adj S) ((L R).map ((η_ T).app a.A)) (part2.φ R a.A comm_iso),
    apply ((adj S).hom_equiv _ _).left_inv.injective,
    erw ((adj S).hom_equiv _ _).right_inv,
    dunfold part2.φ,

    slice_lhs 1 2 {rw ← (L R).map_comp, rw ← (η_ T).naturality},
    have: ((adj S).hom_equiv _ _).to_fun (𝟙 ((free S).obj ((L R).obj a.A))) = _ := (adj S).hom_equiv_unit,
      rw (forget S).map_id at this, rw category.comp_id at this,
    erw this,
    change ((L R).map ((part2.γ R a.A) ≫ (η_ T).app (R.obj ((L R).obj a.A))) ≫
         (L R).map (part1.θ R ((L R).obj a.A) comm_iso)) ≫
      part2.δ R (S.obj ((L R).obj a.A)) = _,
    rw ← (L R).map_comp,
    rw category.assoc,
    rw part1.η_θ,
    change (L R).map (part2.γ R a.A ≫ part1.f1 R ((L R).obj a.A)) ≫ part2.δ R (S.obj ((L R).obj a.A)) = (adj S).unit.app ((L R).obj a.A),
    rw (L R).map_comp,
    rw category.assoc,
    rw part1.f1,
    erw is_right_adjoint.adj.counit.naturality ((adj S).unit.app ((L R).obj a.A)),
    change (L R).map (is_right_adjoint.adj.unit.app a.A) ≫
      (is_right_adjoint.adj).counit.app (((L R).obj a.A)) ≫
        ((adj S).unit.app ((L R).obj a.A)) = (adj S).unit.app ((L R).obj a.A),
    slice_lhs 1 2 {erw (is_right_adjoint.adj).left_triangle_components},
    erw category.id_comp
  end }
end part3

def L'obj (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) (a : algebra T) :
  algebra S :=
begin
  haveI : has_colimit (parallel_pair ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso)) := hrc (part3.refl_pair R a comm_iso),
  exact coequalizer ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso)
end

def e1 (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (a : algebra T) [has_colimit (parallel_pair ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso))] (b : algebra S) :
  (coequalizer ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso) ⟶ b) ≃ {h : (free S).obj ((L R).obj a.A) ⟶ b // (free S).map ((L R).map a.a) ≫ h = part2.φ' R a.A comm_iso ≫ h} :=
coeq_equiv b ((free S).map ((L R).map a.a)) (part2.φ' R a.A comm_iso)

def arrow_map (a : algebra T) (b : algebra S) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) : ((free S).obj ((L R).obj a.A) ⟶ b) ≃ (a.A ⟶ (forget T).obj (R'.obj b)) :=
equiv.trans ((adj S).hom_equiv ((L R).obj a.A) b) $ equiv.trans (ℛ.adj.hom_equiv a.A ((forget S).obj b)) $
{ to_fun := λ f, f ≫ comm_iso.inv.app b,
  inv_fun := λ g, g ≫ comm_iso.hom.app b,
  left_inv := λ f, begin dsimp, rw [category.assoc, nat_iso.inv_hom_id_app], apply category.comp_id end,
  right_inv := λ g, begin dsimp, rw [category.assoc, nat_iso.hom_inv_id_app], apply category.comp_id end
}
-- This final equivalence might be useful in other contexts (that is, A ⟶ B ≃ A ⟶ C when B ≅ C). It should also probably be a consequence of Yoneda

def test (b : algebra S) : (forget T).map ((adj T).counit.app (R'.obj b)) = (R'.obj b).a :=
begin
  dsimp [adj, adjunction.mk_of_hom_equiv],
  rw [T.map_id, category.id_comp],
end

def sound' (a : algebra T) (b : algebra S) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (h : a.A ⟶ (forget T).obj (R'.obj b)) :
  T.map h ≫ (R'.obj b).a = a.a ≫ h ↔
    (free S).map ((L R).map a.a) ≫ (equiv.symm (arrow_map R a b comm_iso)).to_fun h =
      part2.φ' R a.A comm_iso ≫ (equiv.symm (arrow_map R a b comm_iso)).to_fun h :=
begin
  symmetry,
  rw part2.φ',
  dunfold arrow_map,
  conv_lhs {to_lhs, apply_congr ((adj S).hom_equiv_naturality_left_symm _ _).symm},
  dsimp [equiv.symm],
  rw ← adjunction.eq_hom_equiv_apply,
  conv_lhs {to_rhs, apply_congr (adj S).hom_equiv_naturality_right _ _ },
  conv_lhs {to_rhs, congr, apply_congr ((adj S).hom_equiv _ _).right_inv },
  erw ← ℛ.adj.hom_equiv_naturality_left_symm,
  rw ← ℛ.adj.eq_hom_equiv_apply,
  rw ℛ.adj.hom_equiv_naturality_right,
  rw part2.φ,
  rw ← (L R).map_comp_assoc,
  erw ℛ.adj.hom_equiv_naturality_left,
  conv_lhs {to_rhs, congr, congr, skip, apply_congr ℛ.adj.hom_equiv_unit },
  rw [adjunction.right_triangle_components, category.comp_id, part1.θ, transport, iso.app, category.assoc, category.assoc],
  erw ← comm_iso.hom.naturality,
  rw [← category.assoc, ← category.assoc, ← category.assoc, cancel_mono (comm_iso.hom.app b), eq_comm],
  convert iff.refl _ using 2,
  rw ← test R b,
  rw functor.comp_map,
  change (forget T).map ((free T).map _) ≫ _ = ((forget T).map ((free T).map _) ≫ _) ≫ _,
  rw [← (forget T).map_comp, ← (forget T).map_comp, ← (forget T).map_comp],
  congr' 1,
  rw ℛ.adj.hom_equiv_naturality_left_symm,
  rw (adj S).hom_equiv_naturality_left_symm,
  rw R'.map_comp,
  rw category.assoc,
  rw part1.f2,
  rw part1.f1,
  rw transport,
  conv_rhs {congr, skip, congr, apply_congr (adj T).hom_equiv_counit},
  rw (free T).map_comp,
  slice_rhs 4 5 {erw ← (adj T).counit.naturality},
  slice_rhs 3 4 {rw functor.comp_map, rw ← (free T).map_comp },
  conv_rhs {congr, skip, congr, skip, congr, congr, congr, rw iso.app, erw ← comm_iso.inv.naturality, rw functor.comp_map },
  rw (free T).map_comp,
  slice_rhs 2 3 {},
  conv_rhs {congr, skip, congr, congr, congr, rw ← (free T).map_comp, congr, rw ← R.map_comp, congr, erw ← (adj S).unit.naturality, rw functor.id_map },
  slice_rhs 1 2 {rw R.map_comp, rw (free T).map_comp},
  slice_rhs 1 2 {rw ← (free T).map_comp, congr, erw ← ℛ.adj.unit.naturality },
  simp only [functor.id_map, category.assoc, (free T).map_comp],
  congr' 1,
  rw (adj S).hom_equiv_counit,
  rw ℛ.adj.hom_equiv_counit,
  simp only [category.assoc, R'.map_comp, (free S).map_comp],
  slice_rhs 4 5 {erw ← (adj T).counit.naturality},
  slice_rhs 3 4 {rw functor.comp_map, rw ← (free T).map_comp },
  simp only [category.assoc, functor.map_comp],
  slice_rhs 5 7 {rw ← R'.map_comp, erw ← (adj T).counit.naturality, rw functor.map_comp, rw functor.map_comp, rw functor.comp_map, rw functor.comp_map },
  slice_rhs 3 6 {rw [← (free T).map_comp, ← (free T).map_comp, ← (free T).map_comp], congr, erw [← (R' ⋙ forget T).map_comp, ← (R' ⋙ forget T).map_comp], rw ← comm_iso.inv.naturality },
  simp only [functor.map_comp, functor.comp_map, category.assoc],
  slice_rhs 2 4 {erw [← (R ⋙ free T).map_comp, ← (R ⋙ free T).map_comp], congr, erw [← S.map_comp], erw ← (adj S).unit.naturality, rw functor.id_map },
  simp only [functor.map_comp, functor.comp_map, category.assoc],
  slice_rhs 4 5 {erw [← (R ⋙ free T).map_comp], congr, rw (adj S).right_triangle_components },
  erw (R ⋙ free T).map_id,
  erw category.id_comp,
  slice_rhs 1 2 {rw ← (free T).map_comp, congr, erw ← ℛ.adj.unit.naturality, rw functor.id_map },
  simp only [functor.map_comp, functor.comp_map, category.assoc],
  slice_rhs 2 3 {rw ← (free T).map_comp, congr, rw ℛ.adj.right_triangle_components },
  slice_rhs 1 3 {rw [← (free T).map_comp, ← (free T).map_comp], congr, erw category.id_comp, rw nat_iso.hom_inv_id_app },
  erw (free T).map_id,
  rw category.id_comp,
end

omit ℛ
def elast (a : algebra T) (b : algebra S) : {g : a.A ⟶ (forget T).obj (R'.obj b) // T.map g ≫ (R'.obj b).a = a.a ≫ g} ≃ (a ⟶ R'.obj b) :=
{ to_fun := λ f, {f := f.1, h' := f.2},
  inv_fun := λ g, ⟨g.1, g.2⟩,
  left_inv := λ ⟨f, _⟩, rfl,
  right_inv := λ ⟨g, _⟩, rfl}
include ℛ

def L'e (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) (a : algebra T) (b : algebra S) :
  (L'obj R comm_iso hrc a ⟶ b) ≃ (a ⟶ R'.obj b) :=
begin
  apply equiv.trans (e1 _ _ _ _),
  apply equiv.trans _ (elast _ _),
  apply equiv.symm,
  exact equiv.subtype_congr (arrow_map R a b comm_iso).symm (sound' R a b comm_iso),
end

def L' (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) :
  algebra T ⥤ algebra S :=
begin
  refine adjunction.left_adjoint_of_equiv (λ a b, L'e R comm_iso hrc a b) _,
  intros a b b' g h,
  ext1,
  dsimp [L'e, elast, equiv.subtype_congr, arrow_map, e1, coeq_equiv, equiv.trans, equiv.symm],
  change (ℛ.adj.hom_equiv _ _).to_fun (((adj S).hom_equiv _ _).to_fun (_ ≫ h ≫ g)) ≫ comm_iso.inv.app b' =
        ((ℛ.adj.hom_equiv _ _).to_fun (((adj S).hom_equiv _ _).to_fun (_ ≫ h)) ≫ comm_iso.inv.app b) ≫ (R'.map g).f,
  conv_lhs {congr, congr, skip, conv {congr, skip, rw ← category.assoc}, apply_congr (adj S).hom_equiv_naturality_right},
  change (ℛ.adj.hom_equiv a.A ((forget S).obj b')).to_fun (((adj S).hom_equiv _ b).to_fun (_ ≫ h) ≫ (forget S).map g) ≫ comm_iso.inv.app b' =
         ((ℛ.adj.hom_equiv a.A ((forget S).obj b)).to_fun (((adj S).hom_equiv _ b).to_fun (_ ≫ h)) ≫ comm_iso.inv.app b) ≫ (R'.map g).f,
  conv_lhs {congr, apply_congr ℛ.adj.hom_equiv_naturality_right },
  change ((ℛ.adj.hom_equiv a.A ((forget S).obj b)).to_fun (((adj S).hom_equiv _ b).to_fun (_ ≫ h)) ≫ R.map ((forget S).map g)) ≫ comm_iso.inv.app b' =
         ((ℛ.adj.hom_equiv a.A ((forget S).obj b)).to_fun (((adj S).hom_equiv _ b).to_fun (_ ≫ h)) ≫ comm_iso.inv.app b) ≫ (R'.map g).f,
  rw [category.assoc, category.assoc],
  congr' 1,
  apply comm_iso.inv.naturality,
end

def is_adj (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) : L' R comm_iso hrc ⊣ R' :=
adjunction.adjunction_of_equiv_left _ _

end lift_left_adjoint
open lift_left_adjoint

def lift_algebra_left_adjoint {R : D ⥤ C} [is_right_adjoint R] {R' : algebra S ⥤ algebra T}
  (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) :
  is_right_adjoint R' :=
{ left := L' R comm_iso hrc,
  adj := is_adj R comm_iso hrc }

variables {A : Type u₃} [𝒜 : category.{v₁} A] {B : Type u₄} [ℬ : category.{v₂} B]
include 𝒜 ℬ

def adjoint_lifting {Q : A ⥤ B} {R : C ⥤ D} {U : A ⥤ C} {V : B ⥤ D}
  [is_right_adjoint R] [monadic_right_adjoint U] [monadic_right_adjoint V]
  (comm_iso : Q ⋙ V ≅ U ⋙ R)
  (hrc : has_reflexive_coequalizers A) :
  is_right_adjoint Q :=
begin
  let i : (comparison U).inv ⋙ Q ⋙ V ≅ forget (left_adjoint U ⋙ U) ⋙ R :=
    iso_whisker_left (comparison U).inv comm_iso ≪≫ iso_whisker_right (comparison U).inv_fun_id (forget (left_adjoint U ⋙ U) ⋙ R),
  let i₂ : ((comparison U).inv ⋙ Q ⋙ comparison V) ⋙ forget _ ≅ forget _ ⋙ R := i,
  have := lift_algebra_left_adjoint i₂ (reflexive_coeq_of_equiv (comparison U) hrc),
  have i₃ : comparison U ⋙ (comparison U).inv ⋙ Q ⋙ comparison V ⋙ (comparison V).inv ≅ Q,
    exact calc comparison U ⋙ (comparison U).inv ⋙ Q ⋙ comparison V ⋙ (comparison V).inv ≅ Q ⋙ comparison V ⋙ (comparison V).inv :
      begin
        exact iso_whisker_right (comparison U).fun_inv_id (Q ⋙ comparison V ⋙ (comparison V).inv),
      end
          ... ≅ Q : by exact iso_whisker_left Q (comparison V).fun_inv_id ≪≫ Q.right_unitor,
  suffices: is_right_adjoint (comparison U ⋙ (comparison U).inv ⋙ Q ⋙ comparison V ⋙ (comparison V).inv),
    apply @right_adjoint_of_nat_iso _ _ _ _ _ _ i₃ this,
  haveI : is_right_adjoint (comparison U) := right_adjoint_of_equiv,
  haveI : is_right_adjoint (comparison V).inv := right_adjoint_of_equiv,
  haveI : is_right_adjoint (comparison U ⋙ (comparison U).inv ⋙ Q ⋙ comparison V) := right_adjoint_of_comp,
  apply @right_adjoint_of_comp _ _ _ _ _ _ (comparison U ⋙ (comparison U).inv ⋙ Q ⋙ comparison V),
end

end monad
end category_theory