import category_theory.limits.limits
import category_theory.monad.algebra
import category_theory.monad
import category_theory.limits.shapes.equalizers
import creates
import beck2

universes v₁ v₂ u₁ u₂

namespace category_theory
namespace monad

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞
variables {T : C ⥤ C} [monad.{v₁} T]

lemma free_forget : free T ⋙ forget T = T :=
begin
  apply functor.ext _ _,
  intro X,
  refl,
  intros,
  simp
end

open monad limits

lemma thing (A : algebra T) : (η_ T).app ((forget T).obj A) ≫ (forget T).map ((adj T).counit.app A) = 𝟙 ((forget T).obj A) :=
begin
  dunfold forget adj adjunction.mk_of_hom_equiv, dsimp, rw T.map_id, rw category.id_comp,
  exact A.unit,
end

include 𝒟
variables {S : D ⥤ D} [monad.{v₂} S]

variables (R : D ⥤ C) [ℛ : is_right_adjoint R]
include ℛ
variable {R' : algebra S ⥤ algebra T}

abbreviation L : C ⥤ D := left_adjoint R

def transport (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (B : algebra S) :
  (forget T).obj (R'.obj B) ≅ R.obj ((forget S).obj B) :=
iso.app comm_iso B

namespace part1

def f1 (B : D) : R.obj B ⟶ R.obj (S.obj B) :=
R.map ((η_ S).app B)

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
    apply function.injective_of_left_inverse ((adj S).hom_equiv _ _).left_inv,
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
    erw is_right_adjoint.adj.counit.naturality ((η_ S).app ((L R).obj a.A)),
    change (L R).map (is_right_adjoint.adj.unit.app a.A) ≫
      (is_right_adjoint.adj).counit.app (((L R).obj a.A)) ≫
        ((η_ S).app ((L R).obj a.A)) = (adj S).unit.app ((L R).obj a.A),
    slice_lhs 1 2 {erw (is_right_adjoint.adj).left_triangle_components},
    erw category.id_comp,
    dunfold adj adjunction.mk_of_hom_equiv,
    dsimp,
    erw category.comp_id
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
  left_inv := λ f, begin dsimp, slice_lhs 2 3 {rw nat_iso.inv_hom_id_app}, apply category.comp_id end,
  right_inv := λ g, begin dsimp, slice_lhs 2 3 {rw nat_iso.hom_inv_id_app}, apply category.comp_id end
}
-- This final equivalence might be useful in other contexts (that is, A ⟶ B ≃ A ⟶ C when B ≅ C). It should also probably be a consequence of Yoneda

def sound (a : algebra T) (b : algebra S) (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (h' : (free S).obj ((L R).obj a.A) ⟶ b) :
  (free S).map ((L R).map a.a) ≫ h' = part2.φ' R a.A comm_iso ≫ h' ↔ T.map ((arrow_map R a b comm_iso).to_fun h') ≫ (R'.obj b).a = a.a ≫ ((arrow_map R a b comm_iso).to_fun h') :=
begin
  let h := (((adj S).hom_equiv _ _).to_fun h'),
  have: (free S).map ((L R).map a.a) ≫ h' = part2.φ' R a.A comm_iso ≫ h' ↔ ((L R).map a.a) ≫ h = part2.φ R a.A comm_iso ≫ (forget S).map h',
  { erw [← (adj S).hom_equiv_naturality_left, part2.φ', ← (adj S).hom_equiv_naturality_right_symm],
    split,
    { intro k,
      rw k,
      apply ((adj S).hom_equiv _ _).right_inv },
    { intro k,
      rw ← k,
      apply (((adj S).hom_equiv _ _).left_inv _).symm } },
  rw this, clear this,
  let hbar := ((is_right_adjoint.adj).hom_equiv a.A b.A).to_fun h,
  have: (L R).map a.a ≫ h = part2.φ R a.A comm_iso ≫ (forget S).map h' ↔ a.a ≫ hbar = (forget T).map ((free T).map (part2.γ R a.A)) ≫ (forget T).map (part1.f2 _ _ comm_iso) ≫ comm_iso.hom.app ((free S).obj ((L R).obj a.A)) ≫ R.map ((forget S).map h'),
  { sorry },
  rw this, clear this,
  erw ← comm_iso.hom.naturality h',
  change a.a ≫ hbar = T.map (part2.γ R a.A) ≫ (part1.f2 R ((L R).obj a.A) comm_iso).f ≫ (R' ⋙ forget T).map h' ≫ comm_iso.hom.app b ↔
    T.map (hbar ≫ comm_iso.inv.app b) ≫ (R'.obj b).a = a.a ≫ hbar ≫ comm_iso.inv.app b,
  conv_rhs {rw ← category.assoc, rw eq_comm},
  erw (iso.app comm_iso b).comp_inv_eq,
  conv_lhs {rw [← category.assoc, ← category.assoc]},
  convert iff.refl _ using 3,

  -- have : R.obj (b.A) ⟶ (R'.obj b).A := comm_iso.inv.app b,
  -- have := (R'.obj b).a,
  -- have := hbar,

  -- rw T.map_comp,
  -- dunfold part2.γ part1.f2 transport iso.app part1.f1, dsimp,
  change T.map (((is_right_adjoint.adj.hom_equiv a.A b.A).to_fun h) ≫ comm_iso.inv.app b) ≫ (R'.obj b).a =
    ((forget T).map ((free T).map ((is_right_adjoint.adj).unit.app a.A)) ≫
         (forget T).map (((adj T).hom_equiv (R.obj ((L R).obj a.A)) (R'.obj ((free S).obj ((L R).obj a.A)))).inv_fun
            (R.map ((η_ S).app ((L R).obj a.A)) ≫ comm_iso.inv.app ((free S).obj ((L R).obj a.A))))) ≫
      (forget T).map (R'.map h'),
  -- dunfold adj adjunction.mk_of_hom_equiv free forget, dsimp,
  have: (((adj T).hom_equiv _ _).inv_fun (R.map ((η_ S).app ((L R).obj a.A)) ≫ comm_iso.inv.app ((free S).obj ((L R).obj a.A)))) = _ :=
    (adj T).hom_equiv_naturality_left_symm (R.map ((η_ S).app ((L R).obj a.A))) (comm_iso.inv.app ((free S).obj ((L R).obj a.A))),
  erw this, clear this,
  change T.map (((is_right_adjoint.adj).hom_equiv a.A b.A).to_fun h ≫ comm_iso.inv.app b) ≫ (R'.obj b).a =
    ((forget T).map ((free T).map ((is_right_adjoint.adj).unit.app a.A)) ≫
         (forget T).map
           ((free T).map (R.map ((η_ S).app ((L R).obj a.A))) ≫
              ((adj T).hom_equiv (R.obj (S.obj ((L R).obj a.A))) (R'.obj ((free S).obj ((L R).obj a.A)))).inv_fun
                (comm_iso.inv.app ((free S).obj ((L R).obj a.A))))) ≫
      (forget T).map (R'.map h'),



  -- conv_rhs {congr, congr, skip, congr, erw (adj T).hom_equiv_counit,  },
    -- (adj T).hom_equiv_counit,

  -- have := comm_iso.inv.naturality h',
end
#check eq.symm
omit ℛ
def elast (a : algebra T) (b : algebra S) : {g : a.A ⟶ (forget T).obj (R'.obj b) // T.map g ≫ (R'.obj b).a = a.a ≫ g} ≃ (a ⟶ R'.obj b) :=
{ to_fun := λ f, {f := f.1, h' := f.2},
  inv_fun := λ g, ⟨g.1, g.2⟩,
  left_inv := λ ⟨f, _⟩, rfl,
  right_inv := λ ⟨g, _⟩, rfl}
include ℛ

def L'e  (comm_iso : R' ⋙ forget T ≅ forget S ⋙ R) (hrc : has_reflexive_coequalizers (algebra S)) (a : algebra T) (b : algebra S) :
  (L'obj R comm_iso hrc a ⟶ b) ≃ (a ⟶ R'.obj b) :=
begin
  apply equiv.trans (e1 _ _ _ _),
  apply equiv.trans _ (elast _ _),
  exact restrict_equivalence (arrow_map R a b _) _ _ (sound R a b comm_iso),
end

end monad
end category_theory