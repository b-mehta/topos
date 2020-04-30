import power
import category_theory.full_subcategory
import category_theory.limits.creates
import category_theory.reflect_isomorphisms
import reflects
import cartesian_closed

open category_theory category_theory.category category_theory.limits
open subobj

universes v u u₂

variables (C : Type u) [𝒞 : category.{v} C] [has_finite_limits.{v} C] [has_power_objects.{v} C]
include 𝒞

def and_arrow : (Ω : C) ⨯ Ω ⟶ Ω := intersect.intersect _

class topology (j : (Ω : C) ⟶ Ω) :=
(ax1 : truth ≫ j = truth)
(ax2 : j ≫ j = j)
(ax3 : and_arrow C ≫ j = limits.prod.map j j ≫ and_arrow C)

variables {C} (j : (Ω : C) ⟶ Ω) [topology.{v} C j]

namespace closure

variables {E A : C}

def obj (m : A ⟶ E) [mono m] : C := pullback truth (classifier_of m ≫ j)

def arrow (m : A ⟶ E) [mono m] : closure.obj j m ⟶ E := pullback.snd

instance (m : A ⟶ E) [mono m] : mono (closure.arrow j m) := pullback.snd_of_mono

def less_than_closure (m : A ⟶ E) [mono m] : A ⟶ closure.obj j m :=
pullback.lift (square.k m) m (by rw [← reassoc_of (subobj.square.commutes m), topology.ax1])

lemma is_lt (m : A ⟶ E) [mono m] : less_than_closure j m ≫ closure.arrow j m = m :=
pullback.lift_snd _ _ _

class dense (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (arrow j m))

class closed (m : A ⟶ E) extends mono.{v} m :=
(gives_iso : is_iso (less_than_closure j m))

-- def closure_natural {F : C} (f : F ⟶ E) (m : A ⟶ E) [mono.{v} m] : obj j (pullback.snd : pullback m f ⟶ F) ≅ pullback (arrow j m) f :=
-- { hom :=
--   begin
--     apply pullback.lift _ pullback.snd _,
--     { apply pullback.lift pullback.fst (pullback.snd ≫ f) _,
--       { rw pullback.condition,  } },
--     { rw [arrow, pullback.lift_snd] },
--   end,
--   inv :=
--   begin
--     apply pullback.lift _ pullback.snd _,
--     { apply pullback.fst ≫ pullback.fst },
--     { rw [assoc, pullback.condition], sorry }
--   end,
--   hom_inv_id' :=
--   begin
--     apply pullback.hom_ext,
--     { rw [id_comp, assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst] },
--     { rw [id_comp, assoc],
--       slice_lhs 2 3 {rw pullback.lift_snd},
--       rw pullback.lift_snd }
--   end,
--   inv_hom_id' :=
--   begin
--     apply pullback.hom_ext,
--     { rw [id_comp, assoc, pullback.lift_fst],
--       apply pullback.hom_ext,
--       { rw [assoc, pullback.lift_fst, pullback.lift_fst] },
--       { rw [assoc, pullback.lift_snd, pullback.lift_snd_assoc, ← pullback.condition], refl } },
--     { rw [id_comp, assoc, pullback.lift_snd, pullback.lift_snd] }
--   end
-- }

end closure

variable (C)
structure separated :=
(A : C)
(subsingleton_extend : Π B B' (m : B' ⟶ B) f' [closure.dense j m],
  subsingleton {f : B ⟶ A // m ≫ f = f'})

structure sheaf' :=
(A : C)
(unique_extend : Π {B B'} (m : B' ⟶ B) f' [closure.dense j m],
  unique {f : B ⟶ A // m ≫ f = f'})

def forget_sheaf : sheaf'.{v} C j → C := sheaf'.A

def sheaf := induced_category C (forget_sheaf C j)

instance sheaf_category.category : category (sheaf C j) := induced_category.category _
def forget : sheaf C j ⥤ C := induced_functor _

namespace construct_limits

instance sheaf_forget_reflects_limits : reflects_limits (forget C j) :=
forget_reflects_limits (forget_sheaf C j)

variables {C} {J : Type v} [𝒥₁ : small_category J] {K : J ⥤ sheaf C j} {c : cone (K ⋙ forget C j)} (t : is_limit c)
variables {B B' : C} (m : B' ⟶ B) (f' : B' ⟶ c.X)

@[simps]
def alt_cone [mono m] [closure.dense j m] : cone (K ⋙ forget C j) :=
{ X := B,
  π :=
  { app := λ i, ((K.obj i).unique_extend m (f' ≫ c.π.app i)).1.1.1,
    naturality' := λ i₁ i₂ g,
    begin
      dsimp,
      rw [id_comp],
      have q := ((K.obj i₂).unique_extend m (f' ≫ c.π.app i₂)).2,
      let h : {f // m ≫ f = f' ≫ c.π.app i₂} := ⟨((K.obj i₁).unique_extend m (f' ≫ c.π.app i₁)).1.1.1 ≫ (K ⋙ forget C j).map g, _⟩,
      specialize q h,
      rw subtype.ext at q,
      exact q.symm,
      rw [reassoc_of ((K.obj i₁).unique_extend m (f' ≫ c.π.app i₁)).1.1.2, c.w g],
    end } }

instance sheaf_forget_creates_limits : creates_limits (forget C j) :=
{ creates_limits_of_shape := λ J 𝒥₁, by exactI
  { creates_limit := λ K,
    { lifts := λ c t,
      { lifted_cone :=
        { X :=
          { A := c.X,
            unique_extend := λ B B' m f' d,
            begin
              refine ⟨⟨⟨t.lift (alt_cone j m f'), _⟩⟩, _⟩,
              { apply t.hom_ext,
                intro i,
                rw [assoc, t.fac (alt_cone j m f')],
                exact ((K.obj i).unique_extend m (f' ≫ c.π.app i)).1.1.2 },
              { rintro ⟨f₂, hf₂⟩,
                congr,
                apply t.uniq (alt_cone j m f'),
                intro i,
                dsimp [alt_cone],
                apply congr_arg subtype.val (((K.obj i).unique_extend m (f' ≫ c.π.app i)).2 ⟨_, _⟩),
                rw reassoc_of hf₂ }
            end },
          π :=
          { app := c.π.app,
            naturality' := λ X Y f, c.π.naturality f } },
        valid_lift := cones.ext (iso.refl _) (λ i, (id_comp _).symm) } } } }

end construct_limits

instance sheaf_has_finite_limits : has_finite_limits.{v} (sheaf C j) :=
{ has_limits_of_shape := λ J 𝒥₁ 𝒥₂, by exactI
  { has_limit := λ F,
    has_limit_of_created F (forget C j) } }

variable {C}

def dense_prod_map_id (A : C) {B B' : C} (m : B' ⟶ B) [closure.dense.{v} j m] :
  closure.dense.{v} j (limits.prod.map (𝟙 A) m) :=
sorry

set_option trace.type_context.is_def_eq true

def sheaf_exponential (A : C) (s : sheaf C j) : sheaf C j :=
{ A := exp A s.A,
  unique_extend := λ B B' m f' d,
  begin
    haveI := @dense_prod_map_id _ _ _ _ j _ A _ _ m d,
    refine ⟨⟨⟨cchat (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).1.1.1, _⟩⟩, _⟩,
    { rw ← exp_transpose_natural_left,
      rw (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).1.1.2,
      exact ((exp.adjunction _).hom_equiv _ _).right_inv f' },
    rintro ⟨a, ha⟩,
    have z : limits.prod.map (𝟙 A) m ≫ unhat a = unhat f',
      rw [← exp_transpose_natural_left_symm m a, ha],
    rw ← (s.unique_extend (limits.prod.map (𝟙 A) m) (unhat f')).2 ⟨unhat a, z⟩,
    congr,
    symmetry,
    refine ((exp.adjunction A).hom_equiv _ _).right_inv a,
  end
}