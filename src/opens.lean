/- Author: E.W.Ayers
   Show that the open covers for a topological space form a basis for a grothendieck topology.
 -/
import topology.category.Top.opens
import category_theory.limits.lattice
import category_theory.limits.limits
import category_theory.limits.shapes.pullbacks
import .grothendieck

universes u
open category_theory
open topological_space
open category_theory.limits

namespace topological_space.opens

/- [TODO] this is probably in mathlib somewhere. -/
/-- `covers X U ℱ` means that ℱ is an open cover of U. -/
def covers (X : Top) : arrow_set (opens X) :=
λ U ℱ, ∀ (x : X) (xU : x ∈ U), ∃ (V : over U), V ∈ ℱ ∧ x ∈ V.left

variables {X : Top}

instance opens_has_limits : @has_limits (opens X) (opens.opens_category) := 
limits.has_limits_of_complete_lattice

instance opens_has_pullbacks : @has_pullbacks (opens X) (opens.opens_category) :=
⟨@has_limits.has_limits_of_shape _ _ opens.opens_has_limits _ _⟩

instance opens_has_cospan_limits {U V W : opens X} {f : U ⟶ W} {g : V ⟶ W} : has_limit (cospan f g) :=
@has_limits_of_shape.has_limit _ _ _ _ (@has_limits.has_limits_of_shape _ _ opens.opens_has_limits _ _) _

variables {U V W : opens X}

/- [todo] this can be moved to category_theory/limits/lattice -/
lemma eq_of_iso (e : U ≅ W) : U = W :=
begin
    rcases e with ⟨⟨⟨_⟩⟩,⟨⟨_⟩⟩,_,_⟩, 
    apply partial_order.le_antisymm,
    assumption,
    assumption
end

lemma over_eq_of_left_eq : Π {f g : over U}, f.left = g.left → f = g 
| ⟨_,⟨⟩,⟨⟨_⟩⟩⟩ ⟨_,⟨⟩,⟨⟨_⟩⟩⟩ rfl := rfl

open lattice
/- [todo] this can be moved to category_theory/limits/lattice -/
lemma pullback_is_inter {f : U ⟶ W} {g : V ⟶ W} : pullback f g = U ⊓ V :=
begin
    apply eq_of_iso,
    rcases (pullback.fst : pullback f g ⟶ U) with ⟨⟨π1⟩⟩,
    rcases (pullback.snd : pullback f g ⟶ V) with ⟨⟨π2⟩⟩,
    refine ⟨⟨⟨le_inf π1 π2⟩⟩,pullback.lift ⟨⟨inf_le_left⟩⟩ ⟨⟨inf_le_right⟩⟩ rfl,rfl,rfl⟩,
end

instance : grothendieck.basis (covers X) :=
{ has_isos :=
    begin 
        -- all isos in opens U are equality.
        intros U V e x xU,
        refine ⟨over.mk e.hom, _,_⟩, 
        simp, 
        have : U = V, apply eq_of_iso e, 
        simpa [this],
    end, 
  has_pullbacks :=
    begin
        -- idea: ℱ is covering for U 
        -- ⇒ {V ∩ W | W ∈ ℱ} is a covering for V
        intros U V ℱ h₁ g, 
        intros x xV,
        rcases g with ⟨⟨g⟩⟩,
        rcases h₁ x (g xV) with ⟨f,fF,xf⟩, 
        refine ⟨over.mk ⟨⟨inf_le_right⟩⟩,⟨f,fF,_⟩,⟨xf,xV⟩⟩,
        apply over_eq_of_left_eq, 
            simp [over.pullback],
            rw pullback_is_inter,
            rw inf_comm, refl,
    end,
  trans := 
    begin
        -- idea: ℱ covers U and 𝒢 U covers V for each V ∈ ℱ 
        -- ⇒ ⋃ 𝒢 covers U
        intros U, 
        rintros _ FcU _ GcF x xU,
        rcases FcU x xU with ⟨V,VF,xV⟩,
        rcases GcF VF x xV with ⟨W,WG,xW⟩, 
        refine ⟨over.mk (W.hom ≫ V.hom),⟨_,VF,⟨W,WG,rfl⟩⟩,xW⟩,
    end
}

def covering_sieve (X : Top):= sieve_set.generate (covers X)

instance : grothendieck (covering_sieve X) :=
grothendieck.of_basis

end topological_space.opens
