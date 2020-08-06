import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.regular_mono
import category.pullbacks

universes v u u₂

namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C]

variables {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

structure is_kernel_pair :=
(comm : a ≫ f = b ≫ f)
(is_limit : is_limit (pullback_cone.mk _ _ comm))

attribute [reassoc] is_kernel_pair.comm

namespace is_kernel_pair

instance : subsingleton (is_kernel_pair f a b) :=
⟨λ P Q, begin
  cases P,
  cases Q,
  congr,
end⟩

variables {f a b}

def lift' {S : C} (k : is_kernel_pair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
  { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
pullback_cone.is_limit.lift' k.is_limit _ _ w

def sub {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : is_kernel_pair (f₁ ≫ f₂) a b) :
  is_kernel_pair f₁ a b :=
{ comm := comm,
  is_limit := is_limit.mk' _ $ λ s,
  begin
    let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) := pullback_cone.mk s.fst s.snd (s.condition_assoc _),
    refine ⟨big_k.is_limit.lift s',
            big_k.is_limit.fac _ walking_cospan.left,
            big_k.is_limit.fac _ walking_cospan.right,
            λ m m₁ m₂, _⟩,
    apply big_k.is_limit.hom_ext,
    refine ((pullback_cone.mk a b _) : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _,
    erw m₁,
    symmetry,
    apply big_k.is_limit.fac _ walking_cospan.left,
    erw m₂,
    symmetry,
    apply big_k.is_limit.fac _ walking_cospan.right,
  end }

def sub' {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (big_k : is_kernel_pair (f₁ ≫ f₂) a b) :
  is_kernel_pair f₁ a b :=
{ comm := by rw [← cancel_mono f₂, assoc, big_k.comm, assoc],
  is_limit := is_limit.mk' _ $ λ s,
  begin
    let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) := pullback_cone.mk s.fst s.snd (s.condition_assoc _),
    refine ⟨big_k.is_limit.lift s',
            big_k.is_limit.fac _ walking_cospan.left,
            big_k.is_limit.fac _ walking_cospan.right,
            λ m m₁ m₂, _⟩,
    apply big_k.is_limit.hom_ext,
    refine ((pullback_cone.mk a b _) : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _,
    erw m₁,
    symmetry,
    apply big_k.is_limit.fac _ walking_cospan.left,
    erw m₂,
    symmetry,
    apply big_k.is_limit.fac _ walking_cospan.right,
  end }

def sub'' {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (small_k : is_kernel_pair f₁ a b) :
  is_kernel_pair (f₁ ≫ f₂) a b :=
{ comm := by rw [small_k.comm_assoc],
  is_limit := is_limit.mk' _ $ λ s,
  begin
    refine ⟨_, _, _, _⟩,
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).1,
    rw [← cancel_mono f₂, assoc, s.condition, assoc],
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1,
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2,
    intros m m₁ m₂,
    apply small_k.is_limit.hom_ext,
    refine ((pullback_cone.mk a b _) : pullback_cone f₁ _).equalizer_ext _ _,
    rwa (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1,
    rwa (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2,
  end }


/--
If `a,b` is the kernel pair of `f`, and `f` is a coequalizer morphism, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def to_coequalizer (k : is_kernel_pair f a b) [r : regular_epi f] :
  is_colimit (cofork.of_π f k.comm) :=
begin
  let t := k.is_limit.lift (pullback_cone.mk _ _ r.w),
  have ht : t ≫ a = r.left := k.is_limit.fac _ walking_cospan.left,
  have kt : t ≫ b = r.right := k.is_limit.fac _ walking_cospan.right,
  apply cofork.is_colimit.mk _ _ _ _,
  { intro s,
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).1,
    rw [← ht, assoc, s.condition, reassoc_of kt] },
  { intro s,
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).2 },
  { intros s m w,
    apply r.is_colimit.hom_ext,
    rintro ⟨⟩,
    change (r.left ≫ f) ≫ m = (r.left ≫ f) ≫ _,
    rw [assoc, assoc],
    congr' 1,
    erw (cofork.is_colimit.desc' r.is_colimit s.π _).2,
    apply w walking_parallel_pair.one,
    erw (cofork.is_colimit.desc' r.is_colimit s.π _).2,
    apply w walking_parallel_pair.one }
end

end is_kernel_pair
end category_theory