import category_theory.closed.cartesian
import category_theory.isomorphism
import category_theory.adjunction.limits
import tactic.ring

universes v v₂ u u₂

namespace category_theory
open category limits limits.prod

variables (C : Type u) [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables [has_finite_products C]

structure natural_number_object :=
(N : C)
(o : ⊤_ C ⟶ N)
(succ : N ⟶ N)
(lift : Π (A : C) (a : ⊤_ C ⟶ A) (t : A ⟶ A), N ⟶ A)
(fac₁ : ∀ A a t, o ≫ lift A a t = a)
(fac₂ : ∀ A a t, succ ≫ lift A a t = lift A a t ≫ t)
(uniq : ∀ A a t f, o ≫ f = a → succ ≫ f = f ≫ t → f = lift A a t)

attribute [reassoc] natural_number_object.fac₁ natural_number_object.fac₂

namespace natural_number_object

-- variable

variables (N : natural_number_object C) {Q A B : C}

def terminal_iso (F : C ⥤ D) [preserves_limits_of_shape (discrete pempty) F] [has_terminal D] :
  ⊤_ D ≅ F.obj (⊤_ C) :=
is_limit.cone_points_iso_of_nat_iso (limit.is_limit _) (preserves_limit.preserves (limit.is_limit _)) (functor.empty_ext _ _)

-- lemma hom_ext (f g : N.N ⟶ A) (hf₁ : N.o ≫ f = N.o ≫ g) (hf₂ : N.succ ≫ f = N.succ ≫ g) : f = g :=
-- begin

-- end

lemma eq_id_of_comm_zero_succ (f : N.N ⟶ N.N) (hf₁ : N.o ≫ f = N.o) (hf₂ : N.succ ≫ f = f ≫ N.succ) :
  f = 𝟙 _ :=
by rw [N.uniq _ _ _ _ hf₁ hf₂, N.uniq _ _ _ _ (comp_id _) (by simp)]

def os_closed {N' : C} (m : N' ⟶ N.N) [mono m] (o' : ⊤_ C ⟶ N') (s' : N' ⟶ N') (ho : o' ≫ m = N.o)
  (hs : m ≫ N.succ = s' ≫ m) : is_iso m :=
begin
  have : split_epi m,
    refine ⟨N.lift _ o' s', _⟩,
    apply eq_id_of_comm_zero_succ,
    rw [fac₁_assoc, ho],
    rw [fac₂_assoc, assoc, hs],
  resetI,
  apply is_iso_of_mono_of_split_epi,
end

variable {C}
def unit : Q ⟶ ⊤_ C := terminal.from Q
def apply {A B} (f : A ⟶ B) (h : Q ⟶ A) : Q ⟶ B := h ≫ f
instance {A B : C} : has_coe_to_fun (A ⟶ B) :=
{ F := λ f, Π {Q}, (Q ⟶ A) → (Q ⟶ B),
  coe := λ f Q h, h ≫ f }
def zero : Q ⟶ N.N := N.o unit

lemma expand_apply {A B : C} (f : A ⟶ B) (h : Q ⟶ A) : f h = h ≫ f := rfl
@[simp]
lemma apply_id (f : A ⟶ B) : f (𝟙 _) = f := id_comp _
@[simp]
lemma term_zero : N.zero = N.o :=
begin
  change _ ≫ _ = _,
  convert id_comp N.o,
end

abbreviation pair {A B} (f : Q ⟶ A) (g : Q ⟶ B) : Q ⟶ A ⨯ B := prod.lift f g
notation `❲` f `, ` g `❳` := pair f g

lemma right_unitor_hom (a : Q ⟶ A) : iso.hom (prod.right_unitor A) ❲a, unit❳ = a :=
begin
  apply prod.lift_fst,
end

@[reducible] def one : Q ⟶ N.N := N.succ N.zero
lemma hom_eq_id (f : N.N ⟶ N.N) (h0 : ∀ Q, f (N.zero : Q ⟶ _) = N.zero)
  (hsucc : ∀ Q (n : Q ⟶ N.N), f (N.succ n) = N.succ (f n)) : f = 𝟙 _ :=
begin
  apply eq_id_of_comm_zero_succ,
  rw ← term_zero,
    apply h0,
  specialize hsucc _ (𝟙 _),
  rw [apply_id, apply_id] at hsucc,
  apply hsucc
end

section recursion

variables {C}

/-- Define a function by recursion. -/
def recurse' (g : ⊤_ C ⟶ B) (h : N.N ⨯ B ⟶ B) : N.N ⟶ B :=
N.lift _ (prod.lift N.o g) (prod.lift (limits.prod.fst ≫ N.succ) h) ≫ limits.prod.snd

section
variables (g : ⊤_ C ⟶ B) (h : N.N ⨯ B ⟶ B)
lemma recurse'_zero :
  N.o ≫ N.recurse' g h = g :=
begin
  change N.o ≫ _ ≫ _ = _,
  rw [N.fac₁_assoc, prod.lift_snd],
end

lemma int_recurse'_zero : N.recurse' g h N.zero = g :=
begin
  change (_ ≫ _) ≫ _ = _,
  rw [assoc, recurse'_zero],
  convert id_comp _,
end

lemma recurse'_succ :
  N.succ ≫ N.recurse' g h = prod.lift (𝟙 _) (N.recurse' g h) ≫ h :=
begin
  change N.succ ≫ _ ≫ _ = prod.lift _ (_ ≫ _) ≫ _,
  rw [N.fac₂_assoc, prod.lift_snd],
  congr' 1,
  apply prod.hom_ext,
  rw [prod.lift_fst],
  apply eq_id_of_comm_zero_succ,
  rw [N.fac₁_assoc, prod.lift_fst],
  rw [N.fac₂_assoc, prod.lift_fst, assoc],
  rw [prod.lift_snd],
end

lemma int_recurse'_succ (n : Q ⟶ N.N) : N.recurse' g h (N.succ n) = h ❲n, N.recurse' g h n❳ :=
begin
  change (_ ≫ _) ≫ _ = prod.lift _ (_ ≫ _) ≫ _,
  rw [assoc, recurse'_succ, ← assoc],
  congr' 1,
  apply prod.hom_ext; simp,
end

lemma recurse'_uniq (q) :
  N.o ≫ q = g →
  N.succ ≫ q = prod.lift (𝟙 _) q ≫ h →
  q = N.recurse' g h :=
begin
  intros h₁ h₂,
  have : limits.prod.lift (𝟙 _) q = N.lift _ (prod.lift N.o g) (prod.lift (limits.prod.fst ≫ N.succ) h),
    apply N.uniq,
    apply prod.hom_ext; simp [*],
    apply prod.hom_ext; simp [*],
  change q = _ ≫ _,
  rw ← this,
  simp,
end

lemma int_recurse'_uniq (q : N.N ⟶ B) :
  q N.zero = g
→ (∀ Q (n : Q ⟶ N.N), q (N.succ n) = h ❲n, q n❳)
→ q = N.recurse' g h :=
begin
  intros q₁ q₂,
  apply N.recurse'_uniq,
  { rw [← q₁, expand_apply, term_zero] },
  { specialize q₂ N.N (𝟙 _),
    rw [apply_id, apply_id, expand_apply] at q₂,
    rw [q₂], refl }
end

lemma int_recurse'_hom_ext (q₁ q₂ : N.N ⟶ B) [has_equalizers C] :
  (∀ Q, q₁ N.zero = q₂ (N.zero : Q ⟶ _))
→ (∀ Q (n : Q ⟶ N.N), q₁ n = q₂ n → q₁ (N.succ n) = q₂ (N.succ n))
→ q₁ = q₂ :=
begin
  intros h₁ h₂,
  let i := equalizer q₁ q₂,
  let i' : i ⟶ N.N := equalizer.ι q₁ q₂,
  have : (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _ := h₂ i i' (equalizer.condition _ _),
  have : N.o ≫ q₁ = N.o ≫ q₂,
    rw ← term_zero,
    apply h₁,
  have := N.os_closed _ i' (equalizer.lift N.o ‹_›) (equalizer.lift (i' ≫ N.succ) ‹_›) _ _,
  resetI,
  rw [← cancel_epi i'], apply equalizer.condition,
  rw equalizer.lift_ι,
  rw equalizer.lift_ι,
end

end

/-- Define a function with parameters by primitive recursion. -/
def recurse [cartesian_closed C] (g : A ⟶ B) (h : A ⨯ N.N ⨯ B ⟶ B) : A ⨯ N.N ⟶ B :=
cartesian_closed.uncurry
  (N.recurse'
    (internalize_hom g)
    (cartesian_closed.curry
      (prod.lift
        (prod.lift fst (snd ≫ fst))
        (limits.prod.map (𝟙 _) snd ≫ (ev _).app _) ≫ h)))

variables (g : A ⟶ B) (h : A ⨯ N.N ⨯ B ⟶ B)
-- TODO: these lemmas are stated as commutative diagrams but they're
-- probably much easier to understand if they're in terms of
-- elements
lemma recurse_zero [cartesian_closed C] :
  limits.prod.map (𝟙 A) N.o ≫ N.recurse g h = (prod.right_unitor _).hom ≫ g :=
begin
  dsimp [recurse],
  rw [← uncurry_natural_left, N.recurse'_zero, internalize_hom, uncurry_curry],
end

lemma thing {B' : C} {f : A ⟶ B} {g : B ⟶ B'} (q : Q ⟶ A) :
  g (f q) = (f ≫ g) q :=
begin
  apply assoc,
end

lemma map_pair {B' : C} (a : Q ⟶ A) (b : Q ⟶ B) (f : B ⟶ B') : ❲a, f b❳ = limits.prod.map (𝟙 _) f ❲a, b❳ :=
by rw [expand_apply, expand_apply, prod.lift_map, comp_id]

lemma real_map_pair {A' B' : C} (a : Q ⟶ A) (b : Q ⟶ B) (f : A ⟶ A') (g : B ⟶ B') : limits.prod.map f g ❲a, b❳ = ❲f a, g b❳ :=
by { rw [expand_apply, prod.lift_map], refl }

lemma id_apply (x : Q ⟶ A) : (𝟙 A : _ ⟶ _) x = x :=
comp_id _

lemma pair_apply {B' : C} (x : Q ⟶ B') (g h) : (❲g, h❳ : B' ⟶ A ⨯ B) x = ❲g x, h x❳ :=
begin
  rw [expand_apply],
  apply prod.hom_ext,
    rw [assoc, prod.lift_fst, prod.lift_fst, expand_apply],
  rw [assoc, prod.lift_snd, prod.lift_snd, expand_apply],
end

lemma pair_fst_snd : ❲fst, snd❳ = 𝟙 (A ⨯ B) :=
begin
  apply prod.hom_ext; simp,
end

lemma pair_ext (a : Q ⟶ A ⨯ B) : ❲(fst : A ⨯ B ⟶ _) a, (snd : A ⨯ B ⟶ B) a❳ = a :=
begin
  rw [← pair_apply, pair_fst_snd, id_apply],
end

lemma func_assoc {W X Y Z : C} (x : X ⟶ Y) (g : Y ⟶ W) (f : W ⟶ Z) : f (g x) = (f g) x :=
begin
  apply assoc,
end

lemma zero_apply (x : Q ⟶ A) : N.zero x = N.zero :=
begin
  change _ ≫ _ ≫ _ = _ ≫ _,
  rw ← assoc, congr' 1,
end

@[reducible] def two : Q ⟶ N.N := N.succ N.one
@[reducible] def three : Q ⟶ N.N := N.succ N.two
@[reducible] def four : Q ⟶ N.N := N.succ N.three

lemma one_apply (x : Q ⟶ A) : N.one x = N.one :=
begin
  rw [← func_assoc, zero_apply]
end
lemma two_apply (x : Q ⟶ A) : N.two x = N.two :=
begin
  rw [← func_assoc, one_apply]
end

lemma int_recurse_zero [cartesian_closed C] (a : Q ⟶ _) :
  N.recurse g h ❲a, N.zero❳ = g a :=
begin
  have : ❲a, N.zero❳ = limits.prod.map (𝟙 A) N.o ❲a, unit❳,
    rw [real_map_pair, id_apply], refl,
  rw [this, thing, N.recurse_zero, ← thing, right_unitor_hom],
end

lemma recurse_succ [cartesian_closed C] :
  limits.prod.map (𝟙 A) N.succ ≫ N.recurse g h = limits.prod.lift (𝟙 _) (N.recurse g h) ≫ h :=
begin
  dsimp [recurse],
  rw [← uncurry_natural_left, N.recurse'_succ, uncurry_natural_left, uncurry_curry, ← assoc],
  congr' 1,
  apply prod.hom_ext,
    rw [assoc, prod.lift_fst, prod.lift_fst],
    apply prod.hom_ext,
      rw [id_comp, assoc, prod.lift_fst, limits.prod.map_fst, comp_id],
    rw [id_comp, assoc, prod.lift_snd, limits.prod.map_snd_assoc, prod.lift_fst, comp_id],
  rw [prod.lift_snd, assoc, prod.lift_snd, ← prod_map_id_comp_assoc, prod.lift_snd, uncurry_eq],
end

lemma int_recurse_succ [cartesian_closed C] (a : Q ⟶ A) (n : Q ⟶ N.N):
  N.recurse g h ❲a, N.succ n❳ = h ❲❲a, n❳, N.recurse g h ❲a, n❳❳ :=
begin
  rw [map_pair, thing, recurse_succ, ← thing],
  congr' 1,
  apply prod.hom_ext; simp [expand_apply],
end

lemma recurse_uniq [cartesian_closed C] (q) :
  limits.prod.map (𝟙 A) N.o ≫ q = (prod.right_unitor _).hom ≫ g →
  limits.prod.map (𝟙 A) N.succ ≫ q = limits.prod.lift (𝟙 _) q ≫ h →
  q = N.recurse g h :=
begin
  intros q₁ q₂,
  change q = cartesian_closed.uncurry _,
  rw ← curry_eq_iff,
  apply recurse'_uniq,
  rw [← curry_natural_left, curry_eq_iff, internalize_hom, uncurry_curry, q₁], refl,
  rw [← curry_natural_left, q₂, ← curry_natural_left, ← assoc],
  congr' 2,
  apply prod.hom_ext,
    rw [assoc, prod.lift_fst, prod.lift_fst],
    apply prod.hom_ext,
      rw [id_comp, assoc, prod.lift_fst, limits.prod.map_fst, comp_id],
    rw [id_comp, assoc, prod.lift_snd, prod.map_snd_assoc, prod.lift_fst, comp_id],
  rw [prod.lift_snd, assoc, prod.lift_snd, ← prod_map_id_comp_assoc, prod.lift_snd, ← uncurry_eq,
      uncurry_curry],
end

lemma recurse_hom_ext [cartesian_closed C] (q₁ q₂ : A ⨯ N.N ⟶ B) :
  limits.prod.map (𝟙 A) N.o ≫ q₁ = limits.prod.map (𝟙 A) N.o ≫ q₂ →
  limits.prod.map (𝟙 A) N.succ ≫ q₁ = limits.prod.map (𝟙 A) N.succ ≫ q₂ →
  q₁ = q₂ :=
begin
  let h : A ⨯ N.N ⨯ B ⟶ B := limits.prod.fst ≫ limits.prod.map (𝟙 _) N.succ ≫ q₂,
  have hq : map (𝟙 A) N.o ≫ q₂ = (right_unitor A).hom ≫ limits.prod.lift (𝟙 A) N.zero ≫ q₂,
    rw ← assoc, congr' 1,
    apply prod.hom_ext,
      rw [assoc, limits.prod.map_fst, prod.lift_fst], refl,
    rw [assoc, prod.lift_snd, limits.prod.map_snd],
    change _ ≫ _ = _ ≫ _ ≫ _,
    rw ← assoc, congr' 1,
  have : q₂ = N.recurse (prod.lift (𝟙 _) N.zero ≫ q₂) h,
    apply N.recurse_uniq,
      apply hq,
    rw [prod.lift_fst_assoc, id_comp],
  intros h0 hsucc,
  rw this,
  apply N.recurse_uniq,
    rw [h0, hq],
  rw [hsucc, prod.lift_fst_assoc, id_comp],
end


lemma fst_pair {Q : C} (a : Q ⟶ A) (b : Q ⟶ B) : (fst : A ⨯ B ⟶ A) ❲a, b❳ = a :=
begin
  rw [expand_apply, prod.lift_fst],
end
lemma snd_pair {Q : C} (a : Q ⟶ A) (b : Q ⟶ B) : (snd : A ⨯ B ⟶ B) ❲a, b❳ = b :=
begin
  rw [expand_apply, prod.lift_snd],
end

lemma swap_pair {Q : C} (a : Q ⟶ A) (b : Q ⟶ B) : ((braiding _ _).hom : A ⨯ B ⟶ _) ❲a, b❳ = ❲b, a❳ :=
begin
  rw [expand_apply],
  apply prod.hom_ext; simp,
end

lemma test_pair {X Y Z : C} (f g : X ⨯ Y ⟶ Z) :
  (∀ Q (h : Q ⟶ _) k, f ❲h, k❳ = g ❲h, k❳) → f = g :=
begin
  intros h,
  simpa [pair_fst_snd] using h _ fst snd,
end


lemma int_curry_natural_left [cartesian_closed C] {B' : C} (g : A ⨯ B' ⟶ B) (q : Q ⟶ _) :
  cartesian_closed.curry g q = cartesian_closed.curry (g (map (𝟙 A) q)) :=
(curry_natural_left _ _).symm


lemma int_recurse_uniq [cartesian_closed C] (q : A ⨯ N.N ⟶ B) :
  (∀ Q (a : Q ⟶ _), q ❲a, N.zero❳ = g a)
→ (∀ Q (a : Q ⟶ _) n, q ❲a, N.succ n❳ = h ❲❲a, n❳, q ❲a, n❳❳)
→ q = N.recurse g h :=
begin
  intros q₁ q₂,
  apply recurse_uniq,
  { specialize q₁ _ (𝟙 _),
    rw [apply_id] at q₁,
    rw [← q₁, expand_apply, ← assoc],
    congr' 1,
    apply prod.hom_ext,
      rw [limits.prod.map_fst, assoc, prod.lift_fst], refl,
    rw [limits.prod.map_snd, assoc, prod.lift_snd],
    change _ ≫ _ = _ ≫ _ ≫ _,
    rw ← assoc,
    congr' 1 },
  { specialize q₂ (A ⨯ N.N) limits.prod.fst limits.prod.snd,
    rw [map_pair, pair_fst_snd, apply_id, apply_id] at q₂,
    apply q₂ }
end
end recursion

variable [cartesian_closed C]

def add : N.N ⨯ N.N ⟶ N.N :=
N.recurse (𝟙 _) (limits.prod.snd ≫ N.succ)

lemma add_zero (n : Q ⟶ N.N) : N.add ❲n, N.zero❳ = n :=
begin
  change N.recurse _ _ _ = _,
  rw [int_recurse_zero, expand_apply, comp_id],
end

lemma add_succ (n m : Q ⟶ N.N) : N.add ❲n, N.succ m❳ = N.succ (N.add ❲n, m❳) :=
begin
  change N.recurse _ _ _ = _,
  rw [int_recurse_succ],
  rw [← thing, expand_apply limits.prod.snd, prod.lift_snd],
  refl,
end


lemma kevin : N.add ❲N.two, N.two❳ = (N.four : Q ⟶ _) :=
begin
  rw [add_succ, add_succ, add_zero],
end

-- lemma induction (f g : N.N ⟶ A) (t : A ⟶ A) (P0 : ∀ Q, f (N.zero : Q ⟶ N.N) = g N.zero)
--   (Psucc : ∀ Q (n : Q ⟶ N.N), f n = g n → f (N.succ n) = g (N.succ n)) :
--   ∀ (n : Q ⟶ N.N), f n = g n :=
-- begin
--   suffices : f = g,
--   { intro n, rw this },
--   specialize P0 (⊤_ C),
--     rw [term_zero, expand_apply, expand_apply] at P0,
--   -- change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _ at P0,
--   -- rw [assoc, assoc] at P0,
--   rw N.uniq A (N.o ≫ g) t f P0 _,
--   apply (N.uniq A (N.o ≫ g) t g rfl _).symm,
-- end

-- ⇑(N.add) (⇑❲N.zero, 𝟙 N.N❳ N.zero)
-- ⇑(⇑(N.add) ❲N.zero, 𝟙 N.N❳) N.zero


lemma zero_add (n : Q ⟶ N.N) : N.add ❲N.zero, n❳ = n :=
begin
  have : ∀ Q (m : Q ⟶ N.N), ❲N.zero, m❳ = ❲N.zero, 𝟙 _❳ m,
    intros Q m,
    rw pair_apply,
    rw id_apply,
    rw zero_apply,
  rw [this, thing],
  suffices : N.add ❲N.zero, 𝟙 _❳ = 𝟙 N.N,
    have := n ≫= this,
    rw [comp_id] at this,
    exact this,
  apply hom_eq_id,
  intro Q,
  rw [← func_assoc, ← this, add_zero],
  intros Q n,
  rw [← func_assoc, ← this, ← func_assoc, ← this, add_succ],
end

lemma congr_element {f g : A ⟶ B} (x : Q ⟶ A) : f = g → f x = g x :=
begin
  rintro rfl, refl,
end

lemma add_three_one : N.add (limits.prod.map N.add (𝟙 _)) = N.recurse N.add (N.succ snd) :=
begin
  apply int_recurse_uniq,
    intros Q a,
    rw [← func_assoc, real_map_pair, id_apply, add_zero],
  intros Q a n,
  rw [← func_assoc, ← func_assoc, ← func_assoc, real_map_pair, real_map_pair, id_apply, id_apply,
      add_succ, snd_pair],
end

lemma add_three_two :
  ❲limits.prod.fst ≫ limits.prod.fst, limits.prod.map limits.prod.snd (𝟙 _) ≫ N.add❳ ≫ N.add = N.recurse N.add (N.succ snd) :=
begin
  apply int_recurse_uniq,
    intros Q a,
    rw [← thing, pair_apply, ← thing, fst_pair, ← thing, real_map_pair, id_apply, add_zero,
        ← pair_apply, pair_fst_snd, id_apply],
  intros Q a n,
  rw [← thing, ← thing, ← func_assoc, snd_pair, pair_apply, ← thing, fst_pair, ← thing,
      real_map_pair, id_apply, add_succ, add_succ, pair_apply, ← thing, fst_pair, ← thing,
      real_map_pair, id_apply],
end

lemma add_assoc (n m p : Q ⟶ N.N) : N.add ❲N.add ❲n, m❳, p❳ = N.add ❲n, N.add ❲m, p❳❳ :=
begin
  suffices : limits.prod.map N.add (𝟙 _) ≫ N.add = ❲limits.prod.fst ≫ limits.prod.fst, limits.prod.map limits.prod.snd (𝟙 _) ≫ N.add❳ ≫ N.add,
    have := congr_element ❲❲n, m❳, p❳ this,
    rw [← thing, real_map_pair, id_apply] at this,
    rw this,
    rw [← thing, pair_apply, ← thing, fst_pair, fst_pair, ← thing, real_map_pair, snd_pair,
        id_apply],
  rw ← expand_apply,
  rw add_three_one,
  rw ← add_three_two,
end

lemma succ_eq_add_one (n : Q ⟶ N.N) : N.succ n = N.add ❲n, N.one❳ :=
begin
  rw [add_succ, add_zero],
end

lemma succ_add (n m : Q ⟶ N.N) : N.add ❲N.succ n, m❳ = N.succ (N.add ❲n, m❳) :=
begin
  suffices : N.add (limits.prod.map (N.succ) (𝟙 _)) = N.succ N.add,
  { have := congr_element ❲n, m❳ this,
    rwa [← func_assoc, ← func_assoc, real_map_pair, id_apply] at this },
  { have : N.succ N.add = N.recurse N.succ (N.succ snd),
      apply N.int_recurse_uniq,
      { intros Q a,
        rw [← func_assoc, add_zero] },
      { intros Q a n,
        rw [← func_assoc, ← func_assoc, ← func_assoc, add_succ, snd_pair] },
    rw this,
    apply N.int_recurse_uniq,
    { intros Q a,
      rw [← func_assoc, real_map_pair, id_apply, add_zero] },
    { intros Q a n,
      rw [← func_assoc, ← func_assoc, ← func_assoc, real_map_pair, real_map_pair, id_apply,
          add_succ, snd_pair, id_apply] } }
end

lemma add_comm (n m : Q ⟶ N.N) : N.add ❲n, m❳ = N.add ❲m, n❳ :=
begin
  suffices : N.add (limits.prod.braiding _ _).hom = N.add,
    conv_lhs {rw ← this},
    rw [← func_assoc, swap_pair],
  apply N.int_recurse_uniq,
  { intros Q m,
    rw [id_apply, ← func_assoc, swap_pair, zero_add] },
  { intros Q a m,
    rw [← func_assoc, swap_pair, succ_add, ← func_assoc, swap_pair, ← thing, snd_pair] }
end

lemma add_right_comm (n m p : Q ⟶ N.N) : N.add ❲N.add ❲n, m❳, p❳ = N.add ❲N.add ❲n, p❳, m❳ :=
begin
  rw [add_assoc, N.add_comm m p, add_assoc],
end

section multiplication

def mult : N.N ⨯ N.N ⟶ N.N := N.recurse N.zero (N.add ❲snd, fst ≫ fst❳)
lemma mul_zero (n : Q ⟶ N.N) : N.mult ❲n, N.zero❳ = N.zero :=
by rw [mult, N.int_recurse_zero, zero_apply]
lemma mul_succ (n m : Q ⟶ N.N) : N.mult ❲n, N.succ m❳ = N.add ❲N.mult ❲n, m❳, n❳ :=
by rw [mult, N.int_recurse_succ, ← func_assoc, pair_apply, snd_pair, ← thing, fst_pair, fst_pair]

lemma zero_mul (n : Q ⟶ N.N) : N.mult ❲N.zero, n❳ = N.zero :=
begin
  suffices : N.mult ❲N.zero, 𝟙 _❳ = N.zero,
    simpa only [← func_assoc, pair_apply, id_apply, zero_apply] using congr_element n this,
  have : N.mult ❲N.zero, 𝟙 N.N❳ = N.recurse' N.zero snd,
    apply N.int_recurse'_uniq,
    simp only [← func_assoc, pair_apply, zero_apply, id_apply, mul_zero],
    intros Q n,
    simp only [← func_assoc, pair_apply, zero_apply, id_apply, add_zero, mul_succ, snd_pair],
  rw this,
  symmetry,
  apply N.int_recurse'_uniq,
  rw zero_apply,
  intros Q n,
  rw [zero_apply, snd_pair, zero_apply],
end

lemma mul_one (n : Q ⟶ N.N) : N.mult ❲n, N.one❳ = n :=
begin
  rw [mul_succ, mul_zero, zero_add],
end
lemma one_mul (n : Q ⟶ N.N) : N.mult ❲N.one, n❳ = n :=
begin
  suffices : N.mult ❲N.one, 𝟙 _❳ = 𝟙 N.N,
    have := congr_element n this,
    rw [← func_assoc, pair_apply, id_apply, one_apply] at this,
    assumption,
  apply hom_eq_id,
  intro Q,
  rw [← func_assoc, pair_apply, id_apply, mul_zero],
  intros Q n,
  rw [← func_assoc, ← func_assoc, pair_apply, pair_apply, id_apply, id_apply, mul_succ,
      one_apply, one_apply, succ_eq_add_one],
end

lemma mul_add (t a b : Q ⟶ N.N) : N.mult ❲t, N.add ❲a, b❳❳ = N.add ❲N.mult ❲t, a❳, N.mult ❲t, b❳❳ :=
begin
  suffices : N.mult ❲fst ≫ fst, N.add ❲fst ≫ snd, snd❳❳ = N.add ❲N.mult ❲fst ≫ fst, fst ≫ snd❳, N.mult ❲fst ≫ fst, snd❳❳,
    simpa only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair] using congr_element ❲❲t, a❳, b❳ this,
  have : N.mult ❲fst ≫ fst, N.add ❲fst ≫ snd, snd❳❳ = N.recurse N.mult (N.add ❲snd, fst ≫ fst ≫ fst❳),
    apply N.int_recurse_uniq,
      intros Q a,
      simp only [← func_assoc, pair_apply, mul_zero, snd_pair, ← thing, fst_pair, add_zero],
      rw [← pair_apply, pair_fst_snd, id_apply],
    intros Q a n,
    simp only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair, add_succ, mul_succ],
  rw this,
  symmetry,
  apply N.int_recurse_uniq,
  { intros Q a,
    simp only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair, mul_zero, add_zero],
    rw [← pair_apply, pair_fst_snd, id_apply] },
  { intros Q a n,
    simp only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair, mul_zero, add_zero,
               mul_succ, add_assoc] }
end
lemma mul_assoc (a b c : Q ⟶ N.N) : N.mult ❲N.mult ❲a, b❳, c❳ = N.mult ❲a, N.mult ❲b, c❳❳ :=
begin
  suffices : N.mult ❲N.mult ❲fst ≫ fst, fst ≫ snd❳, snd❳ = N.mult ❲fst ≫ fst, N.mult ❲fst ≫ snd, snd❳❳,
    simpa only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair] using congr_element ❲❲a, b❳, c❳ this,
  have : N.mult ❲fst ≫ fst, N.mult ❲fst ≫ snd, snd❳❳ = N.recurse N.zero (N.add ❲snd, N.mult (fst ≫ fst)❳),
    apply N.int_recurse_uniq,
      intros Q a,
      simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, mul_succ, pair_ext,
                 zero_apply, mul_zero],
    intros Q a n,
    simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, mul_succ, pair_ext, mul_add],
  rw this,
  apply N.int_recurse_uniq,
  intros Q a,
  simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, mul_succ, pair_ext, zero_apply,
             mul_zero],
  intros Q a n,
  simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, mul_succ, pair_ext],
end
lemma succ_mul (a b : Q ⟶ N.N) : N.mult ❲N.succ a, b❳ = N.add ❲N.mult ❲a, b❳, b❳ :=
begin
  suffices : N.mult ❲N.succ fst, snd❳ = N.add ❲N.mult (𝟙 _), snd❳,
    simpa only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair, id_apply] using congr_element ❲a, b❳ this,
  have : N.add ❲N.mult (𝟙 _), snd❳ = N.recurse N.zero (N.succ (N.add ❲snd, fst ≫ fst❳)),
    apply N.int_recurse_uniq,
    { intros Q a,
      simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, pair_ext,
                 zero_apply, mul_zero, id_apply, add_zero] },
    { intros Q a n,
      simp only [← func_assoc, pair_apply, snd_pair, fst_pair, mul_succ, add_succ, ← thing,
                 id_apply, add_right_comm] },
  rw this,
  apply N.int_recurse_uniq,
  { intros Q a,
    simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, pair_ext,
                zero_apply, mul_zero, id_apply, add_zero] },
  { intros Q a n,
    simp only [← func_assoc, pair_apply, snd_pair, fst_pair, mul_succ, add_succ, ← thing] }
end

instance {Q : C} : has_add (Q ⟶ N.N) := ⟨λ f g, N.add ❲f, g❳⟩
instance {Q : C} : has_mul (Q ⟶ N.N) := ⟨λ f g, N.mult ❲f, g❳⟩

lemma add_mul (a b t : Q ⟶ N.N) : N.mult ❲a + b, t❳ = N.add ❲N.mult ❲a, t❳, N.mult ❲b, t❳❳ :=
begin
  suffices : N.mult ❲N.add fst, snd❳ = N.add ❲N.mult ❲fst ≫ fst, snd❳, N.mult ❲fst ≫ snd, snd❳❳,
    simpa only [← func_assoc, pair_apply, ← thing, fst_pair, snd_pair, id_apply] using congr_element ❲❲a, b❳, t❳ this,
  have : N.mult ❲N.add fst, snd❳ = N.recurse N.zero (N.add ❲snd, N.add (fst ≫ fst)❳),
  { apply N.int_recurse_uniq,
    { intros Q a,
      simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, pair_ext,
                 zero_apply, mul_zero, id_apply, add_zero] },
    { intros Q a n,
      simp only [← func_assoc, pair_apply, fst_pair, snd_pair, mul_succ, ← thing] } },
  rw this,
  symmetry,
  apply N.int_recurse_uniq,
  { intros Q a,
    simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, pair_ext,
                zero_apply, mul_zero, id_apply, add_zero] },
  { intros Q a n,
    simp only [← func_assoc, pair_apply, fst_pair, snd_pair, ← thing, mul_succ, add_assoc],
    congr' 2,
    rw [← add_assoc, add_right_comm, pair_ext, add_comm] }
end

lemma mul_comm (n m : Q ⟶ N.N) : N.mult ❲n, m❳ = N.mult ❲m, n❳ :=
begin
  suffices : N.mult (limits.prod.braiding _ _).hom = N.mult,
    simpa only [← func_assoc, swap_pair] using congr_element ❲m, n❳ this,
  apply N.int_recurse_uniq,
  { intros Q m,
    rw [← func_assoc, swap_pair, zero_mul, zero_apply] },
  { intros Q a m,
    simp only [← func_assoc, swap_pair, succ_mul, pair_apply, snd_pair, ← thing, fst_pair] }
end

lemma mul_right_comm (n m p : Q ⟶ N.N) : N.mult ❲N.mult ❲n, m❳, p❳ = N.mult ❲N.mult ❲n, p❳, m❳ :=
begin
  rw [mul_assoc, N.mul_comm m p, mul_assoc],
end

instance : comm_semiring (Q ⟶ N.N) :=
{ add := (+),
  add_assoc := λ a b c, N.add_assoc a b c,
  zero := N.zero,
  zero_add := λ a, N.zero_add a,
  add_zero := λ a, N.add_zero a,
  add_comm := λ a b, N.add_comm a b,
  mul := (*),
  mul_assoc := λ a b c, N.mul_assoc a b c,
  one := N.one,
  one_mul := λ a, N.one_mul a,
  mul_one := λ a, N.mul_one a,
  zero_mul := λ a, N.zero_mul a,
  mul_zero := λ a, N.mul_zero a,
  left_distrib := λ a b c, N.mul_add a b c,
  right_distrib := λ a b c, N.add_mul a b c,
  mul_comm := λ a b, N.mul_comm a b }

end multiplication

section exponentiation

def pow : N.N ⨯ N.N ⟶ N.N := N.recurse N.one (N.mult ❲snd, fst ≫ fst❳)

instance : has_pow (Q ⟶ N.N) (Q ⟶ N.N) := ⟨λ a b, N.pow ❲a, b❳⟩

lemma pow_zero (a : Q ⟶ N.N) : N.pow ❲a, N.zero❳ = N.one :=
begin
  rw [pow, N.int_recurse_zero, one_apply],
end
lemma pow_succ (a b : Q ⟶ N.N) : N.pow ❲a, N.succ b❳ = N.mult ❲N.pow ❲a, b❳, a❳ :=
begin
  rw [pow, N.int_recurse_succ, ← pow, ← func_assoc, pair_apply, snd_pair, ← thing, fst_pair, fst_pair],
end

lemma zero_pow_zero : N.pow ❲N.zero, N.zero❳ = (N.one : Q ⟶ _) :=
begin
  rw pow_zero,
end
lemma zero_pow_succ (m : Q ⟶ N.N) : N.pow ❲N.zero, N.succ m❳ = N.zero :=
begin
  rw [pow_succ, mul_zero],
end

lemma pow_one (a : Q ⟶ N.N) : N.pow ❲a, N.one❳ = a :=
begin
  rw [N.pow_succ, pow_zero, one_mul],
end

lemma one_pow (a : Q ⟶ N.N) : N.pow ❲N.one, a❳ = N.one :=
begin
  suffices : N.pow ❲N.one, 𝟙 _❳ = N.one,
    simpa only [← func_assoc, pair_apply, one_apply, id_apply] using congr_element a this,
  have : N.pow ❲N.one, 𝟙 N.N❳ = N.recurse' N.one snd,
    apply N.int_recurse'_uniq,
    rw [← func_assoc, pair_apply, one_apply, id_apply, pow_zero],
    intros Q n,
    simp only [snd_pair, ← func_assoc, pair_apply, zero_apply, id_apply, pow_succ, mul_one],
  rw this,
  symmetry,
  apply N.int_recurse'_uniq,
  rw one_apply,
  intros Q n,
  rw [snd_pair, one_apply, one_apply],
end

lemma pow_two_eq_mul (n : Q ⟶ N.N) : N.pow ❲n, N.two❳ = N.mult ❲n, n❳ :=
begin
  rw [pow_succ, pow_one],
end


lemma add_square (a b : Q ⟶ N.N) : N.pow ❲a + b, N.two❳ = N.pow ❲a, N.two❳ + 2 * a * b + N.pow ❲b, N.two❳ :=
begin
  rw [pow_two_eq_mul, pow_two_eq_mul, pow_two_eq_mul],
  change (a + b) * (a + b) = a * a + 2 * a * b + b * b,
  ring,
end

-- pow_add
--   (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n
-- mul_pow
--   (a b n : mynat) : (a * b) ^ n = a ^ n * b ^ n
-- pow_pow
--   (a m n : mynat) : (a ^ m) ^ n = a ^ (m * n)

end exponentiation

def pred : N.N ⟶ N.N := N.recurse' N.o fst
lemma pred_zero' : N.pred N.zero = N.o :=
N.int_recurse'_zero _ _
lemma pred_zero : N.pred (N.zero : Q ⟶ N.N) = N.zero :=
begin
  change N.pred (N.o unit) = N.o unit,
  rw [func_assoc, ← term_zero, pred_zero'],
  simp,
end
lemma pred_succ (n : Q ⟶ N.N) : N.pred (N.succ n) = n :=
begin
  change N.recurse' _ _ _ = _,
  rw int_recurse'_succ,
  rw fst_pair,
end

instance : split_mono N.succ := ⟨N.pred, by simpa using N.pred_succ (𝟙 _)⟩

def sub : N.N ⨯ N.N ⟶ N.N := N.recurse (𝟙 _) (snd ≫ N.pred)
lemma sub_zero (n : Q ⟶ N.N) : N.sub ❲n, N.zero❳ = n :=
begin
  rw [sub, N.int_recurse_zero, id_apply],
end
lemma sub_succ (n m : Q ⟶ N.N) : N.sub ❲n, N.succ m❳ = N.pred (N.sub ❲n, m❳) :=
begin
  rw [sub, N.int_recurse_succ, ← sub, ← thing, snd_pair],
end

def coprod_cofan : is_colimit (binary_cofan.mk N.o N.succ) :=
{ desc := λ s, N.lift (N.N ⨯ s.X) ❲N.o, binary_cofan.inl s❳ (❲N.succ, binary_cofan.inr s❳ fst) ≫ snd,
  fac' := λ s j,
  begin
    cases j,
      change N.o ≫ N.lift _ _ _ ≫ _ = _,
      rw [N.fac₁_assoc, prod.lift_snd],
    change N.succ ≫ _ ≫ _ = binary_cofan.inr s,
    rw [N.fac₂_assoc, expand_apply, assoc, prod.lift_snd, ← assoc],
    convert id_comp _,
    apply eq_id_of_comm_zero_succ,
      rw [N.fac₁_assoc, prod.lift_fst],
    rw [N.fac₂_assoc, assoc, prod.lift_fst, assoc],
  end,
  uniq' := λ s m j,
  begin
    have := N.uniq (N.N ⨯ s.X) ❲N.o, binary_cofan.inl s❳ (❲N.succ, binary_cofan.inr s❳ fst) ❲𝟙 _, m❳ _ _,
      rw [← this, prod.lift_snd],
    apply prod.hom_ext,
      rw [assoc, prod.lift_fst, comp_id, prod.lift_fst],
    rw [assoc, prod.lift_snd, prod.lift_snd], apply j walking_pair.left,
    rw [expand_apply, prod.lift_fst_assoc, id_comp],
    apply prod.hom_ext,
      rw [assoc, prod.lift_fst, comp_id, prod.lift_fst],
    rw [prod.lift_snd, assoc, prod.lift_snd],
    apply j walking_pair.right,
  end }

instance : split_epi (terminal.from N.N) :=
{ section_ := N.o }

def coeq_cofork : is_colimit (cofork.of_π (terminal.from N.N) (by tidy) : cofork (𝟙 N.N) N.succ) :=
cofork.is_colimit.mk' _ $
begin
  intro s,
  have : N.succ ≫ s.π = s.π,
    rw [← s.condition, id_comp],
  have : s.π = N.lift s.X (N.o ≫ s.π) (𝟙 _),
    apply N.uniq _ _ _ _ rfl (by rw [this, comp_id]),
  have : s.π = terminal.from N.N ≫ N.o ≫ s.π,
    apply this.trans (eq.symm _),
    apply N.uniq _ _,
    rw reassoc_of (subsingleton.elim (N.o ≫ terminal.from N.N) (𝟙 _)),
    rw [reassoc_of (subsingleton.elim (N.succ ≫ terminal.from N.N) (terminal.from N.N)), comp_id],
  refine ⟨N.o ≫ s.π, ‹_ = _›.symm, _⟩,
  intros m w,
  rw ← cancel_epi (terminal.from N.N),
  erw w,
  assumption,
end

/-- Transfer a natural numbers object across a left adjoint functor. -/
-- Note this is alternatively doable if F is cocartesian and D is a topos
def functor.map_nno (F : C ⥤ D) [is_left_adjoint F] [preserves_limits_of_shape (discrete pempty) F]
  [has_finite_products D] :
  natural_number_object D :=
{ N := F.obj N.N,
  o := (terminal_iso _ F).hom ≫ F.map N.o,
  succ := F.map N.succ,
  lift := λ A a t,
  begin
    apply ((adjunction.of_left_adjoint F).hom_equiv _ _).symm _,
    haveI := adjunction.right_adjoint_preserves_limits (adjunction.of_left_adjoint F),
    apply N.lift _ ((terminal_iso _ (right_adjoint F)).hom ≫ (right_adjoint F).map a) ((right_adjoint F).map t),
  end,
  fac₁ := λ A a t,
  begin
    rw [assoc, ← adjunction.hom_equiv_naturality_left_symm, N.fac₁,
        adjunction.hom_equiv_naturality_right_symm, ← assoc],
    convert id_comp _,
  end,
  fac₂ := λ A a t,
  begin
    rw [← adjunction.hom_equiv_naturality_left_symm, N.fac₂, adjunction.hom_equiv_naturality_right_symm],
  end,
  uniq := λ A a t f f₁ f₂,
  begin
    rw ← adjunction.hom_equiv_apply_eq,
    apply N.uniq,
      rw [← adjunction.hom_equiv_naturality_left, ← f₁, adjunction.hom_equiv_apply_eq,
          adjunction.hom_equiv_naturality_right_symm, assoc, ← assoc],
      convert (id_comp _).symm,
      rw iso.comp_hom_eq_id,
      refine subsingleton.elim _ _,
    rw [← adjunction.hom_equiv_naturality_right, ← adjunction.hom_equiv_naturality_left, f₂],
  end }

-- n - n = 0
-- (n+1) - (n+1) = pred ((n + 1) - n) = 0

-- @[simp] lemma succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
-- nat.rec_on b
--   (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
--   (λ b, congr_arg pred)

lemma succ_sub_succ_eq_sub (n m : Q ⟶ N.N) : N.sub ❲N.succ n, N.succ m❳ = N.sub ❲n, m❳ :=
begin
  suffices : N.sub ❲N.succ fst, N.succ snd❳ = N.sub,
    simpa only [← func_assoc, pair_apply, snd_pair, fst_pair] using congr_element ❲n, m❳ this,
  apply N.int_recurse_uniq,
    intros Q n,
    rw [← func_assoc, pair_apply, ← func_assoc, ← func_assoc, fst_pair, snd_pair, sub_succ,
        sub_zero, pred_succ, id_apply],
  intros Q a n,
  rw [← func_assoc, ← thing, pair_apply, ← func_assoc, fst_pair, ← func_assoc, snd_pair, sub_succ,
      snd_pair, ← func_assoc, pair_apply, ← func_assoc, fst_pair, ← func_assoc, snd_pair],
end
lemma sub_self (n : Q ⟶ N.N) : N.sub ❲n, n❳ = N.zero :=
begin
  suffices : N.sub ❲𝟙 _, 𝟙 _❳ = N.zero,
    simpa only [← func_assoc, pair_apply, id_apply, zero_apply] using congr_element n this,
  have : N.sub ❲𝟙 _, 𝟙 _❳ = N.recurse' N.zero snd,
    apply N.int_recurse'_uniq,
      rw [← func_assoc, pair_apply, id_apply, sub_zero],
    intros Q n,
      rw [← func_assoc, pair_apply, id_apply, succ_sub_succ_eq_sub, snd_pair, ← func_assoc,
          pair_apply, id_apply],
  rw this,
  symmetry,
  apply N.int_recurse'_uniq,
  rw zero_apply,
  intros Q n,
  rw [snd_pair, zero_apply, zero_apply],
end

end natural_number_object
end category_theory