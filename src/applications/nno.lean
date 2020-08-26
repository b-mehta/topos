import category_theory.closed.cartesian

universes v u

namespace category_theory
open category limits limits.prod

variables (C : Type u) [category.{v} C]
variables [has_finite_products C] [cartesian_closed C]

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

variables (N : natural_number_object C) {Q A B : C}

-- lemma hom_ext (f g : N.N ⟶ A) (hf₁ : N.o ≫ f = N.o ≫ g) (hf₂ : N.succ ≫ f = N.succ ≫ g) : f = g :=
-- begin

-- end

lemma eq_id_of_comm_zero_succ (f : N.N ⟶ N.N) (hf₁ : N.o ≫ f = N.o) (hf₂ : N.succ ≫ f = f ≫ N.succ) :
  f = 𝟙 _ :=
by rw [N.uniq _ N.o N.succ f hf₁ hf₂, N.uniq _ N.o N.succ (𝟙 _) (comp_id _) (by simp)]

variable {C}
def unit : Q ⟶ ⊤_ C := terminal.from Q
def apply {A B} (f : A ⟶ B) (h : Q ⟶ A) : Q ⟶ B := h ≫ f
instance {A B : C} : has_coe_to_fun (A ⟶ B) :=
{ F := λ f, Π {Q}, (Q ⟶ A) → (Q ⟶ B),
  coe := λ f Q h, h ≫ f }
abbreviation zero : Q ⟶ N.N := N.o unit

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

end

/-- Define a function with parameters by primitive recursion. -/
def recurse (g : A ⟶ B) (h : A ⨯ N.N ⨯ B ⟶ B) : A ⨯ N.N ⟶ B :=
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
lemma recurse_zero :
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

lemma int_recurse_zero (a : Q ⟶ _) :
  N.recurse g h ❲a, N.zero❳ = g a :=
begin
  have : ❲a, N.zero❳ = limits.prod.map (𝟙 A) N.o ❲a, unit❳,
  { rw ← map_pair },
  rw [this, thing, N.recurse_zero, ← thing, right_unitor_hom],
end

lemma recurse_succ :
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

lemma int_recurse_succ (a : Q ⟶ A) (n : Q ⟶ N.N):
  N.recurse g h ❲a, N.succ n❳ = h ❲❲a, n❳, N.recurse g h ❲a, n❳❳ :=
begin
  rw [map_pair, thing, recurse_succ, ← thing],
  congr' 1,
  apply prod.hom_ext; simp [expand_apply],
end

lemma recurse_uniq (q) :
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

lemma recurse_hom_ext (q₁ q₂ : A ⨯ N.N ⟶ B) :
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


lemma pair_fst_snd : ❲fst, snd❳ = 𝟙 (A ⨯ B) :=
begin
  apply prod.hom_ext; simp,
end

lemma fst_pair {Q : C} (a : Q ⟶ A) (b : Q ⟶ B) : (fst : A ⨯ B ⟶ A) ❲a, b❳ = a :=
begin
  rw [expand_apply, prod.lift_fst],
end
lemma snd_pair {Q : C} (a : Q ⟶ A) (b : Q ⟶ B) : (snd : A ⨯ B ⟶ B) ❲a, b❳ = b :=
begin
  rw [expand_apply, prod.lift_snd],
end

lemma test_pair {X Y Z : C} (f g : X ⨯ Y ⟶ Z) :
  (∀ Q (h : Q ⟶ _) k, f ❲h, k❳ = g ❲h, k❳) → f = g :=
begin
  intros h,
  simpa [pair_fst_snd] using h _ fst snd,
end


lemma int_curry_natural_left {B' : C} (g : A ⨯ B' ⟶ B) (q : Q ⟶ _) :
  cartesian_closed.curry g q = cartesian_closed.curry (g (map (𝟙 A) q)) :=
(curry_natural_left _ _).symm


lemma int_recurse_uniq (q : A ⨯ N.N ⟶ B) :
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

lemma func_assoc {W X Y Z : C} (x : X ⟶ Y) (g : Y ⟶ W) (f : W ⟶ Z) : f (g x) = (f g) x :=
begin
  apply assoc,
end


lemma pair_apply {B' : C} (x : Q ⟶ B') (g h) : (❲g, h❳ : B' ⟶ A ⨯ B) x = ❲g x, h x❳ :=
begin
  rw [expand_apply],
  apply prod.hom_ext,
    rw [assoc, prod.lift_fst, prod.lift_fst, expand_apply],
  rw [assoc, prod.lift_snd, prod.lift_snd, expand_apply],
end

lemma id_apply (x : Q ⟶ A) : (𝟙 A : _ ⟶ _) x = x :=
comp_id _

lemma int_recurse_hom_ext (q₁ q₂ : A ⨯ N.N ⟶ B) :
  (∀ Q (a : Q ⟶ A), q₁ ❲a, N.zero❳ = q₂ ❲a, N.zero❳) →
  (∀ Q (a : Q ⟶ A) (n : Q ⟶ N.N), q₁ ❲a, n❳ = q₂ ❲a, n❳ → q₁ ❲a, N.succ n❳ = q₂ ❲a, N.succ n❳) →
  q₁ = q₂ :=
begin
  intros h0 hsucc,
  let g := q₂ ❲𝟙 _, N.zero❳,
  let h : A ⨯ N.N ⨯ B ⟶ B := limits.prod.fst ≫ limits.prod.map (𝟙 _) N.succ ≫ q₂,
  have : map (𝟙 A) N.o ≫ q₂ = (right_unitor A).hom ≫ g,
    change _ ≫ _ = _ ≫ _ ≫ _,
    rw ← assoc,
    congr' 1,
    apply prod.hom_ext,
      rw [limits.prod.map_fst, assoc, prod.lift_fst], refl,
    rw [limits.prod.map_snd, assoc, prod.lift_snd],
    change _ = _ ≫ _ ≫ _,
    rw ← assoc,
    congr' 1,
  have : map (𝟙 A) N.succ ≫ q₂ = limits.prod.lift (𝟙 (A ⨯ N.N)) q₂ ≫ h,
    rw [prod.lift_fst_assoc, id_comp],
  have := N.recurse_uniq g h q₂ ‹_› ‹_›,
  rw this,
  apply N.recurse_uniq g h q₁ _ _,
  { rw ← ‹_ = _›,
    sorry, },
  { apply test_pair,
    intros Q a n,
    rw [← thing, real_map_pair, id_apply, ← thing, pair_apply, id_apply],
    sorry
  }

  -- rw N.int_recurse_uniq g h q₂,
  -- apply N.int_recurse_uniq g h q₁,
  -- { intros Q a,
  --   rw h0,
  --   change _ = (q₂ _) _,
  --   rw [← func_assoc],
  --   congr' 1,
  --   rw [expand_apply],
  --   apply prod.hom_ext,
  --     simp,
  --   rw [prod.lift_snd, assoc, prod.lift_snd],
  --   change _ ≫ _ = _ ≫ _ ≫ _,
  --   rw ← assoc, congr' 1 },
  -- { intros Q a n,
  --   change _ = (fst ≫ map (𝟙 A) N.succ ≫ q₂) ❲❲a, n❳, q₁ ❲a, n❳❳,
  --   rw [← thing, fst_pair, ← thing, ← map_pair],
  --   apply hsucc,

  --    },
  -- { intros Q a,
  --   change _ = (q₂ _) _,
  --   rw [← func_assoc],
  --   congr' 1,
  --   rw [expand_apply],
  --   apply prod.hom_ext,
  --     simp,
  --   rw [prod.lift_snd, assoc, prod.lift_snd],
  --   change _ ≫ _ = _ ≫ _ ≫ _,
  --   rw ← assoc, congr' 1 },
  -- { intros Q a n,
  --   change _ = (fst ≫ map (𝟙 A) N.succ ≫ q₂) ❲❲a, n❳, q₂ ❲a, n❳❳,
  --   rw [← thing, ← thing, fst_pair, ← map_pair] },
end

end recursion

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

@[reducible] def two : Q ⟶ N.N := N.succ N.one
@[reducible] def three : Q ⟶ N.N := N.succ N.two
@[reducible] def four : Q ⟶ N.N := N.succ N.three

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



lemma zero_apply (x : Q ⟶ A) : N.zero x = N.zero :=
begin
  change _ ≫ _ ≫ _ = _ ≫ _,
  rw ← assoc, congr' 1,
end

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

lemma add_assoc (n m p : Q ⟶ N.N) : N.add ❲N.add ❲n, m❳, p❳ = N.add ❲n, N.add ❲m, p❳❳ :=
begin
  -- rw [expand_apply, expand_apply, expand_apply, expand_apply],
  suffices : limits.prod.map N.add (𝟙 _) ≫ N.add = ❲limits.prod.fst ≫ limits.prod.fst, limits.prod.map limits.prod.snd (𝟙 _) ≫ N.add❳ ≫ N.add,
    have := congr_element ❲❲n, m❳, p❳ this,
    rw [← thing, real_map_pair, id_apply] at this,
    rw this,
    rw [← thing, pair_apply, ← thing, fst_pair, fst_pair, ← thing, real_map_pair, snd_pair,
        id_apply],
  sorry
  -- apply int_recurse_hom_ext,
  --   intros Q mn,
  --   rw [← thing, real_map_pair, id_apply, add_zero, ← thing, pair_apply, ← thing, fst_pair,
  --       ← thing, real_map_pair, id_apply, add_zero, ← pair_apply, pair_fst_snd, id_apply],
  -- intros Q mn p,


end

end natural_number_object
end category_theory