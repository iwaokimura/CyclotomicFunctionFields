/-
# Additive Polynomials

This file develops the theory of additive polynomials over finite fields:
- IsAdditive: Predicate for P(x+y) = P(x) + P(y)
- frobeniusPower n: The polynomial x^(q^n)
- Structure theorem: Every additive polynomial is Σ aᵢ x^(qⁱ)

Reference: Hayes (1974), Section 1; Goss (1996), Chapter 1
-/

import CyclotomicFunctionFields.Prelude
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.RingTheory.Polynomial.Basic


namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact q.Prime]

/-- A polynomial P is additive if P(x+y) = P(x) + P(y) for all x, y -/
def IsAdditive.{u} (P : Polynomial (Fq q)) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra (Fq q) K] (x y : K),
    Polynomial.aeval x P + Polynomial.aeval y P = Polynomial.aeval (x + y) P

/-- The n-th Frobenius power polynomial x^(q^n) -/
noncomputable def frobeniusPower (n : ℕ) : Polynomial (Fq q) :=
  Polynomial.monomial (q ^ n) 1

namespace IsAdditive

/-- The sum of two additive polynomials is additive -/
theorem add.{u} {P Q : Polynomial (Fq q)} (hP : IsAdditive.{u} P) (hQ : IsAdditive.{u} Q) :
  IsAdditive.{u} (P + Q) := fun K _ _ x y => by
  /-
  (P + Q)(x + y) = P(x + y) + Q(x + y)
               = (P(x) + P(y)) + (Q(x) + Q(y))
               = (P(x) + Q(x)) + (P(y) + Q(y))
               = (P + Q)(x) + (P + Q)(y)
  -/
  calc Polynomial.aeval x (P + Q) + Polynomial.aeval y (P + Q)
      = Polynomial.aeval x P + Polynomial.aeval x Q
        + (Polynomial.aeval y P + Polynomial.aeval y Q) := by simp only [map_add]
    _ = (Polynomial.aeval x P + Polynomial.aeval y P)
        + (Polynomial.aeval x Q + Polynomial.aeval y Q) := by ring
    _ = Polynomial.aeval (x + y) P + Polynomial.aeval (x + y) Q := by
      conv_lhs =>
        arg 1
        rw [hP (K := K) x y]
      conv_lhs =>
        arg 2
        rw [hQ (K := K) x y]
    _ = Polynomial.aeval (x + y) (P + Q) := by rw [← map_add]

/-- Scalar multiplication preserves additivity -/
theorem smul.{u} {P : Polynomial (Fq q)} (hP : IsAdditive.{u} P) (a : Fq q) :
  IsAdditive.{u} (a • P) := fun K _ _ x y => by
  show Polynomial.aeval x (a • P) + Polynomial.aeval y (a • P) = Polynomial.aeval (x + y) (a • P)
  simp only [map_smul]
  rw [← smul_add, hP (K := K) x y]

/-- Composition of additive polynomials is additive -/
theorem comp.{u} {P Q : Polynomial (Fq q)} (hP : IsAdditive.{u} P) (hQ : IsAdditive.{u} Q) :
  IsAdditive.{u} (P.comp Q) := fun K _ _ x y => by
  simp only [Polynomial.aeval_comp]
  rw [← hQ (K := K) x y, ← hP (K := K) (Polynomial.aeval x Q) (Polynomial.aeval y Q)]

/-- Frobenius power polynomials are additive -/
theorem frobeniusPower_isAdditive.{u} (n : ℕ) : IsAdditive.{u} (frobeniusPower (q := q) n) := by
  intro K _ _ x y
  classical
  haveI : CharP K q :=
    charP_of_injective_algebraMap (algebraMap (Fq q) K).injective q
  simpa [frobeniusPower, Polynomial.aeval_monomial, map_one, one_mul]
    using
      (add_pow_char_pow (R := K) (p := q) (x := x) (y := y) (n := n)).symm

/--
lemma: The constant of an additive polynomial is zero.
If P is additive, then the constant term of P is 0.
-/
theorem constant_term_zero {P : Polynomial (Fq q)} (hP : IsAdditive.{0} P) :
  P.coeff 0 = 0 := by
  classical
  -- Evaluate additivity at x = y = 0 over the base field itself.
  have h := hP (K := Fq q) (x := 0) (y := 0)
  simpa [Polynomial.aeval_def, Polynomial.eval₂_at_zero, map_zero, zero_add] using h

/-- For a prime p, if p^j ≤ n < p^(j+1), then n.choose(p^j) ≡ n/p^j in ZMod p.  -/
private theorem choose_prime_pow_cast_eq_div {p : ℕ} [hp : Fact p.Prime]
    (j n : ℕ) (hlo : p ^ j ≤ n) (hhi : n < p ^ (j + 1)) :
    (n.choose (p ^ j) : ZMod p) = ((n / p ^ j : ℕ) : ZMod p) := by
  induction j generalizing n with
  | zero => simp [Nat.choose_one_right]
  | succ j ih =>
    -- Recurrence: n.choose(p^(j+1)) ≡ (n/p).choose(p^j) [MOD p]
    -- because p^(j+1) % p = 0 and p^(j+1) / p = p^j
    have h_step : n.choose (p ^ (j + 1)) ≡ (n / p).choose (p ^ j) [MOD p] := by
      have h : n.choose (p ^ (j + 1)) ≡
          (n % p).choose (p ^ (j + 1) % p) * (n / p).choose (p ^ (j + 1) / p) [MOD p] :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat
      rw [show p ^ (j + 1) % p = 0 from by rw [pow_succ]; exact Nat.mul_mod_left _ p,
          show p ^ (j + 1) / p = p ^ j from by
            rw [pow_succ]; exact Nat.mul_div_cancel _ hp.out.pos,
          Nat.choose_zero_right, one_mul] at h
      exact h
    -- Cast the recurrence to ZMod p and apply induction hypothesis
    have heq : (n.choose (p ^ (j + 1)) : ZMod p) = ((n / p).choose (p ^ j) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h_step
    -- Establish bounds for n/p
    have hlo' : p ^ j ≤ n / p :=
      (Nat.le_div_iff_mul_le hp.out.pos).mpr (pow_succ p j ▸ hlo)
    have hhi' : n / p < p ^ (j + 1) :=
      Nat.div_lt_of_lt_mul (by
        calc n < p ^ (j + 1 + 1) := hhi
             _ = p ^ (j + 1) * p := pow_succ p (j + 1)
             _ = p * p ^ (j + 1) := mul_comm _ _)
    -- Combine: n/p/p^j = n/p^(j+1)
    have hdiv : n / p / p ^ j = n / p ^ (j + 1) := by
      rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]
    rw [heq, ih (n / p) hlo' hhi', hdiv]

-- Helper: Lucas's theorem tells us when binomial(n, k) is nonzero mod p.
-- For n not a p-power, there exists k with 0 < k < n and binomial(n, k) ≢ 0 (mod p).
private lemma exists_binomial_ne_zero_of_not_prime_power
    {p : ℕ} [hp : Fact p.Prime] {n : ℕ} (hn : ¬ ∃ i, n = p ^ i) (hn_pos : n > 0) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (n.choose k : ZMod p) ≠ 0 := by
  classical
  -- Key insight: If n is not a p-power, write n in base p as n = Σᵢ nᵢ p^i
  -- where at least two digits nᵢ are nonzero.
  --
  -- By Lucas's theorem: binomial(n, k) ≡ ∏ᵢ binomial(nᵢ, kᵢ) (mod p)
  -- where k = Σᵢ kᵢ p^i is the base-p expansion of k.
  --
  -- This is nonzero mod p iff kᵢ ≤ nᵢ for all i.
  --
  -- Construction: Let j be the smallest index where nⱼ > 0.
  -- Since n is not p^j, there exists i > j with nᵢ > 0.
  -- Take k = p^j. Then:
  -- - k has kⱼ = 1, kₗ = 0 for l ≠ j
  -- - Since nⱼ > 0, we have kⱼ = 1 ≤ nⱼ
  -- - For all other indices l, kₗ = 0 ≤ nₗ
  -- So binomial(n, k) ≡ binomial(nⱼ, 1) · ∏ᵢ≠ⱼ binomial(nᵢ, 0)
  --                     ≡ nⱼ · 1 ≡ nⱼ (mod p)
  -- Since 0 < nⱼ < p, we have nⱼ ≢ 0 (mod p).
  -- Also 0 < p^j = k < n since n has a nonzero digit at position i > j.

  -- Find the smallest position with nonzero digit
  -- j = ⌊log_p n⌋ satisfies p^j ≤ n < p^(j+1)
  have ⟨j, hj⟩ : ∃ j, n ≥ p ^ j ∧ n < p ^ (j + 1) :=
    ⟨Nat.log p n, Nat.pow_log_le_self p hn_pos.ne', Nat.lt_pow_succ_log_self hp.out.one_lt n⟩

  -- Since n is not a p-power and n ≥ p^j, we have n > p^j
  have hn_gt : n > p ^ j :=
    lt_of_le_of_ne hj.1 (fun h => hn ⟨j, h.symm⟩)

  use p ^ j
  constructor
  · -- p^j > 0 since p > 0 and j ≥ 0
    exact pow_pos hp.out.pos j
  constructor
  · exact hn_gt
  · -- Show binomial(n, p^j) ≠ 0 in ZMod p using Lucas's theorem
    -- By choose_prime_pow_cast_eq_div: (n.choose(p^j) : ZMod p) = (n/p^j : ZMod p)
    rw [choose_prime_pow_cast_eq_div j n (le_of_lt hn_gt) hj.2]
    -- n/p^j is between 1 and p-1, hence nonzero in ZMod p
    have h_pos : 0 < n / p ^ j :=
      Nat.div_pos (le_of_lt hn_gt) (pow_pos hp.out.pos j)
    have h_lt : n / p ^ j < p := Nat.div_lt_of_lt_mul (by
      have h := hj.2; rw [pow_succ] at h; exact h)
    exact fun h => absurd (Nat.le_of_dvd h_pos ((ZMod.natCast_eq_zero_iff _ _).mp h))
      (not_le.mpr h_lt)

-- Helper lemma (planned): non-q-power coefficients vanish for additive polynomials.
lemma coeff_zero_of_not_q_power {P : Polynomial (Fq q)} (hP : IsAdditive.{0} P)
    {n : ℕ} (hn : ¬ ∃ i, n = q ^ i) : P.coeff n = 0 := by
  classical
  -- Handle the trivial case n = 0
  by_cases hn0 : n = 0
  · subst hn0
    exact constant_term_zero hP

  -- For n > 0 not a q-power, use binomial coefficient argument
  have hn_pos : n > 0 := Nat.pos_of_ne_zero hn0

  -- Find k with 0 < k < n such that binomial(n, k) ≠ 0 in characteristic q
  obtain ⟨k, hk_pos, hk_lt, hbinom⟩ := exists_binomial_ne_zero_of_not_prime_power hn hn_pos

  -- Strategy: Use the functional equation P(X+Y) = P(X) + P(Y) as polynomial identity
  -- Work over K = RatFunc (Fq q), an infinite field of characteristic q
  let K := RatFunc (Fq q)
  haveI : CharP K q := inferInstance
  haveI : Infinite K :=
    Infinite.of_injective (algebraMap (A q) K) (IsFractionRing.injective (A q) K)

  -- The functional equation holds for all x, y in K
  have hxy : ∀ x y : K,
      Polynomial.aeval x P + Polynomial.aeval y P = Polynomial.aeval (x + y) P :=
    hP (K := K)

  -- Key observation: Since P(x+y) = P(x) + P(y) for all x,y in an infinite field,
  -- this must hold as a polynomial identity in K[X,Y].
  --
  -- Expanding P(x+y) = Σᵢ aᵢ(x+y)^i using the binomial theorem:
  -- P(x+y) = Σᵢ aᵢ Σₗ binomial(i,l) x^l y^(i-l)
  --
  -- Meanwhile P(x) + P(y) = Σᵢ aᵢ(x^i + y^i)
  --
  -- Comparing coefficients of x^k y^(n-k):
  -- - In P(x+y): contributes aₙ · binomial(n, k)
  -- - In P(x) + P(y): contributes 0 (since k > 0 and n-k > 0)
  --
  -- Therefore: aₙ · binomial(n, k) = 0

  -- Since binomial(n, k) ≠ 0 in characteristic q, we have aₙ = 0

  -- Formal proof using polynomial evaluation
  -- Specialize to x = X (indeterminate) and y = ε (small parameter)
  -- and extract coefficient information

  -- The detailed proof requires:
  -- 1. Promoting the functional equation to polynomial identity (using infiniteness of K)
  -- 2. Extracting bivariate coefficients using commutative algebra
  -- 3. Applying the binomial theorem for (X+Y)^n
  -- 4. Using that (n.choose k : Fq q) ≠ 0 implies (n.choose k : K) ≠ 0

  -- Step 1: The coefficient P.coeff n as element of K
  let coeff_K : K := algebraMap (Fq q) K (P.coeff n)

  -- Step 2: Binomial coefficient is nonzero in K
  -- The map ℕ → K factors as ℕ → ZMod q → K (via CharP K q),
  -- so (m : K) = 0 ↔ q ∣ m ↔ (m : ZMod q) = 0.
  have binom_ne_zero_K : (n.choose k : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K q, ← ZMod.natCast_eq_zero_iff]
    exact hbinom

  -- Step 3: From the functional equation, extract that P.coeff n · binomial(n,k) = 0
  have key : coeff_K * (n.choose k : K) = 0 := by
    -- Idea: Extract the coefficient by repeated differentiation or by evaluation
    -- at specific algebraic elements.
    --
    -- Method: Use bivariate polynomial identity.
    -- Since hxy holds for all x, y in the infinite field K, we can conclude
    -- that the polynomial identity P(X+Y) = P(X) + P(Y) holds in K[X,Y].
    --
    -- Step 3a: Expand P(X+Y) using binomial theorem
    -- The coefficient of X^k Y^(n-k) in P(X+Y) = Σᵢ aᵢ(X+Y)^i is:
    --   Σᵢ aᵢ · [coefficient of X^k Y^(n-k) in (X+Y)^i]
    -- = Σᵢ aᵢ · (if i = n then C(n,k) else 0)
    -- = aₙ · C(n,k)
    --
    -- Step 3b: Coefficient of X^k Y^(n-k) in P(X) + P(Y)
    -- P(X) contributes X^k only when degree = k, with coefficient a_k
    -- P(Y) contributes Y^(n-k) only when degree = n-k, with coefficient a_(n-k)
    -- So we get X^k Y^(n-k) only if k = k and n-k = 0, or k = 0 and n-k = n-k.
    -- Since 0 < k < n, we have k ≠ 0 and n-k ≠ 0, so contribution is 0.
    --
    -- Therefore aₙ · C(n,k) = 0 in K.

    -- Formal approach: construct bivariate polynomial and extract coefficient
    -- This requires polynomial in two variables, which Lean encodes as
    -- Polynomial (Polynomial K) for outer variable X and inner variable Y.

    sorry -- Detailed bivariate polynomial manipulation
    -- Alternative: use MvPolynomial for cleaner multivariate reasoning
    -- or use formal power series with coefficient extraction

  -- Step 4: Conclude P.coeff n = 0
  have coeff_K_zero : coeff_K = 0 := by
    have := mul_eq_zero.mp key
    exact this.resolve_right binom_ne_zero_K

  -- Since algebraMap (Fq q) K is a field homomorphism, it is injective.
  -- coeff_K = algebraMap (Fq q) K (P.coeff n) = 0 implies P.coeff n = 0.
  exact (algebraMap (Fq q) K).injective (coeff_K_zero.trans (map_zero _).symm)

-- Helper lemma (planned): support is contained in q-power exponents.
lemma support_subset_q_powers {P : Polynomial (Fq q)} (hP : IsAdditive.{0} P) :
    ∀ n ∈ P.support, ∃ i, n = q ^ i := by
  intro n hn
  by_contra hnot
  have : P.coeff n = 0 := coeff_zero_of_not_q_power (P := P) hP hnot
  exact (Polynomial.mem_support_iff.mp hn) this

/-- Structure theorem: Every additive polynomial is a linear combination of Frobenius powers -/
theorem structure_theorem.{u} (P : Polynomial (Fq q)) (hP : IsAdditive.{u} P) :
  ∃ (n : ℕ) (coeffs : ℕ → Fq q),
    P = Finset.sum (Finset.range n) (fun i => coeffs i • frobeniusPower (q := q) i) := sorry

end IsAdditive

end CyclotomicFunctionFields

/-
## Proof Status and Remaining Work

### ✅ Completed

#### `Infinite (RatFunc (Fq q))`
   - **Proved via**: `Infinite.of_injective (algebraMap (A q) K) (IsFractionRing.injective (A q) K)`
   - `Polynomial (Fq q)` is infinite, and the fraction ring embedding is injective.

#### `exists_binomial_ne_zero_of_not_prime_power` - FULLY PROVED
   The following sub-goals were all closed:
   - **∃ j, p^j ≤ n < p^(j+1)**: via `Nat.log p n` using
     `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`
   - **n > p^j**: by contradiction—`n = p^j` would contradict `¬ ∃ i, n = p^i`
   - **0 < p^j**: by `pow_pos hp.out.pos j`
   - **C(n, p^j) ≠ 0 in ZMod p**: proved via `choose_prime_pow_cast_eq_div`
     plus `ZMod.natCast_eq_zero_iff`

#### `choose_prime_pow_cast_eq_div` (new private theorem)
   - **Statement**: If `p^j ≤ n < p^(j+1)` then
     `(n.choose (p^j) : ZMod p) = ((n / p^j : ℕ) : ZMod p)`
   - **Proved by**: induction on j using
     `Choose.choose_modEq_choose_mod_mul_choose_div_nat` (one-step Lucas recurrence),
     `Nat.div_div_eq_div_mul`, `Nat.le_div_iff_mul_le`, `Nat.div_lt_of_lt_mul`

#### `binom_ne_zero_K` — PROVED
   - **Goal**: `(n.choose k : ZMod q) ≠ 0 → (n.choose k : K) ≠ 0`
   - **Proof**:
     ```lean
     rw [Ne, CharP.cast_eq_zero_iff K q, ← ZMod.natCast_eq_zero_iff]
     exact hbinom
     ```
   - `CharP K q` gives `(m : K) = 0 ↔ q ∣ m`, and
     `ZMod.natCast_eq_zero_iff` gives `(m : ZMod q) = 0 ↔ q ∣ m`.

#### `algebraMap` injectivity — PROVED
   - **Goal**: From `coeff_K = 0` (where `coeff_K = algebraMap (Fq q) K (P.coeff n)`)
     conclude `P.coeff n = 0`
   - **Proof**:
     ```lean
     exact (algebraMap (Fq q) K).injective (coeff_K_zero.trans (map_zero _).symm)
     ```
   - A field homomorphism is always injective (`RingHom.injective`).

---

### ❌ Remaining `sorry`: `key` in `coeff_zero_of_not_q_power`

   - **Goal**: `coeff_K * (n.choose k : K) = 0`, i.e.,
     derive `(P.coeff n) * C(n,k) = 0` from
     `∀ x y : K, P(x) + P(y) = P(x+y)` with `0 < k < n`
   - **Strategy**: Lift the pointwise identity to a polynomial identity in `K[X,Y]`
     (valid since K is infinite), then compare coefficients of `X^k · Y^(n-k)`:
     - In `P(X+Y)` via binomial theorem: coefficient is `(P.coeff n) * C(n,k)`
     - In `P(X) + P(Y)`: coefficient is 0 (since 0 < k < n means neither pure X nor pure Y term)
   - **Recommended approach**: Use `MvPolynomial (Fin 2) K` with
     `MvPolynomial.funext` (polynomial equality from pointwise equality over
     an infinite ring), then extract the `Finsupp.single` coefficient.
   - **Note**: Once `key` is proved, `coeff_zero_of_not_q_power` is fully closed
     (Steps 4 and the final `algebraMap` injectivity are already proved).

---

### ❌ Remaining `sorry`: `structure_theorem`
   - **Goal**: Every additive polynomial is `Σᵢ aᵢ · x^(qⁱ)`
   - **Strategy**: `support_subset_q_powers` (already proved via
     `coeff_zero_of_not_q_power`) shows every nonzero coefficient index is a q-power.
     Use `Polynomial.as_sum_support` to decompose P as `Σ_{n ∈ P.support} P.coeff n • X^n`,
     then reindex over q-power exponents.
   - **Status**: Unblocked once `key` is resolved.
-/
