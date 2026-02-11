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

-- Helper lemma (planned): non-q-power coefficients vanish for additive polynomials.
lemma coeff_zero_of_not_q_power {P : Polynomial (Fq q)} (hP : IsAdditive.{0} P)
    {n : ℕ} (hn : ¬ ∃ i, n = q ^ i) : P.coeff n = 0 := by
  classical
  -- Strategy: compare coefficients in the identity P(x + y) = P(x) + P(y)
  -- over an infinite field of characteristic q (e.g. RatFunc (Fq q)).
  -- For n not a q-power, some binomial coefficient (n choose k) is nonzero
  -- in char q, giving a contradiction if coeff n ≠ 0.
  -- Step 1: move to an infinite field of characteristic q.
  let K := RatFunc (Fq q)
  have hxy : ∀ x y : K,
      Polynomial.aeval x P + Polynomial.aeval y P = Polynomial.aeval (x + y) P :=
    hP (K := K)
  -- Step 2: turn the functional identity into a polynomial identity in two variables.
  -- We model bivariate polynomials as `Polynomial (Polynomial K)`.
  let X : Polynomial (Polynomial K) := Polynomial.X
  let Y : Polynomial (Polynomial K) := Polynomial.C Polynomial.X
  let Pxy : Polynomial (Polynomial K) := Polynomial.aeval (X + Y) P
  let Px : Polynomial (Polynomial K) := Polynomial.aeval X P
  let Py : Polynomial (Polynomial K) := Polynomial.aeval Y P
  have hpoly_eval : ∀ x y : K,
      Polynomial.eval₂ (Polynomial.evalRingHom y) x Pxy
        = Polynomial.eval₂ (Polynomial.evalRingHom y) x (Px + Py) := by
    intro x y
    -- TODO: connect `eval₂ (evalRingHom y)` on Pxy/Px/Py to `aeval` on K,
    -- then use `hxy x y`.
    sorry
  have hpoly : Pxy = Px + Py := by
    -- TODO: use polynomial ext via evaluation on all x,y (K is infinite).
    -- Suggested: `ext z` for coefficients, or `Polynomial.funext` with `hpoly_eval`.
    sorry
  -- Step 2b: compare bivariate coefficients.
  -- We view coefficients as `((Pxy.coeff i).coeff j)` corresponding to X^i * Y^j.
  -- Helper: extract the (i,j)-coefficient using hpoly.
  have hcoeff (i j : ℕ) : (Pxy.coeff i).coeff j = ((Px + Py).coeff i).coeff j := by
    simp [hpoly]
  -- TODO: compute the coefficient of X^k * Y^(n-k) in Pxy as
  --   P.coeff n * (n.choose k) (in K), using binomial expansion.
  -- TODO: compute the same coefficient in Px + Py (it should be 0 for 0<k<n).
  -- Step 3: use a binomial coefficient that survives in char q to force coeff n = 0.
  -- TODO: add the Lucas/Kummer-style lemma and finish.
  sorry

-- Helper lemma (planned): support is contained in q-power exponents.
lemma support_subset_q_powers {P : Polynomial (Fq q)} (hP : IsAdditive.{0} P) :
    P.support ⊆ {n | ∃ i, n = q ^ i} := by
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
Memo (next session):
1) Finish hpoly_eval: relate
  `Polynomial.eval₂ (Polynomial.evalRingHom y) x (Polynomial.aeval Z P)`
  to `Polynomial.aeval z P` for Z = X, Y, X+Y and z = x, y, x+y.
  Likely use `Polynomial.aeval_def` plus an eval₂ composition lemma.
2) Prove hpoly from hpoly_eval:
  show Pxy = Px + Py by polynomial ext using evaluation on all x,y in K;
  may need `Infinite K` (RatFunc is infinite) and a 2-variable ext lemma.
3) Compute coefficients:
  (a) in Pxy, show coeff of X^k Y^(n-k) is `P.coeff n * (n.choose k)`;
  (b) in Px + Py, show same coefficient is 0 for 0<k<n.
4) Add Lucas/Kummer lemma in char q:
  for n not q-power, there exists k with 0<k<n and (n choose k) ≠ 0 in Fq q.
  Use this to conclude P.coeff n = 0.
-/
