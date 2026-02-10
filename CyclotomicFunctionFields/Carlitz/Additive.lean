/-
# Additive Polynomials

This file develops the theory of additive polynomials over finite fields:
- IsAdditive: Predicate for P(x+y) = P(x) + P(y)
- frobeniusPower n: The polynomial x^(q^n)
- Structure theorem: Every additive polynomial is Σ aᵢ x^(qⁱ)

Reference: Hayes (1974), Section 1; Goss (1996), Chapter 1
-/

import CyclotomicFunctionFields.Prelude
import Mathlib.Data.Polynomial.Derivative
import Mathlib.FieldTheory.Separable

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact (Nat.Prime q ∨ q = 1)]

/-- A polynomial P is additive if P(x+y) = P(x) + P(y) for all x, y -/
def IsAdditive (P : Polynomial (Fq q)) : Prop :=
  ∀ (K : Type*) [Field K] [Algebra (Fq q) K] (x y : K),
    Polynomial.aeval x P + Polynomial.aeval y P = Polynomial.aeval (x + y) P

/-- The n-th Frobenius power polynomial x^(q^n) -/
def frobeniusPower (n : ℕ) : Polynomial (Fq q) :=
  Polynomial.monomial (q ^ n) 1

namespace IsAdditive

/-- The sum of two additive polynomials is additive -/
theorem add {P Q : Polynomial (Fq q)} (hP : IsAdditive P) (hQ : IsAdditive Q) :
  IsAdditive (P + Q) := sorry

/-- Scalar multiplication preserves additivity -/
theorem smul {P : Polynomial (Fq q)} (hP : IsAdditive P) (a : Fq q) :
  IsAdditive (a • P) := sorry

/-- Composition of additive polynomials is additive -/
theorem comp {P Q : Polynomial (Fq q)} (hP : IsAdditive P) (hQ : IsAdditive Q) :
  IsAdditive (P.comp Q) := sorry

/-- Frobenius power polynomials are additive -/
theorem frobeniusPower_isAdditive (n : ℕ) : IsAdditive (frobeniusPower n) := sorry

/-- Structure theorem: Every additive polynomial is a linear combination of Frobenius powers -/
theorem structure_theorem (P : Polynomial (Fq q)) (hP : IsAdditive P) :
  ∃ (n : ℕ) (coeffs : Fin n → Fq q),
    P = Finset.sum (Finset.range n) (fun i => coeffs i • frobeniusPower i) := sorry

end IsAdditive

end CyclotomicFunctionFields
