/-
# Additive Polynomials

This file develops the theory of additive polynomials over finite fields:
- IsAdditive: Predicate for P(x+y) = P(x) + P(y)
- frobeniusPower n: The polynomial x^(q^n)
- Structure theorem: Every additive polynomial is Σ aᵢ x^(qⁱ)

Reference: Hayes (1974), Section 1; Goss (1996), Chapter 1
-/

import CyclotomicFunctionFields.Prelude
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
        rw [@hP K _ _ x y]
      conv_lhs =>
        arg 2
        rw [@hQ K _ _ x y]
    _ = Polynomial.aeval (x + y) (P + Q) := by rw [← map_add]

/-- Scalar multiplication preserves additivity -/
theorem smul.{u} {P : Polynomial (Fq q)} (hP : IsAdditive.{u} P) (a : Fq q) :
  IsAdditive.{u} (a • P) := fun K _ _ x y => by
  show Polynomial.aeval x (a • P) + Polynomial.aeval y (a • P) = Polynomial.aeval (x + y) (a • P)
  simp only [map_smul]
  rw [← smul_add, @hP K _ _ x y]

/-- Composition of additive polynomials is additive -/
theorem comp.{u} {P Q : Polynomial (Fq q)} (hP : IsAdditive.{u} P) (hQ : IsAdditive.{u} Q) :
  IsAdditive.{u} (P.comp Q) := fun K _ _ x y => by
  simp only [Polynomial.aeval_comp]
  rw [← @hQ K _ _ x y, ← @hP K _ _ (Polynomial.aeval x Q) (Polynomial.aeval y Q)]

/-- Frobenius power polynomials are additive -/
theorem frobeniusPower_isAdditive.{u} (n : ℕ) : IsAdditive.{u} (frobeniusPower (q := q) n) := by
  intro K _ _ x y
  simp only [frobeniusPower, Polynomial.aeval_monomial]
  -- In characteristic p, (x + y)^(p^n) = x^(p^n) + y^(p^n)
  simp only [map_one, one_mul]
  -- This follows from iterative application of Frobenius
  sorry

/-- Structure theorem: Every additive polynomial is a linear combination of Frobenius powers -/
theorem structure_theorem.{u} (P : Polynomial (Fq q)) (hP : IsAdditive.{u} P) :
  ∃ (n : ℕ) (coeffs : ℕ → Fq q),
    P = Finset.sum (Finset.range n) (fun i => coeffs i • frobeniusPower (q := q) i) := sorry

end IsAdditive

end CyclotomicFunctionFields
