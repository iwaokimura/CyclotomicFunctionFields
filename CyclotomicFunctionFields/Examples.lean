/-
# Explicit Examples and Computations

This file contains explicit computations of:
- Division points for small cases (M = t, t², etc.)
- Cyclotomic fields for small q (q = 2, 3)
- Galois group calculations
- Concrete field extensions

These examples serve as test cases and illustrate the general theory.
-/

import CyclotomicFunctionFields.Carlitz.Field
import Mathlib.LinearAlgebra.Dimension.Finrank

open Module

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact q.Prime]

/-- Example: Verify the setup for q = 2 -/
example : CharP (Fq 2) 2 := inferInstance

/-- Example: The field K is a field -/
noncomputable example : Field (K 3) := inferInstance

/- Example computation for M = t -/
section ExampleT

variable (φ : CarlitzModule 2)

/-- For M = t, the division points generate a degree q extension -/
theorem cyclotomic_field_t_degree :
  finrank (K 2) (CyclotomicField Polynomial.X φ) = 2 := sorry

end ExampleT

/- Example: Computing division points explicitly for small cases -/
section SmallCases

/-- For q = 2, M = t, we can compute Λ_t explicitly -/
example (φ : CarlitzModule 2) :
  Nat.card (DivisionPoints Polynomial.X φ) = 2 := sorry

/-- For q = 3, M = t, we have |Λ_t| = 3 -/
example (φ : CarlitzModule 3) :
  Nat.card (DivisionPoints Polynomial.X φ) = 3 := sorry

end SmallCases

/- Example: Tower structure -/
section TowerExample

variable (φ : CarlitzModule 2)

/-- The tower K ⊆ K(Λ_t) ⊆ K(Λ_{t²}) -/
theorem tower_example :
  (CyclotomicField Polynomial.X φ : Set (L 2)) ⊆
  (CyclotomicField (Polynomial.X ^ 2) φ : Set (L 2)) := sorry

end TowerExample

end CyclotomicFunctionFields
