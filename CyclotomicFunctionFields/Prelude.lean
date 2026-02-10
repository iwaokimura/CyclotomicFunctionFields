/-
# Prelude: Basic Setup for Cyclotomic Function Fields

Defines:
- Fq: finite field with q elements
- A = Fq[t]: polynomial ring
- K = Fq(t): rational function field
- L: separable closure of K
-/

import Mathlib.NumberTheory.FunctionField
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IntermediateField
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Data.Polynomial.RingDivision

variable (q : ℕ) [Fact (Nat.Prime q ∨ q = 1)]

abbrev Fq := ZMod q
abbrev A (q : ℕ) [Fact (Nat.Prime q ∨ q = 1)] := Polynomial (Fq q)
abbrev K (q : ℕ) [Fact (Nat.Prime q ∨ q = 1)] := RatFunc (Fq q)
abbrev L (q : ℕ) [Fact (Nat.Prime q ∨ q = 1)] := SeparableClosure (K q)

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact (Nat.Prime q ∨ q = 1)]

instance : CharP (Fq q) q := ZMod.charP q
instance : CharP (A q) q := CharP.polynomial_charP (Fq q) q
instance : CharP (K q) q := inferInstance

end CyclotomicFunctionFields
