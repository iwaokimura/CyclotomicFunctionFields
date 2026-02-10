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
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.RingDivision

variable (q : ℕ) [Fact q.Prime]

abbrev Fq := ZMod q
abbrev A (q : ℕ) [Fact q.Prime] := Polynomial (Fq q)
abbrev K (q : ℕ) [Fact q.Prime] := RatFunc (Fq q)
abbrev L (q : ℕ) [Fact q.Prime] := SeparableClosure (K q)

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact q.Prime]

instance : CharP (Fq q) q := ZMod.charP q
instance : CharP (A q) q := inferInstance
instance : CharP (K q) q := inferInstance

end CyclotomicFunctionFields
