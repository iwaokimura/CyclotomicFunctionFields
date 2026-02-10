/-
# Division Points (Torsion Points)

This file defines and studies the M-division points of the Carlitz module:
- DivisionPoints M: The set Λ_M = {x : φ_M(x) = 0}
- Finiteness and cardinality: |Λ_M| = q^(deg M)
- Tower property: M | N ⟹ Λ_M ⊆ Λ_N
- A-module structure on Λ_M

Reference: Hayes (1974), Section 3
-/

import CyclotomicFunctionFields.Carlitz.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact (Nat.Prime q ∨ q = 1)]

/-- The M-division points (M-torsion) of the Carlitz module -/
def DivisionPoints (M : A q) (φ : CarlitzModule q) : Set (L q) :=
  {x : L q | φ.action M x = 0}

namespace DivisionPoints

variable (M : A q) (φ : CarlitzModule q)

/-- Division points form a finite set -/
theorem finite : (DivisionPoints M φ).Finite := sorry

/-- The cardinality of Λ_M is q^(deg M) -/
theorem card (hM : M ≠ 0) : 
  Nat.card (DivisionPoints M φ) = q ^ Polynomial.natDegree M := sorry

/-- Tower property: if M divides N, then Λ_M ⊆ Λ_N -/
theorem subset_of_dvd {M N : A q} (h : M ∣ N) :
  DivisionPoints M φ ⊆ DivisionPoints N φ := sorry

/-- Division points form an A-module -/
instance : AddCommGroup (DivisionPoints M φ) := sorry

/-- The A-module structure on division points -/
instance : Module (A q) (DivisionPoints M φ) := sorry

/-- Λ_M is isomorphic to A/M as A-modules -/
theorem iso_quotient (hM : M ≠ 0) :
  Nonempty ((DivisionPoints M φ) ≃+ (A q ⧸ Ideal.span {M})) := sorry

end DivisionPoints

end CyclotomicFunctionFields
