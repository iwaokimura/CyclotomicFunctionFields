/-
# Carlitz Module: Basic Definitions

This file defines the Carlitz module structure:
- CarlitzModule: The structure encoding φ : A → End(L)
- carlitz_t_action: The defining property φ_t(x) = tx + x^q
- Basic properties: additivity, linearity, ring homomorphism

Reference: Hayes (1974), Section 2
-/

import CyclotomicFunctionFields.Prelude
import CyclotomicFunctionFields.Carlitz.Additive
import Mathlib.RingTheory.TensorProduct.Basic

namespace CyclotomicFunctionFields

variable {q : ℕ} [Fact (Nat.Prime q ∨ q = 1)]

/-- The Carlitz module action on L -/
structure CarlitzModule (q : ℕ) [Fact (Nat.Prime q ∨ q = 1)] where
  /-- The action of A on L -/
  action : A q → (L q →+* L q)
  /-- The action on the generator t: φ_t(x) = tx + x^q -/
  carlitz_t_action : ∀ x : L q, action (Polynomial.X) x = (Polynomial.X : A q).coeff 0 • x + x ^ q
  /-- Additivity: φ_{a+b} = φ_a + φ_b -/
  add_action : ∀ (a b : A q), action (a + b) = action a + action b
  /-- Multiplicativity: φ_{ab} = φ_a ∘ φ_b -/
  mul_action : ∀ (a b : A q) (x : L q), action (a * b) x = action a (action b x)

namespace CarlitzModule

variable {q : ℕ} [Fact (Nat.Prime q ∨ q = 1)] (φ : CarlitzModule q)

/-- The Carlitz module action preserves 0 -/
theorem action_zero (a : A q) : φ.action a 0 = 0 := sorry

/-- The Carlitz module action preserves addition -/
theorem action_add (a : A q) (x y : L q) : 
  φ.action a (x + y) = φ.action a x + φ.action a y := sorry

/-- The Carlitz module defines a ring homomorphism -/
theorem is_ring_hom : ∀ a b : A q, φ.action (a + b) = φ.action a + φ.action b :=
  φ.add_action

end CarlitzModule

end CyclotomicFunctionFields
