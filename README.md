# Cyclotomic Function Fields - Lean4 Formalization

This project aims to formalize Hayes' "Explicit Class Field Theory for Rational Function Fields" in Lean4, focusing on the theory of cyclotomic function fields over 𝔽_q(t).

## Goal

Formalize the theory of cyclotomic function fields over 𝔽_q(t) in Lean4, ultimately proving that every abelian extension can be explicitly constructed using division points of the Carlitz module.

## Project Structure

- `CyclotomicFunctionFields/Prelude.lean`: Basic setup (Fq, A, K, L)
- `CyclotomicFunctionFields/Carlitz/`: Carlitz module theory
  - `Basic.lean`: Carlitz module definition
  - `Additive.lean`: Additive polynomials
  - `Torsion.lean`: Division points Λ_M
  - `Field.lean`: Cyclotomic fields K(Λ_M)
- `CyclotomicFunctionFields/ClassField/Setup.lean`: Future CFT scaffolding
- `CyclotomicFunctionFields/Examples.lean`: Explicit computations

## Quick Start

```bash
# Install/update elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan self update

# Get cached builds
lake exe cache get

# Build project
lake build

# Open in VS Code
code .
```

## Mathematical Background

### The Carlitz Module

The Carlitz module is defined by its action on the generator t:

φ_t(x) = tx + x^q

where x^q is the Frobenius map.

### Division Points

For M ∈ A nonzero, the M-division points are:

Λ_M = {x ∈ L : φ_M(x) = 0}

Key properties:
- |Λ_M| = q^(deg M)
- Λ_M ≅ A/M as A-modules
- Tower: M | N ⟹ Λ_M ⊆ Λ_N

### Hayes' Main Theorem

Every finite abelian extension of K = 𝔽_q(t) is contained in some K(Λ_M).

## Resources

- D. R. Hayes, "Explicit class field theory for rational function fields", Trans. AMS 189 (1974), 77-91
- Lean 4 Documentation: https://leanprover.github.io/lean4/doc/
- Mathlib4 Docs: https://leanprover-community.github.io/mathlib4_docs/
