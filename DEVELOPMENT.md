# Development Guide

## Daily Workflow

### 1. Pick a `sorry` to eliminate
- Start with simple lemmas
- Work bottom-up: Additive → Basic → Torsion → Field

### 2. Write the proof
Use these tactics and tools:
- `#check` to explore available lemmas
- `exact?` to search for exact matches
- `apply?` for goal-directed search
- `simp` for simplification
- `rw` for rewriting
- `intro` to introduce variables
- `cases` for case analysis

### 3. Test locally
```bash
lake build CyclotomicFunctionFields.Carlitz.Basic
```

### 4. Commit progress
```bash
git add -A
git commit -m "Prove: [description]"
```

## Tips for Lean Beginners

- **Use `sorry` liberally at first**: Focus on getting the structure right
- **Learn by example**: Study similar proofs in mathlib
- **Ask on Zulip**: https://leanprover.zulipchat.com/ - The Lean community is very helpful!
- **Use tactics**: Start with basic tactics and learn more as you go
- **Type-driven development**: Let Lean guide you with type errors

## Common Tactics

- `intro x`: Introduce a variable
- `apply h`: Apply a hypothesis or lemma
- `exact h`: Provide the exact proof term
- `rw [h]`: Rewrite using an equality
- `simp`: Simplify using simp lemmas
- `ring`: Solve ring equations
- `field_simp`: Simplify field expressions
- `norm_num`: Normalize numerical expressions
- `cases h`: Case split on a hypothesis
- `induction x`: Induction on x

## Mathlib Naming Conventions

- Use `PascalCase` for types and structures
- Use `snake_case` for theorems, definitions, and lemmas
- Follow patterns: `foo_bar_of_baz` (conclusion_of_hypothesis)
- Use `_comm`, `_assoc`, `_zero`, `_one` suffixes appropriately

## Checking Your Work

Run these commands to verify:

```bash
# Build everything
lake build

# Build a specific file
lake build CyclotomicFunctionFields.Carlitz.Basic

# Check for unused imports
lake exe checkUnusedImports

# Get documentation
lake -Kenv=dev build CyclotomicFunctionFields:docs
```

## Resources

- Lean 4 Manual: https://leanprover.github.io/lean4/doc/
- Mathlib4 Documentation: https://leanprover-community.github.io/mathlib4_docs/
- Theorem Proving in Lean 4: https://leanprover.github.io/theorem_proving_in_lean4/
- Mathematics in Lean: https://leanprover-community.github.io/mathematics_in_lean/
- Zulip Chat: https://leanprover.zulipchat.com/
