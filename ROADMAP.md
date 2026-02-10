# Development Roadmap

## Phase 1: Foundational Infrastructure (Current)

### Week 1-2: Prelude and Basic Setup
- [x] Define Fq, A, K, L
- [ ] Set up characteristic p instances
- [ ] Verify imports from mathlib4

### Week 3-4: Additive Polynomials
- [ ] Define IsAdditive predicate
- [ ] Prove structure theorem: every additive polynomial is Σ aᵢ x^(qⁱ)
- [ ] Prove closure properties

### Week 5-7: Carlitz Module
- [ ] Define CarlitzModule structure
- [ ] Prove φ_t(x) = tx + x^q
- [ ] Prove ring homomorphism properties
- [ ] Prove additivity and linearity

### Week 8-10: Division Points
- [ ] Define DivisionPoints M
- [ ] Prove finiteness of Λ_M
- [ ] Prove |Λ_M| = q^(deg M)
- [ ] Prove tower property: M | N ⟹ Λ_M ⊆ Λ_N
- [ ] Define A-module structure

### Week 11-14: Cyclotomic Function Fields
- [ ] Define CyclotomicField M
- [ ] Prove [K(Λ_M) : K] = q^(deg M)
- [ ] Prove K(Λ_M)/K is separable
- [ ] Prove K(Λ_M)/K is Galois
- [ ] Prove Gal(K(Λ_M)/K) is abelian

## Phase 2: Class Field Theory Connection (Future)

### Galois Groups
- [ ] Compute Gal(K(Λ_M)/K) ≅ (A/M)*
- [ ] Prove compatibility with tower structure

### Ray Class Groups
- [ ] Define ray class groups for function fields
- [ ] Establish conductor theory

### Artin Map
- [ ] Define Artin reciprocity map
- [ ] Prove surjectivity

### Hayes' Main Theorem
- [ ] Prove every abelian extension is contained in some K(Λ_M)
- [ ] Establish explicit class field theory

## Phase 3: Applications and Examples

### Explicit Computations
- [ ] Compute division points for small cases (M = t, t², etc.)
- [ ] Examples for q = 2, 3
- [ ] Galois group calculations

### Integration with Mathlib
- [ ] Refactor for mathlib4 contribution
- [ ] Complete documentation
- [ ] Add comprehensive tests

## Current Status

✅ Project structure created
⬜ Basic infrastructure (in progress)
⬜ Carlitz module definition
⬜ Division points theory
⬜ Cyclotomic fields construction
⬜ Class field theory connection
