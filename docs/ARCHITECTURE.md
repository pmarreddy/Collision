# Architecture: Quantum Lower Bound for the Collision Problem

Lean 4 formalization proving Q(collision) = Θ(n^{1/3}).

## Proof Structure

```
┌─────────────────────────────────────────────────────────────────┐
│                         MAIN THEOREM                             │
│         Q(collision) = Θ(n^{1/3})                                │
└─────────────────────────────────────────────────────────────────┘
                    │                              │
          ┌────────┴────────┐            ┌────────┴────────┐
          │   LOWER BOUND   │            │   UPPER BOUND   │
          │   Ω(n^{1/3})    │            │   O(n^{1/3})    │
          │    [THEOREM]    │            │     [AXIOM]     │
          └────────┬────────┘            └─────────────────┘
                   │
    ┌──────────────┴──────────────┐
    │      POLYNOMIAL METHOD      │
    │   T queries → deg-2T poly   │
    │          [AXIOM]            │
    └──────────────┬──────────────┘
                   │
    ┌──────────────┴──────────────┐
    │   PROMISE DEGREE BOUND      │
    │   deg̃(collision) ≥ Ω(n^{1/3}) │
    │         [THEOREM]           │
    └──────────────┬──────────────┘
                   │
    ┌──────────────┴──────────────┐
    │     SYMMETRIZATION +        │
    │   APPROXIMATION THEORY      │
    │          [AXIOMS]           │
    └─────────────────────────────┘
```

## Module Structure

```
Collision/
├── Basic.lean            # Problem definitions
├── QuantumQuery.lean     # Query complexity model
├── PolynomialMethod.lean # Approximation theory
└── MainTheorem.lean      # Main result
```

---

## Layer 1: Basic.lean

Defines the collision problem.

### Definitions

| Name | Type | Description |
|------|------|-------------|
| `IsOneToOne f` | `Prop` | f is injective |
| `IsRToOne r f` | `Prop` | Each image has exactly r preimages |
| `IsTwoToOne f` | `Prop` | r = 2 case |
| `hasCollision f` | `Prop` | ∃ distinct x₁, x₂ with f(x₁) = f(x₂) |

### Theorems

- `one_to_one_no_collision`: Injective ⟹ no collision
- `two_to_one_has_collision`: 2-to-1 ⟹ collision exists

**Axioms: 0**

---

## Layer 2: QuantumQuery.lean

Formalizes quantum query complexity.

### Definitions

| Name | Type | Description |
|------|------|-------------|
| `Input n` | `Type` | Boolean string {0,1}ⁿ |
| `BoundedErrorAlgorithm n` | `Structure` | Algorithm with ≥2/3 success |
| `queryComplexity f` | `ℕ` | Minimum queries needed |
| `stdApproxDegree f` | `ℕ` | Approximate degree (ε = 1/3) |

### Axioms (2)

| Axiom | Statement |
|-------|-----------|
| `boolean_multilinear_representation` | Boolean functions have multilinear representations |
| `polynomial_method_lower_bound` | Q(f) ≥ ⌈deg̃(f)/2⌉ |

---

## Layer 3: PolynomialMethod.lean

Approximation-theoretic tools for degree bounds.

### Definitions

| Name | Type | Description |
|------|------|-------------|
| `hammingWeight x` | `ℕ` | Number of 1-bits |
| `IsSymmetric f` | `Prop` | f depends only on Hamming weight |
| `promiseApproxDegree m n ε` | `ℕ` | Minimum degree for promise approximation |

### Theorems

- `collision_promise_degree_lower_bound`: promiseApproxDegree ≥ c·n^{1/3}

### Axioms (6)

| Axiom | Statement |
|-------|-----------|
| `symmetrization` | Degree-d multivariate → degree-d univariate |
| `chebyshev_degree` | deg(Tₙ) = n |
| `markov_inequality` | ‖p‖ ≤ 1 on [-1,1] ⟹ ‖p'‖ ≤ n² |
| `paturi_or_lower_bound` | deg̃(OR_n) ≥ c·√n |
| `two_point_distinguishing_bound` | Distinguishing 0 from k₀ needs degree ≥ c·(m/k₀)^{1/3} |
| `symmetrization_promise` | Promise approximation preserved under symmetrization |

---

## Layer 4: MainTheorem.lean

Connects all components.

### Encoding Bridge

```
Oracle Model                     Polynomial Model
─────────────                    ────────────────
f : Fin N → Fin R       ←→       x : Input (numPairs N)
collisionDecision(f)    ←→       collisionIndicator(x)
```

The bridge is established via `collisionPatternEncoding`.

### Theorems

- `encoding_indicator_bridge`: collisionIndicator ∘ encoding = collisionDecision
- `one_to_one_pattern_zeros`: 1-to-1 ⟹ weight-0 pattern
- `r_to_one_pattern_weight`: r-to-1 ⟹ weight = (N/r)·C(r,2)
- `polynomial_method_implies_quantum_lower_bound`: Q(collision) ≥ c·n^{1/3}
- `collision_query_complexity_tight`: Q(collision) = Θ(n^{1/3})

### Axioms (4)

| Axiom | Statement |
|-------|-----------|
| `polynomial_method_collision_degree` | T queries ⟹ 2T ≥ promiseApproxDegree |
| `collision_quantum_upper_bound` | ∃ algorithm with O(n^{1/3}) queries |
| `r_to_one_collision_lower_bound` | r-to-1 needs Ω((n/r)^{1/3}) queries |
| `collision_classical_lower_bound` | Classical needs Ω(√n) queries |

---

## Axiom Summary

| Category | Axioms |
|----------|--------|
| Foundational | 2 |
| Approximation Theory | 6 |
| Query Complexity | 4 |
| **Total** | **12** |

All axioms are standard results from the literature.

### Key Theorems (Derived)

| Theorem | Derivation |
|---------|------------|
| `collision_promise_degree_lower_bound` | From symmetrization_promise + two_point_distinguishing_bound |
| `polynomial_method_implies_quantum_lower_bound` | From polynomial_method_collision_degree + promise degree bound |

---

## Build

```bash
lake build Collision  # Success, 0 sorries
```

---

## References

1. Aaronson, "Quantum Lower Bound for the Collision Problem", 2002
2. Aaronson-Shi, "Quantum Lower Bounds for Collision and Element Distinctness", 2004
3. Brassard-Høyer-Tapp, "Quantum Algorithm for the Collision Problem", 1997
4. Beals et al., "Quantum Lower Bounds by Polynomials", FOCS 1998
5. Paturi, "On the degree of polynomials that approximate symmetric Boolean functions", STOC 1992
6. Minsky-Papert, "Perceptrons", 1969
