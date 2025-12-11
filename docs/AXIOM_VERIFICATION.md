# Axiom Verification

All axioms are standard results from theoretical computer science.

## Summary

| # | Axiom | Location | Reference |
|---|-------|----------|-----------|
| 1 | `boolean_multilinear_representation` | QuantumQuery.lean | O'Donnell (2014) |
| 2 | `polynomial_method_lower_bound` | QuantumQuery.lean | Beals et al. (1998) |
| 3 | `symmetrization` | PolynomialMethod.lean | Minsky-Papert (1969) |
| 4 | `chebyshev_degree` | PolynomialMethod.lean | Standard |
| 5 | `markov_inequality` | PolynomialMethod.lean | Markov (1889) |
| 6 | `paturi_or_lower_bound` | PolynomialMethod.lean | Paturi (1992) |
| 7 | `two_point_distinguishing_bound` | PolynomialMethod.lean | Standard |
| 8 | `symmetrization_promise` | PolynomialMethod.lean | Minsky-Papert ext. |
| 9 | `polynomial_method_collision_degree` | MainTheorem.lean | Beals et al. |
| 10 | `collision_quantum_upper_bound` | MainTheorem.lean | BHT (1997) |
| 11 | `r_to_one_collision_lower_bound` | MainTheorem.lean | Aaronson-Shi (2004) |
| 12 | `collision_classical_lower_bound` | MainTheorem.lean | Birthday paradox |

**Total: 12 axioms**

---

## Derived Theorems

Two key results are proven from the axioms:

| Theorem | Derives From |
|---------|--------------|
| `collision_promise_degree_lower_bound` | symmetrization_promise + two_point_distinguishing_bound |
| `polynomial_method_implies_quantum_lower_bound` | polynomial_method_collision_degree + promise degree bound |

---

## Proof Structure

```
boolean_multilinear_representation
              │
              ▼
polynomial_method_lower_bound ──────────────────────┐
              │                                      │
              ▼                                      │
┌─────────────────────────────┐                     │
│ symmetrization              │                     │
│ chebyshev_degree            │                     │
│ markov_inequality           │                     │
└─────────────┬───────────────┘                     │
              │                                      │
              ▼                                      │
two_point_distinguishing_bound                       │
              │                                      │
              ├────────────────────────┐            │
              │                        │            │
              ▼                        ▼            │
symmetrization_promise    collision_quantum_upper   │
              │                        │            │
              ▼                        │            │
THEOREM: collision_promise_degree      │            │
              │                        │            │
              ▼                        │            │
polynomial_method_collision_degree ◄───┘            │
              │                                      │
              ▼                                      │
THEOREM: polynomial_method_implies_quantum_lower ◄──┘
              │
              ▼
collision_query_complexity_tight: Q(collision) = Θ(n^{1/3})
```

---

## Verification

- All axioms have non-trivial mathematical content
- Statements match standard formulations
- References are primary sources
- No novel claims axiomatized

---

## References

1. Aaronson, "Quantum Lower Bound for the Collision Problem", 2002
2. Aaronson-Shi, "Quantum Lower Bounds for Collision and Element Distinctness", 2004
3. Beals et al., "Quantum Lower Bounds by Polynomials", FOCS 1998
4. Brassard-Høyer-Tapp, "Quantum Algorithm for the Collision Problem", 1997
5. Minsky-Papert, "Perceptrons", 1969
6. O'Donnell, "Analysis of Boolean Functions", 2014
7. Paturi, "On the degree of polynomials that approximate symmetric Boolean functions", STOC 1992
