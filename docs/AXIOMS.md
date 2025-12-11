# Axiom Documentation

All axioms in the Collision formalization are standard results from the literature.

## Summary

| Category | Count |
|----------|-------|
| Foundational | 2 |
| Approximation Theory | 6 |
| Query Complexity | 4 |
| **Total** | **12** |

**Derived Theorems** (not axioms):
- `collision_promise_degree_lower_bound` — from symmetrization_promise + two_point_distinguishing_bound
- `polynomial_method_implies_quantum_lower_bound` — from polynomial_method_collision_degree + promise degree bound

---

## 1. Foundational

### boolean_multilinear_representation

Every Boolean function f : {0,1}ⁿ → {0,1} has a unique multilinear polynomial representation.

```lean
axiom boolean_multilinear_representation {n : ℕ} (f : Input n → Bool) :
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ n ∧
    (∀ x : Input n, MvPolynomial.eval (toReal x) p = if f x then 1 else 0)
```

**Reference:** O'Donnell, *Analysis of Boolean Functions*, 2014.

---

### chebyshev_degree

The Chebyshev polynomial Tₙ has degree exactly n.

```lean
axiom chebyshev_degree (n : ℕ) : (chebyshevT n).natDegree = n
```

**Reference:** Standard result from approximation theory.

---

## 2. Approximation Theory

### symmetrization

For any multivariate polynomial p of degree d, there exists a univariate polynomial q of degree ≤ d such that q(k) equals the average of p over inputs of Hamming weight k.

```lean
axiom symmetrization {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
      ∀ k : ℕ, k ≤ n → q.eval (k : ℝ) = avgOverWeight p k
```

**Reference:** Minsky-Papert, *Perceptrons*, 1969.

---

### markov_inequality

If ‖p‖ ≤ 1 on [-1,1], then ‖p'‖ ≤ n² on [-1,1].

```lean
axiom markov_inequality (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.derivative.eval x| ≤ n^2
```

**Reference:** Markov, 1889.

---

### paturi_or_lower_bound

The approximate degree of OR on n bits is Ω(√n).

```lean
axiom paturi_or_lower_bound (n : ℕ) (hn : n > 0) :
  ∃ c : ℝ, c > 0 ∧ (stdApproxDegree (orFunction n) : ℝ) ≥ c * Real.sqrt n
```

**Reference:** Paturi, STOC 1992.

---

### two_point_distinguishing_bound

A polynomial distinguishing 0 from k₀ on [0,m] with bounded values requires degree ≥ c·(m/k₀)^{1/3}.

```lean
axiom two_point_distinguishing_bound (m k₀ : ℕ) (hm : m > 0) (hk : k₀ > 0) (hk_le : k₀ ≤ m) :
    ∃ c : ℝ, c > 0 ∧
      ∀ d : ℕ,
        (∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
          q.eval 0 ≤ 1/3 ∧ q.eval (k₀ : ℝ) ≥ 2/3 ∧
          (∀ k : ℕ, k ≤ m → |q.eval (k : ℝ)| ≤ 1)) →
        (d : ℝ) ≥ c * ((m : ℝ) / (k₀ : ℝ)) ^ (1/3 : ℝ)
```

**Reference:** Standard approximation theory (Cheney, Rivlin).

---

### symmetrization_promise

Promise-approximating multivariate polynomial yields univariate polynomial with same promise properties.

```lean
axiom symmetrization_promise {m d : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (hp_deg : p.totalDegree ≤ d)
    (hp_bound : ∀ x : Input m, 0 ≤ MvPolynomial.eval (toReal x) p ∧
                               MvPolynomial.eval (toReal x) p ≤ 1)
    (n : ℕ) (hn : n ≤ m)
    (hp_zero : ∀ x : Input m, hammingWeight x = 0 → MvPolynomial.eval (toReal x) p ≤ 1/3)
    (hp_n : ∀ x : Input m, hammingWeight x = n → MvPolynomial.eval (toReal x) p ≥ 2/3) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
      q.eval 0 ≤ 1/3 ∧ q.eval (n : ℝ) ≥ 2/3 ∧
      (∀ k : ℕ, k ≤ m → |q.eval (k : ℝ)| ≤ 1)
```

**Reference:** Extension of Minsky-Papert symmetrization.

---

## 3. Query Complexity

### polynomial_method_lower_bound

Q(f) ≥ ⌈deg̃(f)/2⌉.

```lean
axiom polynomial_method_lower_bound {n : ℕ} (f : Input n → Bool) :
    queryComplexity f ≥ (stdApproxDegree f + 1) / 2
```

**Reference:** Beals et al., FOCS 1998.

---

### polynomial_method_collision_degree

T-query bounded-error collision algorithm satisfies 2T ≥ promiseApproxDegree.

```lean
axiom polynomial_method_collision_degree (n T : ℕ) (hn : n > 0)
    (alg : BoundedErrorAlgorithm (numPairs (2 * n)))
    (hT : alg.queries = T)
    (haccept : ∀ f, IsTwoToOne f → alg.acceptance (collisionPatternEncoding ...) ≥ 2/3)
    (hreject : ∀ f, IsOneToOne f → alg.acceptance (collisionPatternEncoding ...) ≤ 1/3) :
    (2 * T : ℕ) ≥ promiseApproxDegree (numPairs (2 * n)) n (1/3)
```

**Reference:** Beals et al. applied to collision with promise.

---

### collision_quantum_upper_bound

There exists a quantum algorithm for collision using O(n^{1/3}) queries.

```lean
axiom collision_quantum_upper_bound (n : ℕ) (hn : n > 0) :
    ∃ c : ℝ, c > 0 ∧
      ∃ (T : ℕ), (T : ℝ) ≤ c * (n : ℝ)^(1/3 : ℝ) ∧
        ∃ alg : BoundedErrorAlgorithm (numPairs (2 * n)),
          alg.queries = T ∧ [correctness conditions]
```

**Reference:** Brassard-Høyer-Tapp, 1997.

---

### r_to_one_collision_lower_bound

r-to-1 collision requires Ω((n/r)^{1/3}) queries.

```lean
axiom r_to_one_collision_lower_bound (n r : ℕ) (hn : n > 0) (hr : r > 0) (hdiv : r ∣ n) :
    ∃ c : ℝ, c > 0 ∧
      ∀ T : ℕ, [algorithm solves r-to-1 collision] →
        (T : ℝ) ≥ c * ((n : ℝ) / (r : ℝ)) ^ (1/3 : ℝ)
```

**Reference:** Aaronson-Shi, 2004.

---

### collision_classical_lower_bound

Classical algorithms require Ω(√n) queries for collision.

```lean
axiom collision_classical_lower_bound (n : ℕ) (hn : n > 0) :
    ∃ c : ℝ, c > 0 ∧
      ∀ T : ℕ, [classical algorithm solves collision] →
        (T : ℝ) ≥ c * Real.sqrt n
```

**Reference:** Birthday paradox analysis.

---

## References

1. Aaronson, "Quantum Lower Bound for the Collision Problem", 2002
2. Aaronson-Shi, "Quantum Lower Bounds for Collision and Element Distinctness", 2004
3. Beals et al., "Quantum Lower Bounds by Polynomials", FOCS 1998
4. Brassard-Høyer-Tapp, "Quantum Algorithm for the Collision Problem", 1997
5. Minsky-Papert, "Perceptrons", 1969
6. O'Donnell, "Analysis of Boolean Functions", 2014
7. Paturi, "On the degree of polynomials that approximate symmetric Boolean functions", STOC 1992
