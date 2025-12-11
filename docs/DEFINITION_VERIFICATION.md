# Definition Verification

All definitions match standard TCS literature.

## Summary

| # | Definition | File | Description |
|---|------------|------|-------------|
| 1 | `IsOneToOne` | Basic.lean | Injective function |
| 2 | `IsRToOne` | Basic.lean | r-to-1 function |
| 3 | `IsTwoToOne` | Basic.lean | 2-to-1 function |
| 4 | `Collision` | Basic.lean | Pair with same image |
| 5 | `hasCollision` | Basic.lean | ∃ collision |
| 6 | `Input` | QuantumQuery.lean | Boolean string {0,1}ⁿ |
| 7 | `toReal` | QuantumQuery.lean | Boolean → Real embedding |
| 8 | `QueryAlgorithm` | QuantumQuery.lean | T queries → deg-2T polynomial |
| 9 | `BoundedErrorAlgorithm` | QuantumQuery.lean | 2/3 success probability |
| 10 | `queryComplexity` | QuantumQuery.lean | Q(f) = min queries |
| 11 | `IsApproximating` | QuantumQuery.lean | \|p(x) - f(x)\| ≤ ε |
| 12 | `approxDegree` | QuantumQuery.lean | deg_ε(f) |
| 13 | `stdApproxDegree` | QuantumQuery.lean | deg̃(f) with ε = 1/3 |
| 14 | `hammingWeight` | PolynomialMethod.lean | Number of 1-bits |
| 15 | `IsSymmetric` | PolynomialMethod.lean | Depends only on weight |
| 16 | `inputsOfWeight` | PolynomialMethod.lean | {x : \|x\| = k} |
| 17 | `avgOverWeight` | PolynomialMethod.lean | E_{|x|=k}[p(x)] |
| 18 | `chebyshevT` | PolynomialMethod.lean | Chebyshev polynomial |
| 19 | `orFunction` | PolynomialMethod.lean | OR on n bits |
| 20 | `numPairs` | PolynomialMethod.lean | N(N-1)/2 |
| 21 | `collisionIndicator` | PolynomialMethod.lean | OR on collision bits |
| 22 | `promiseApproxDegree` | PolynomialMethod.lean | Promise approximation degree |
| 23 | `StrictPair` | MainTheorem.lean | (i,j) with i < j |
| 24 | `pairIndex` | MainTheorem.lean | Pair enumeration |
| 25 | `collisionPatternEncoding` | MainTheorem.lean | f ↦ collision pattern |
| 26 | `collisionDecision` | MainTheorem.lean | Has collision? |
| 27 | `ClassicalQueryAlgorithm` | MainTheorem.lean | T queries → deg-T polynomial |

**Total: 27 definitions**

---

## Key Definitions with Standard Mathematical Notation

### 1. Function Classifications

#### IsOneToOne (Injective)
**Standard Math:** f : A → B is **injective** (one-to-one) iff
$$\forall x_1, x_2 \in A : f(x_1) = f(x_2) \Rightarrow x_1 = x_2$$

**Lean:**
```lean
def IsOneToOne (f : α → β) := Function.Injective f
```
**Reference:** Standard definition (any algebra textbook)

---

#### IsRToOne (r-to-1 function)
**Standard Math:** f : A → B is **r-to-one** iff every element in im(f) has exactly r preimages:
$$\forall y \in \text{im}(f) : |f^{-1}(y)| = r$$

**Lean:**
```lean
def IsRToOne (r : ℕ) (f : α → β) :=
  ∀ y ∈ Set.range f, (Finset.univ.filter (fun x => f x = y)).card = r
```
**Reference:** Brassard-Høyer-Tapp (1997), Aaronson (2002)

---

#### hasCollision
**Standard Math:** f has a **collision** iff
$$\exists x_1, x_2 \in A : x_1 \neq x_2 \land f(x_1) = f(x_2)$$

**Lean:**
```lean
def hasCollision (f : α → β) := ∃ x₁ x₂, x₁ ≠ x₂ ∧ f x₁ = f x₂
```
**Reference:** Standard cryptographic definition

---

### 2. Input Representation

#### Input (Boolean string)
**Standard Math:** The set of n-bit Boolean strings:
$$\{0,1\}^n = \{x : \{1,\ldots,n\} \to \{0,1\}\}$$

**Lean:**
```lean
abbrev Input (n : ℕ) := Fin n → Bool
```
**Reference:** Standard (Beals et al. 1998)

---

#### toReal (Boolean embedding)
**Standard Math:** The natural embedding of Boolean values into reals:
$$\iota : \{0,1\}^n \to \mathbb{R}^n, \quad \iota(x)_i = \begin{cases} 1 & \text{if } x_i = \text{true} \\ 0 & \text{if } x_i = \text{false} \end{cases}$$

**Lean:**
```lean
def toReal (x : Input n) : Fin n → ℝ := fun i => if x i then 1 else 0
```
**Reference:** Standard (Nisan-Szegedy 1992, Beals et al. 1998)

---

### 3. Query Model (Beals et al. 1998)

#### QueryAlgorithm
**Standard Math:** A **T-query quantum algorithm** is modeled by:
- T oracle queries to input x
- Acceptance probability Pr[accept | x] that is a **degree-2T polynomial** in x

$$\text{Pr}[\text{accept} | x] = p(x_1, \ldots, x_n) \quad \text{where } \deg(p) \leq 2T$$

**Lean:**
```lean
structure QueryAlgorithm (n : ℕ) where
  queries : ℕ
  acceptance : Input n → ℝ
  prob_valid : ∀ x, 0 ≤ acceptance x ∧ acceptance x ≤ 1
  is_polynomial : ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ x, acceptance x = MvPolynomial.eval (toReal x) p) ∧
    p.totalDegree ≤ 2 * queries
```
**Reference:** Beals, Buhrman, Cleve, Mosca, de Wolf, "Quantum Lower Bounds by Polynomials", FOCS 1998, J. ACM 2001

---

#### BoundedErrorAlgorithm
**Standard Math:** A **bounded-error algorithm** for f : {0,1}ⁿ → {0,1} satisfies:
$$f(x) = 1 \Rightarrow \text{Pr}[\text{accept} | x] \geq \frac{2}{3}$$
$$f(x) = 0 \Rightarrow \text{Pr}[\text{accept} | x] \leq \frac{1}{3}$$

**Lean:**
```lean
structure BoundedErrorAlgorithm (n : ℕ) extends QueryAlgorithm n where
  target : Input n → Bool
  completeness : ∀ x, target x = true → acceptance x ≥ 2/3
  soundness : ∀ x, target x = false → acceptance x ≤ 1/3
```
**Reference:** Beals et al. (1998); 2/3 threshold is standard (can be amplified)

---

#### queryComplexity
**Standard Math:** **Quantum query complexity** of f:
$$Q(f) = \min\{T \in \mathbb{N} : \exists \text{ bounded-error T-query algorithm computing } f\}$$

**Lean:**
```lean
noncomputable def queryComplexity (f : Input n → Bool) : ℕ :=
  Nat.find (fun T => ∃ A : BoundedErrorAlgorithm n, A.target = f ∧ A.queries ≤ T)
```
**Reference:** Beals et al. (1998)

---

### 4. Polynomial Method (Nisan-Szegedy 1992)

#### hammingWeight
**Standard Math:** **Hamming weight** of x ∈ {0,1}ⁿ:
$$|x| = \sum_{i=1}^{n} x_i = |\{i : x_i = 1\}|$$

**Lean:**
```lean
def hammingWeight (x : Input n) := (Finset.univ.filter (fun i => x i = true)).card
```
**Reference:** Standard definition

---

#### IsSymmetric
**Standard Math:** f : {0,1}ⁿ → {0,1} is **symmetric** iff it depends only on Hamming weight:
$$\forall x, y \in \{0,1\}^n : |x| = |y| \Rightarrow f(x) = f(y)$$

**Lean:**
```lean
def IsSymmetric (f : Input n → Bool) :=
  ∀ x y : Input n, hammingWeight x = hammingWeight y → f x = f y
```
**Reference:** Minsky-Papert (1969), "Perceptrons"

---

#### IsApproximating (ε-approximation)
**Standard Math:** Polynomial p **ε-approximates** Boolean function f iff:
$$\forall x \in \{0,1\}^n : |p(x) - f(x)| \leq \varepsilon$$
where f(x) is interpreted as 0 or 1.

**Lean:**
```lean
def IsApproximating (p : MvPolynomial (Fin n) ℝ) (f : Input n → Bool) (ε : ℝ) :=
  ∀ x : Input n, |MvPolynomial.eval (toReal x) p - (if f x then 1 else 0)| ≤ ε
```
**Reference:** Nisan-Szegedy (1992), "On the degree of Boolean functions as real polynomials"

---

#### approxDegree
**Standard Math:** **ε-approximate degree** of f (for ε ≥ 0):
$$\widetilde{\deg}_\varepsilon(f) = \min\{d \in \mathbb{N} : \exists p \in \mathbb{R}[x_1,\ldots,x_n], \deg(p) \leq d \land p \text{ ε-approximates } f\}$$

**Precondition:** ε ≥ 0. For ε < 0, no polynomial can ε-approximate any function (since |p(x) - f(x)| ≥ 0 > ε), so the infimum is undefined.

**Lean:**
```lean
noncomputable def approxDegree (f : Input n → Bool) (ε : ℝ) : ℕ :=
  if h : ε ≥ 0 then
    Nat.find (fun d => ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ IsApproximating p f ε)
  else 0  -- Sentinel: undefined for ε < 0
```
**Note:** The Lean implementation returns 0 as a sentinel for ε < 0. This value is meaningless; callers must ensure ε ≥ 0.

**Reference:** Nisan-Szegedy (1992)

---

#### stdApproxDegree
**Standard Math:** **Approximate degree** (standard notation deg̃):
$$\widetilde{\deg}(f) = \widetilde{\deg}_{1/3}(f)$$

The choice ε = 1/3 matches the bounded-error threshold.

**Lean:**
```lean
noncomputable def stdApproxDegree (f : Input n → Bool) : ℕ := approxDegree f (1/3)
```
**Reference:** Nisan-Szegedy (1992); ε = 1/3 is canonical

---

#### avgOverWeight (Symmetrization)
**Standard Math:** **Average over Hamming weight class** (for 0 ≤ k ≤ n):
$$\mathbb{E}_{|x|=k}[p(x)] = \frac{1}{\binom{n}{k}} \sum_{x : |x|=k} p(x)$$

**Precondition:** 0 ≤ k ≤ n. When k > n, the set {x : |x| = k} is empty (no n-bit string can have more than n ones), so the average is undefined.

**Lean:**
```lean
noncomputable def avgOverWeight (p : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  if h : (inputsOfWeight n k).card > 0 then
    (∑ x ∈ inputsOfWeight n k, MvPolynomial.eval (toReal x) p) / (inputsOfWeight n k).card
  else 0  -- Sentinel: undefined when weight class is empty (k > n)
```
**Note:** The Lean implementation returns 0 when the weight class is empty. This is a sentinel value; the average is only meaningful when 0 ≤ k ≤ n.

**Reference:** Minsky-Papert (1969), "Perceptrons", Chapter 3

---

### 5. Chebyshev Polynomials

#### chebyshevT
**Standard Math:** **Chebyshev polynomial of the first kind** Tₙ(x):

**Trigonometric definition:**
$$T_n(\cos\theta) = \cos(n\theta) \quad \text{for } \theta \in [0, \pi]$$

**Recurrence relation:**
$$T_0(x) = 1, \quad T_1(x) = x, \quad T_{n+1}(x) = 2x \cdot T_n(x) - T_{n-1}(x)$$

**Explicit polynomials:**
- $T_2(x) = 2x^2 - 1$
- $T_3(x) = 4x^3 - 3x$
- $T_4(x) = 8x^4 - 8x^2 + 1$

**Key properties:**
1. deg(Tₙ) = n with leading coefficient $2^{n-1}$ for n ≥ 1
2. $|T_n(x)| \leq 1$ for all $x \in [-1, 1]$
3. **Extremal property:** Among all degree-n monic polynomials, $2^{1-n}T_n$ has smallest sup-norm on [-1,1]
4. **Growth rate:** For $|x| > 1$: $T_n(x) = \frac{1}{2}\left[(x + \sqrt{x^2-1})^n + (x - \sqrt{x^2-1})^n\right]$

**Lean:**
```lean
noncomputable def chebyshevT (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ n
```
**Reference:** Cheney, "Introduction to Approximation Theory" (1966); Rivlin, "Chebyshev Polynomials" (1990)

---

### 6. Collision Encoding (Aaronson 2002)

#### numPairs
**Standard Math:** Number of unordered pairs from N elements:
$$\binom{N}{2} = \frac{N(N-1)}{2}$$

**Lean:**
```lean
def numPairs (N : ℕ) := N * (N - 1) / 2
```
**Reference:** Standard combinatorics

---

#### collisionPatternEncoding
**Standard Math:** **Collision pattern encoding** of f : [N] → [R]:
$$\text{encode}(f) \in \{0,1\}^{\binom{N}{2}}$$
where for each pair (i,j) with i < j:
$$\text{encode}(f)_{(i,j)} = \begin{cases} 1 & \text{if } f(i) = f(j) \\ 0 & \text{if } f(i) \neq f(j) \end{cases}$$

**Lean:**
```lean
noncomputable def collisionPatternEncoding (N R : ℕ) (f : Fin N → Fin R) : Input (numPairs N) :=
  fun idx => let pair := pairFromIndex N idx; decide (f pair.val.1 = f pair.val.2)
```
**Reference:** Aaronson (2002), "Quantum Lower Bound for the Collision Problem"

---

#### collisionIndicator
**Standard Math:** **Collision indicator** = OR over all pair comparisons:
$$\text{COL}(x) = \text{OR}(x_0, x_1, \ldots, x_{M-1}) = \begin{cases} 1 & \text{if } \exists m \in \{0,\ldots,M-1\} : x_m = 1 \\ 0 & \text{otherwise} \end{cases}$$
where $M = \binom{N}{2}$.

**Lean:**
```lean
def collisionIndicator (N : ℕ) (x : Input (numPairs N)) : Bool :=
  decide (∃ idx : Fin (numPairs N), x idx = true)
```
**Reference:** Aaronson (2002)

---

### 7. Promise Approximation (Aaronson 2002)

#### promiseApproxDegree
**Standard Math:** **Promise approximate degree** for collision:

For the promise problem (weight 0 vs weight n on m bits), polynomial p **ε-promise-approximates** iff:
1. $\forall x \in \{0,1\}^m : p(x) \in [0,1]$ (valid probability)
2. $|x| = 0 \Rightarrow p(x) \leq \varepsilon$ (reject 1-to-1 functions)
3. $|x| = n \Rightarrow p(x) \geq 1-\varepsilon$ (accept 2-to-1 functions)

$$\widetilde{\deg}^{\text{promise}}_\varepsilon(m, n) = \min\{d \in \mathbb{N} : \exists p \in \mathbb{R}[x_1,\ldots,x_m], \deg(p) \leq d \land p \text{ ε-promise-approximates}\}$$

**Preconditions:**
- ε > 0 (otherwise condition 2 requires p(x) ≤ 0 while condition 1 requires p(x) ≥ 0, forcing p ≡ 0 at weight 0)
- ε < 1/2 (otherwise conditions 2 and 3 can both be satisfied by constant p = 1/2, giving trivial degree 0)
- n > 0 (otherwise weight-n promise set is just weight-0, making the problem trivial)
- Implicitly: n ≤ m for the promise set to be non-empty (no m-bit string has weight > m)

**Lean:**
```lean
noncomputable def promiseApproxDegree (m n : ℕ) (ε : ℝ) : ℕ :=
  if h : ε > 0 ∧ ε < 1/2 ∧ n > 0 then
    Nat.find (fun d => ∃ p : MvPolynomial (Fin m) ℝ,
      p.totalDegree ≤ d ∧ IsPromiseApproximating p n ε)
  else 0  -- Sentinel: undefined when preconditions fail
```
**Note:** Returns 0 as sentinel when preconditions fail. The implementation does NOT check n ≤ m; if n > m, the weight-n set is empty, making condition 3 vacuously true—any bounded polynomial works, collapsing the degree to 0. Callers must ensure n ≤ m for meaningful results.

**Key insight:** This is SMALLER than stdApproxDegree since we only require correctness on promise inputs (weight 0 and weight n), not all $2^m$ inputs.

**Reference:** Aaronson (2002); the Ω(n^{1/3}) bound is Aaronson's key contribution

---

### 8. Classical vs Quantum

#### ClassicalQueryAlgorithm
**Standard Math:** A **T-query classical algorithm** has acceptance probability that is a **degree-T polynomial** (not 2T):
$$\text{Pr}[\text{accept} | x] = p(x) \quad \text{where } \deg(p) \leq T$$

**Lean:**
```lean
structure ClassicalQueryAlgorithm (n : ℕ) where
  queries : ℕ
  acceptance : Input n → ℝ
  is_polynomial : ∃ p, (∀ x, acceptance x = p.eval (toReal x)) ∧ p.totalDegree ≤ queries
```
**Reference:** Nisan (1991), "CREW PRAMS and decision trees"

---

## Type Structure

```
Problem Layer:
  IsOneToOne, IsRToOne, IsTwoToOne → hasCollision

Query Layer:
  Input → QueryAlgorithm → BoundedErrorAlgorithm → queryComplexity

Polynomial Layer:
  hammingWeight, IsSymmetric → IsApproximating → approxDegree → stdApproxDegree

Symmetrization Layer:
  avgOverWeight → symmetrization lemma → univariate reduction

Approximation Theory Layer:
  chebyshevT → Markov inequality → two_point_distinguishing_bound

Encoding Layer:
  numPairs → StrictPair → pairIndex → collisionPatternEncoding ↔ collisionIndicator

Promise Layer:
  IsPromiseApproximating → promiseApproxDegree → collision_promise_degree_lower_bound
```

---

## Main Theorem Chain

**Setup:** Collision on domain [N] = [2n] with 2-to-1 promise.
- Number of pair-bits: m = C(2n,2) = n(2n-1)
- Collision count for 2-to-1: exactly n pairs collide

```
T-query quantum algorithm for collision
        ↓  Beals et al. (1998): acceptance = degree-2T polynomial
degree-2T polynomial p(x) on m = n(2n-1) bits
        ↓  bounded-error on promise inputs
p(x) ≤ 1/3 when |x| = 0  (1-to-1 case)
p(x) ≥ 2/3 when |x| = n  (2-to-1 case)
        ↓  symmetrization (Minsky-Papert 1969)
∃ univariate q of degree ≤ 2T with q(0) ≤ 1/3, q(n) ≥ 2/3, |q(k)| ≤ 1 on [0,m]
        ↓  approximation theory (Chebyshev growth bounds)
deg(q) ≥ c · (m/n)^{1/3}  for some constant c > 0
        ↓  substituting m = n(2n-1) ≥ n·n = n²
2T ≥ c · (n²/n)^{1/3} = c · n^{1/3}
        ↓  divide by 2
T ≥ (c/2) · n^{1/3} = Ω(n^{1/3})  ∎
```

**Note:** The constant c comes from Chebyshev polynomial growth rates. The exact value depends on the approximation-theoretic analysis but the Ω(n^{1/3}) scaling is tight (matched by BHT upper bound).

---

## References

### Primary Sources
1. **Beals, Buhrman, Cleve, Mosca, de Wolf** (1998/2001), "Quantum Lower Bounds by Polynomials", FOCS 1998, J. ACM 48(4):778-797
2. **Nisan, Szegedy** (1992/1994), "On the Degree of Boolean Functions as Real Polynomials", STOC 1992, Computational Complexity 4:301-313
3. **Minsky, Papert** (1969), "Perceptrons: An Introduction to Computational Geometry", MIT Press
4. **Aaronson** (2002), "Quantum Lower Bound for the Collision Problem", STOC 2002
5. **Aaronson, Shi** (2004), "Quantum Lower Bounds for the Collision and the Element Distinctness Problems", J. ACM 51(4):595-605
6. **Brassard, Høyer, Tapp** (1997), "Quantum Algorithm for the Collision Problem", arXiv:quant-ph/9705002

### Secondary Sources
7. **Paturi** (1992), "On the Degree of Polynomials that Approximate Symmetric Boolean Functions", STOC 1992
8. **Cheney** (1966), "Introduction to Approximation Theory", McGraw-Hill
9. **Rivlin** (1990), "Chebyshev Polynomials: From Approximation Theory to Algebra and Number Theory", Wiley
10. **Markov** (1889), "On a question by D.I. Mendeleev", original Russian; establishes Markov brothers' inequality

### Surveys
11. **Bun, Thaler** (2020), "Approximate Degree in Classical and Quantum Computing", Foundations and Trends in TCS
12. **de Wolf** (2024), "Open Problems Related to Quantum Query Complexity", ACM Trans. Quantum Computing
