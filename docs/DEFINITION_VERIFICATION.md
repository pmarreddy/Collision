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

## Key Definitions

### Function Classifications

```lean
def IsOneToOne (f : α → β) := Function.Injective f

def IsRToOne (r : ℕ) (f : α → β) :=
  ∀ y ∈ Set.range f, (Finset.univ.filter (fun x => f x = y)).card = r

def hasCollision (f : α → β) := ∃ x₁ x₂, x₁ ≠ x₂ ∧ f x₁ = f x₂
```

### Query Model

```lean
structure QueryAlgorithm (n : ℕ) where
  queries : ℕ
  acceptance : Input n → ℝ
  is_polynomial : ∃ p, (∀ x, acceptance x = p.eval (toReal x)) ∧ p.totalDegree ≤ 2 * queries

def queryComplexity (f : Input n → Bool) : ℕ :=
  Nat.find (∃ A : BoundedErrorAlgorithm n, A.target = f ∧ A.queries ≤ T)
```

### Polynomial Method

```lean
def hammingWeight (x : Input n) := (Finset.univ.filter (fun i => x i)).card

def IsSymmetric (f : Input n → Bool) :=
  ∀ x y, hammingWeight x = hammingWeight y → f x = f y

def IsApproximating (p : MvPolynomial (Fin n) ℝ) (f : Input n → Bool) (ε : ℝ) :=
  ∀ x, |p.eval (toReal x) - (if f x then 1 else 0)| ≤ ε
```

### Collision Encoding

```lean
def numPairs (N : ℕ) := N * (N - 1) / 2

def collisionPatternEncoding (N R : ℕ) (f : Fin N → Fin R) : Input (numPairs N) :=
  fun idx => let (i, j) := pairFromIndex idx; decide (f i = f j)

def collisionIndicator (N : ℕ) (x : Input (numPairs N)) :=
  decide (∃ idx, x idx = true)
```

---

## Type Structure

```
Problem Layer:
  IsOneToOne, IsRToOne, IsTwoToOne → hasCollision

Query Layer:
  Input → QueryAlgorithm → BoundedErrorAlgorithm → queryComplexity

Polynomial Layer:
  hammingWeight, IsSymmetric → IsApproximating → approxDegree

Encoding Layer:
  numPairs → collisionPatternEncoding ↔ collisionIndicator
```

---

## References

1. Beals et al., "Quantum Lower Bounds by Polynomials", FOCS 1998
2. Minsky-Papert, "Perceptrons", 1969
3. Nisan-Szegedy, "On the degree of Boolean functions", STOC 1992
4. Aaronson, "Quantum Lower Bound for the Collision Problem", 2002
