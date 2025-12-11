/-
# Quantum Query Model

Standard formalization of the quantum query model following Beals et al. (1998).

## Key Definitions

**Oracle Model** (Standard):
- Input x ∈ {0,1}ⁿ is accessed via oracle O_x
- Bit oracle: O_x|i,b⟩ = |i, b ⊕ xᵢ⟩
- Phase oracle: O_x|i⟩ = (-1)^{xᵢ}|i⟩ (equivalent up to basis change)

**Query Complexity**:
- Q(f) = minimum queries for bounded-error computation of f
- Bounded error: Pr[correct] ≥ 2/3 on all inputs

**Polynomial Method** (Beals et al. 1998):
- T-query algorithm → acceptance probability is degree-2T polynomial
- Therefore: Q(f) ≥ deg̃(f)/2, where deg̃ is approximate degree

## References
- Beals, Buhrman, Cleve, Mosca, de Wolf, "Quantum Lower Bounds by Polynomials" (1998)
- Nisan-Szegedy, "On the degree of Boolean functions as real polynomials" (1994)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Basic

namespace QuantumQuery

/-!
## The Oracle

Standard definition: oracle O_x encodes input string x ∈ {0,1}ⁿ.

We work abstractly: the key property is that T queries to O_x
yield acceptance probability that is a degree-2T polynomial in x.
-/

/-- Input string type: n-bit Boolean string. -/
abbrev Input (n : ℕ) := Fin n → Bool

/-- Convert Boolean input to real values (0 or 1) for polynomial evaluation. -/
def toReal {n : ℕ} (x : Input n) : Fin n → ℝ :=
  fun i => if x i then 1 else 0

/-!
## Multilinear Polynomial Representation

Every Boolean function f : {0,1}ⁿ → {0,1} has a unique multilinear polynomial
representation p ∈ ℝ[x₁,...,xₙ] such that p(x) = f(x) for all x ∈ {0,1}ⁿ.

This is also known as the algebraic normal form (ANF) or Fourier expansion.
The polynomial is multilinear (degree at most 1 in each variable), so total degree ≤ n.
-/

/--
**Multilinear Polynomial Representation** (Folklore/Fourier Analysis):
Every Boolean function has a unique multilinear polynomial that agrees with it
on the Boolean hypercube {0,1}ⁿ.

This is a fundamental result used throughout query complexity.
The polynomial p satisfies:
- p(x) = f(x) for all x ∈ {0,1}ⁿ
- p is multilinear (degree ≤ 1 in each variable)
- deg(p) ≤ n
-/
axiom boolean_multilinear_representation {n : ℕ} (f : Input n → Bool) :
  ∃ p : MvPolynomial (Fin n) ℝ,
    p.totalDegree ≤ n ∧
    (∀ x : Input n, MvPolynomial.eval (toReal x) p = if f x then 1 else 0)

/-!
## Quantum Query Algorithm

Abstract model: we care about query count and acceptance probability.
The full unitary model is equivalent for query complexity purposes.
-/

/--
Abstract quantum query algorithm with T queries.

**Standard Model**: Algorithm alternates T+1 unitaries with T oracle calls:
  |ψ_final⟩ = U_T · O_x · U_{T-1} · O_x · ... · U_1 · O_x · U_0 |0⟩

We abstract this to just the acceptance probability function,
with the constraint that it must be a degree-2T polynomial.
-/
structure QueryAlgorithm (n : ℕ) where
  /-- Number of oracle queries -/
  queries : ℕ
  /-- Acceptance probability as function of input x ∈ {0,1}ⁿ -/
  acceptance : Input n → ℝ
  /-- Acceptance probability is valid (in [0,1]) -/
  prob_valid : ∀ x, 0 ≤ acceptance x ∧ acceptance x ≤ 1
  /-- Key property: acceptance is a degree-2T polynomial (Beals et al.) -/
  is_polynomial : ∃ p : MvPolynomial (Fin n) ℝ,
    (∀ x, acceptance x = MvPolynomial.eval (toReal x) p) ∧
    p.totalDegree ≤ 2 * queries

/-!
## Bounded-Error Query Complexity

**Standard Definition** (following Beals et al.):
- f : {0,1}ⁿ → {0,1} is the Boolean function to compute
- Algorithm has bounded error if:
  - f(x) = 1 ⟹ Pr[accept] ≥ 2/3  (completeness)
  - f(x) = 0 ⟹ Pr[accept] ≤ 1/3  (soundness)
- Query complexity Q(f) = minimum queries over all bounded-error algorithms

Note: 2/3 can be amplified to 1-ε with O(log(1/ε)) overhead.
-/

/--
Bounded-error quantum query algorithm for Boolean function f.

**Standard Definition**: Algorithm computes f with bounded error iff
- On YES instances (f(x)=1): accept with probability ≥ 2/3
- On NO instances (f(x)=0): accept with probability ≤ 1/3
-/
structure BoundedErrorAlgorithm (n : ℕ) extends QueryAlgorithm n where
  /-- The Boolean function being computed -/
  target : Input n → Bool
  /-- Completeness: accept YES instances with probability ≥ 2/3 -/
  completeness : ∀ x, target x = true → acceptance x ≥ 2/3
  /-- Soundness: accept NO instances with probability ≤ 1/3 -/
  soundness : ∀ x, target x = false → acceptance x ≤ 1/3

/--
Quantum query complexity of f: minimum queries over all bounded-error algorithms.

Q(f) = min { T : ∃ algorithm A with T queries computing f with bounded error }
-/
noncomputable def queryComplexity {n : ℕ} (f : Input n → Bool) : ℕ :=
  @Nat.find (fun T => ∃ A : BoundedErrorAlgorithm n, A.target = f ∧ A.queries ≤ T)
    (Classical.decPred _) (bounded_error_exists f)
where
  /-- Every Boolean function can be computed with enough queries (trivially n queries suffice).
      Proof: Read all n bits deterministically, then compute f exactly.
      The deterministic algorithm has acceptance probability ∈ {0, 1}, which satisfies
      bounded error (1 ≥ 2/3 and 0 ≤ 1/3). -/
  bounded_error_exists (f : Input n → Bool) : ∃ T : ℕ, ∃ A : BoundedErrorAlgorithm n,
      A.target = f ∧ A.queries ≤ T := by
    -- Construct a deterministic algorithm using n queries
    use n
    -- The algorithm that computes f exactly
    let acc : Input n → ℝ := fun x => if f x then 1 else 0
    -- Construct the algorithm
    refine ⟨⟨⟨n, acc, ?prob_valid, ?is_poly⟩, f, ?compl, ?sound⟩, rfl, le_refl n⟩
    case prob_valid =>
      intro x
      simp only [acc]
      split_ifs <;> norm_num
    case is_poly =>
      -- Use the multilinear polynomial representation
      obtain ⟨p, hp_deg, hp_eval⟩ := boolean_multilinear_representation f
      use p
      constructor
      · intro x
        simp only [acc]
        exact (hp_eval x).symm
      · calc p.totalDegree ≤ n := hp_deg
          _ = 2 * (n / 2) + n % 2 := by omega
          _ ≤ 2 * n := by omega
    case compl =>
      intro x hx
      simp only [acc, hx]
      norm_num
    case sound =>
      intro x hx
      simp only [acc, hx]
      norm_num

/-!
## Approximate Degree

**Standard Definition** (Nisan-Szegedy 1994):
The ε-approximate degree of f, denoted deg_ε(f), is the minimum degree d
such that there exists a polynomial p with:
  |p(x) - f(x)| ≤ ε for all x ∈ {0,1}ⁿ

The approximate degree deg̃(f) uses ε = 1/3 (matches bounded error).
-/

/-- ε-approximating polynomial for Boolean function f. -/
def IsApproximating {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (f : Input n → Bool) (ε : ℝ) : Prop :=
  ∀ x : Input n, |MvPolynomial.eval (toReal x) p - (if f x then 1 else 0)| ≤ ε

/--
ε-approximate degree of f: minimum degree of an ε-approximating polynomial.

deg_ε(f) = min { deg(p) : |p(x) - f(x)| ≤ ε for all x }

Note: This is noncomputable since it requires searching over all polynomials.
For ε < 0, this returns a meaningless value since no polynomial can ε-approximate.
-/
noncomputable def approxDegree {n : ℕ} (f : Input n → Bool) (ε : ℝ) : ℕ :=
  if h : ε ≥ 0 then
    @Nat.find (fun d => ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ IsApproximating p f ε)
      (Classical.decPred _) (approx_poly_exists f ε h)
  else 0  -- Meaningless for negative ε
where
  /-- Any Boolean function has an approximating polynomial (for ε ≥ 0).
      Proof: The exact polynomial representation (Fourier/ANF) of f has degree ≤ n
      and 0-approximates f, hence ε-approximates for any ε ≥ 0. -/
  approx_poly_exists (f : Input n → Bool) (ε : ℝ) (hε : ε ≥ 0) :
      ∃ d : ℕ, ∃ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ d ∧ IsApproximating p f ε := by
    -- Use the exact multilinear polynomial representation
    obtain ⟨p, hp_deg, hp_eval⟩ := boolean_multilinear_representation f
    use n, p
    constructor
    · exact hp_deg
    · -- p exactly represents f, so |p(x) - f(x)| = 0 ≤ ε
      intro x
      rw [hp_eval]
      simp only [sub_self, abs_zero]
      exact hε

/--
**Standard Approximate Degree**: deg̃(f) = deg_{1/3}(f)

Why ε = 1/3? Matches bounded-error quantum computation:
- Accept YES with prob ≥ 2/3 = 1 - 1/3
- Accept NO with prob ≤ 1/3

Any polynomial achieving this is a "1/3-approximation" of f.
The minimum degree of such polynomials is deg̃(f).
-/
noncomputable def stdApproxDegree {n : ℕ} (f : Input n → Bool) : ℕ :=
  approxDegree f (1/3 : ℝ)

/-!
## The Polynomial Method

**Main Theorem** (Beals et al. 1998):
For any Boolean function f : {0,1}ⁿ → {0,1}:
  Q(f) ≥ deg̃(f) / 2

Proof idea:
1. Any T-query algorithm has acceptance probability that is degree-2T polynomial
2. For bounded-error algorithm, this polynomial ε-approximates f with ε = 1/3
3. Therefore 2T ≥ deg̃(f), so T ≥ deg̃(f)/2
-/

/--
**Axiom: Polynomial Method Lower Bound** (Beals et al. 1998):
Quantum query complexity is at least half the approximate degree.

Q(f) ≥ ⌈deg̃(f) / 2⌉

**Proof sketch** (not formalized):
1. Any T-query quantum algorithm has acceptance probability that is a
   degree-2T multivariate polynomial in the input bits (follows from
   unitary evolution and measurement probability being degree-2 in amplitudes)
2. For bounded-error algorithms, this polynomial 1/3-approximates f
3. Therefore 2T ≥ deg̃(f), so T ≥ deg̃(f)/2

**Standard Reference**: R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf,
"Quantum Lower Bounds by Polynomials", FOCS 1998, J. ACM 2001.
-/
axiom polynomial_method_lower_bound {n : ℕ} (f : Input n → Bool) :
    queryComplexity f ≥ (stdApproxDegree f + 1) / 2

/--
**Corollary of Polynomial Method**: To prove Q(f) ≥ k, show deg̃(f) ≥ 2k.

Follows directly from polynomial_method_lower_bound:
  Q(f) ≥ ⌈deg̃(f)/2⌉ ≥ ⌈2k/2⌉ = k
-/
theorem query_lower_bound_from_approx_degree {n : ℕ} (f : Input n → Bool) (k : ℕ)
    (h : stdApproxDegree f ≥ 2 * k) :
    queryComplexity f ≥ k := by
  have hpm := polynomial_method_lower_bound f
  omega

end QuantumQuery
