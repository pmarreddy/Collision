/-
# The Polynomial Method for Collision Lower Bounds

Standard techniques from approximation theory used to prove lower bounds
on approximate degree, which then imply quantum query lower bounds.

## Key Techniques

1. **Symmetrization** (Minsky-Papert 1969): For symmetric functions,
   reduce multivariate polynomials to univariate in Hamming weight.

2. **Chebyshev Polynomials**: Optimal growth rate outside [-1,1],
   used to bound how well low-degree polynomials approximate step functions.

3. **Paturi's Lemma** (1992): Bounds on approximating OR function,
   extended by Aaronson for collision.

## References
- Minsky-Papert, "Perceptrons" (1969) - Symmetrization
- Paturi, "On the degree of polynomials that approximate symmetric Boolean functions" (1992)
- Aaronson, "Quantum Lower Bound for the Collision Problem" (2002)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

import Collision.QuantumQuery

namespace PolynomialMethod

open Polynomial QuantumQuery

/-!
## Symmetric Functions and Symmetrization

A Boolean function is symmetric if it depends only on the Hamming weight
(number of 1s) in the input, not on the positions of those 1s.
-/

/-- Hamming weight: number of true bits in input. -/
def hammingWeight {n : ℕ} (x : Input n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/--
A Boolean function is **symmetric** if it depends only on Hamming weight.

**Standard Definition**: f is symmetric iff f(x) = f(y) whenever |x| = |y|
where |x| denotes Hamming weight.
-/
def IsSymmetric {n : ℕ} (f : Input n → Bool) : Prop :=
  ∀ x y : Input n, hammingWeight x = hammingWeight y → f x = f y

/-- Hamming weight of canonical input (first k bits true) equals min k n. -/
lemma hammingWeight_canonical (n k : ℕ) :
    hammingWeight (fun i : Fin n => decide (i.val < k)) = min k n := by
  simp only [hammingWeight, decide_eq_true_eq]
  -- Count {i : Fin n | i.val < k} = min k n
  have : (Finset.univ.filter (fun i : Fin n => i.val < k)).card =
         (Finset.range (min k n)).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_range, Nat.lt_min]
      exact ⟨hi, i.isLt⟩
    · intro i₁ _ i₂ _ h
      exact Fin.val_injective h
    · intro b hb
      simp only [Finset.mem_range, Nat.lt_min] at hb
      exact ⟨⟨b, hb.2⟩, by simp [hb.1], rfl⟩
  rw [this, Finset.card_range]

/-- Hamming weight is bounded by n. -/
lemma hammingWeight_le (n : ℕ) (x : Input n) : hammingWeight x ≤ n := by
  simp only [hammingWeight]
  calc (Finset.univ.filter (fun i => x i = true)).card
      ≤ Finset.univ.card := Finset.card_filter_le Finset.univ (fun i => x i = true)
    _ = n := Finset.card_fin n

/--
For a symmetric function, there exists a univariate function g : ℕ → Bool
such that f(x) = g(|x|).
-/
theorem symmetric_univariate {n : ℕ} (f : Input n → Bool) (hf : IsSymmetric f) :
    ∃ g : ℕ → Bool, ∀ x : Input n, f x = g (hammingWeight x) := by
  -- Define g(k) as f applied to the canonical input of weight k
  use fun k => f (fun i => decide (i.val < k))
  intro x
  -- f(x) = f(canonical_{|x|}) by symmetry
  apply hf
  -- Show: hammingWeight x = hammingWeight canonical
  rw [hammingWeight_canonical]
  -- hammingWeight x = min (hammingWeight x) n
  -- Since hammingWeight x ≤ n, min = hammingWeight x
  rw [min_eq_left (hammingWeight_le n x)]

/-!
## Symmetrization Lemma (Minsky-Papert 1969)

Classical result from computational learning theory.
-/

/-- The set of all inputs of a given Hamming weight. -/
def inputsOfWeight (n k : ℕ) : Finset (Input n) :=
  Finset.univ.filter (fun x => hammingWeight x = k)

/-- Number of inputs of Hamming weight k is C(n,k). -/
lemma card_inputsOfWeight (n k : ℕ) (hk : k ≤ n) :
    (inputsOfWeight n k).card = Nat.choose n k := by
  -- Establish bijection with k-element subsets of Fin n
  unfold inputsOfWeight hammingWeight
  -- Map x : Input n to the set {i | x i = true}
  -- This is a bijection from inputs of weight k to k-subsets of Fin n
  have hpow := Finset.card_powersetCard k (Finset.univ : Finset (Fin n))
  rw [Finset.card_univ, Fintype.card_fin] at hpow
  rw [← hpow]
  apply Finset.card_bij
    (fun x _ => Finset.univ.filter (fun i => x i = true))
  -- Membership: image is in powersetCard k
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hx.2⟩
  -- Injectivity: different inputs give different sets
  · intro x₁ _ x₂ _ heq
    funext i
    have hmem : (i ∈ Finset.univ.filter (fun j => x₁ j = true)) ↔
                (i ∈ Finset.univ.filter (fun j => x₂ j = true)) := by rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    cases hx₁' : x₁ i <;> cases hx₂' : x₂ i <;> simp_all
  -- Surjectivity: every k-subset comes from some input
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    refine ⟨fun i => decide (i ∈ s), ?_, ?_⟩
    · -- Show the constructed input has weight k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      convert hs.2 using 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    · -- Show the image is s
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- Average of a polynomial over inputs of given Hamming weight. -/
noncomputable def avgOverWeight {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) : ℝ :=
  if h : (inputsOfWeight n k).card > 0 then
    (∑ x ∈ inputsOfWeight n k, MvPolynomial.eval (toReal x) p) / (inputsOfWeight n k).card
  else 0

/--
**Axiom: Symmetrization Lemma** (Minsky-Papert, 1969)

Any multivariate polynomial can be symmetrized to a univariate polynomial
of the same degree, preserving averages over Hamming weight classes.

**Exact Statement**: For p : ℝ[x₁,...,xₙ] of degree d, there exists
q : ℝ[k] of degree ≤ d such that for all k ∈ {0,...,n}:
  E_{|x|=k}[p(x)] = q(k)
where the expectation is uniform over inputs of Hamming weight k.

**Key Application**: For symmetric Boolean functions, this reduces
analyzing multivariate approximating polynomials to univariate ones.
If p ε-approximates a symmetric f, then q ε-approximates the univariate
representation of f.

**Standard Reference**: M. Minsky and S. Papert, "Perceptrons" (1969), Chapter 3.
Also: Beals et al., "Quantum Lower Bounds by Polynomials" (1998), uses this.
-/
axiom symmetrization {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
      ∀ k : ℕ, k ≤ n →
        -- q(k) equals the average of p over inputs of Hamming weight k
        q.eval (k : ℝ) = avgOverWeight p k

/-!
## Chebyshev Polynomials

The Chebyshev polynomial Tₙ(x) is the unique polynomial satisfying:
- Tₙ(cos θ) = cos(nθ)
- |Tₙ(x)| ≤ 1 for x ∈ [-1, 1]
- Tₙ has the fastest growth outside [-1, 1] among degree-n polynomials
  bounded by 1 on [-1, 1]

This makes Chebyshev polynomials the key tool for proving that low-degree
polynomials cannot approximate step functions well.
-/

/-- Chebyshev polynomial of first kind. -/
noncomputable def chebyshevT (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.T ℝ n

/-- Chebyshev polynomials are bounded by 1 on [-1, 1].
    Proof: For x ∈ [-1,1], write x = cos(θ) for θ ∈ [0,π].
    Then T_n(x) = T_n(cos θ) = cos(nθ), and |cos(nθ)| ≤ 1. -/
theorem chebyshev_bounded (n : ℕ) :
    ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |Polynomial.eval x (chebyshevT n)| ≤ 1 := by
  intro x hx
  -- x ∈ [-1, 1] means there exists θ ∈ [0, π] with x = cos θ
  -- Use that cos is surjective from [0, π] onto [-1, 1]
  have hsurj := Real.surjOn_cos
  rw [Set.SurjOn] at hsurj
  obtain ⟨θ, hθ_mem, hx_eq⟩ := hsurj hx
  -- T_n(cos θ) = cos(n * θ)
  simp only [chebyshevT]
  rw [← hx_eq]
  -- Use T_real_cos which works for integers; cast n to ℤ
  have h := Polynomial.Chebyshev.T_real_cos θ (n : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h]
  -- |cos(n * θ)| ≤ 1
  exact Real.abs_cos_le_one _

/--
**Axiom: Chebyshev Degree** (Classical Analysis)

The n-th Chebyshev polynomial T_n has degree exactly n.

This follows from the recurrence: T_0 = 1, T_1 = X, T_{n+2} = 2X·T_{n+1} - T_n.
By induction, deg(T_n) = n since leading coefficients don't cancel (leading coeff = 2^{n-1} for n ≥ 1).

Not currently in Mathlib; would require proof via the recurrence relation.
-/
axiom chebyshev_degree (n : ℕ) : (chebyshevT n).natDegree = n

/-!
## Markov Brothers' Inequality

Classical result from approximation theory (A.A. Markov, 1889).
-/

/--
**Axiom: Markov Brothers' Inequality** (A.A. Markov, 1889)

If p is a polynomial of degree ≤ n with ‖p‖_{[-1,1]} ≤ 1,
then ‖p'‖_{[-1,1]} ≤ n².

**Standard Reference**: A.A. Markov, "On a question by D.I. Mendeleev" (1889)
The bound is tight: equality holds for Chebyshev polynomials T_n.

This is a fundamental result in approximation theory, used to bound
how well low-degree polynomials can approximate discontinuous functions.
-/
axiom markov_inequality (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.eval x| ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1) 1 → |p.derivative.eval x| ≤ n^2

/-!
## Paturi's Lemma

Classical result from Boolean function analysis (Paturi, STOC 1992).
-/

/-- The OR function: true iff at least one input bit is true. -/
def orFunction {n : ℕ} (x : Input n) : Bool :=
  decide (∃ i : Fin n, x i = true)

/-- OR is a symmetric function. -/
theorem or_symmetric {n : ℕ} : IsSymmetric (orFunction (n := n)) := by
  intro x y hxy
  -- OR(x) = true iff hammingWeight x > 0
  -- So OR(x) = OR(y) when hammingWeight x = hammingWeight y
  simp only [orFunction, decide_eq_decide]
  -- Both directions: exists a true bit iff Hamming weight > 0
  have hx_pos : (∃ i, x i = true) ↔ hammingWeight x > 0 := by
    simp only [hammingWeight, Finset.card_pos, Finset.filter_nonempty_iff,
               Finset.mem_univ, true_and]
  have hy_pos : (∃ i, y i = true) ↔ hammingWeight y > 0 := by
    simp only [hammingWeight, Finset.card_pos, Finset.filter_nonempty_iff,
               Finset.mem_univ, true_and]
  rw [hx_pos, hy_pos, hxy]

/--
**Axiom: Paturi's Theorem** (Paturi, STOC 1992)

The approximate degree of OR_n is Θ(√n).

**Exact Statement**: For the OR function on n bits,
  deg̃_{1/3}(OR_n) = Θ(√n)

More generally, for any symmetric Boolean function f:
  deg̃(f) = Θ(√(n · (ℓ₀(f) + ℓ₁(f))))
where ℓ₀, ℓ₁ measure how far from constant f is at the boundaries.

For OR: ℓ₀ = 0, ℓ₁ = 1, giving Θ(√n).

**Standard Reference**: R. Paturi, "On the degree of polynomials that
approximate symmetric Boolean functions", STOC 1992, pp. 468-474.
-/
axiom paturi_or_lower_bound (n : ℕ) (hn : n > 0) :
    ∃ c : ℝ, c > 0 ∧ (stdApproxDegree (orFunction (n := n)) : ℝ) ≥ c * Real.sqrt n

/-!
## Collision-Specific Analysis

The main technical result from Aaronson's 2002 paper.

**Setup**: For a function f : [N] → [R], the collision pattern encodes
which pairs of elements have the same image. Specifically:
- Index pairs (i,j) with i < j by m = 0, 1, ..., N(N-1)/2 - 1
- Bit x_m = 1 iff f(i) = f(j) for the m-th pair
- The collision function outputs 1 iff any x_m = 1

This is exactly the OR function on N(N-1)/2 bits, but the key insight
from Aaronson is that the *promise* (f is 1-to-1 or 2-to-1) restricts
which inputs are valid, enabling a lower bound analysis via symmetrization.
-/

/-- Number of pairs for N elements: N(N-1)/2 -/
def numPairs (N : ℕ) : ℕ := N * (N - 1) / 2

/--
The collision indicator on N elements: given the collision pattern
(which pairs collide), output true iff any collision exists.

Input: For each pair (i,j) with i < j, bit indicates if f(i) = f(j).
Output: true iff at least one pair collides.

This is OR on numPairs(N) bits.
-/
def collisionIndicator (N : ℕ) (x : Input (numPairs N)) : Bool :=
  decide (∃ idx : Fin (numPairs N), x idx = true)

/-- The collision indicator is symmetric (depends only on number of collisions). -/
theorem collisionIndicator_symmetric (N : ℕ) :
    IsSymmetric (collisionIndicator N) := by
  intro x y hxy
  simp only [collisionIndicator, decide_eq_decide]
  -- Both are true iff Hamming weight > 0
  have hx : (∃ i, x i = true) ↔ hammingWeight x > 0 := by
    simp only [hammingWeight, Finset.card_pos, Finset.filter_nonempty_iff,
               Finset.mem_univ, true_and]
  have hy : (∃ i, y i = true) ↔ hammingWeight y > 0 := by
    simp only [hammingWeight, Finset.card_pos, Finset.filter_nonempty_iff,
               Finset.mem_univ, true_and]
  rw [hx, hy, hxy]

/-!
## Promise Approximate Degree

For promise problems, we only need to approximate the function on valid inputs.
For collision: weight-0 inputs (1-to-1) and weight-n inputs (2-to-1).

This is DIFFERENT from stdApproxDegree which requires approximation on ALL inputs.
- stdApproxDegree(collisionIndicator) = Θ(n) [it's OR on ~2n² bits, so Θ(√(2n²)) = Θ(n)]
- promiseApproxDegree(collision) = Θ(n^{1/3}) [only weight 0 vs weight n]

The n^{1/3} bound is Aaronson's key contribution.
-/

/--
**Promise Approximation** (distinct from standard approximation).

Standard `IsApproximating`: must approximate f on ALL 2^m inputs.
Promise `IsPromiseApproximating`: only needs to work on VALID inputs (weight 0 or n).

For collision:
- Weight 0 = 1-to-1 function (no collisions) → output ≤ ε
- Weight n = 2-to-1 function (n collisions) → output ≥ 1-ε
- Other weights are invalid (not 1-to-1 or 2-to-1), so ignored

This weaker requirement gives: promiseApproxDegree = Θ(n^{1/3}) vs stdApproxDegree = Θ(n).
Still sufficient for quantum lower bounds since algorithms only see valid inputs.
-/
def IsPromiseApproximating {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (n : ℕ) (ε : ℝ) : Prop :=
  -- Bounded in [0,1] on all inputs (for quantum algorithm interpretation)
  (∀ x : Input m, 0 ≤ MvPolynomial.eval (toReal x) p ∧ MvPolynomial.eval (toReal x) p ≤ 1) ∧
  -- On all-zeros input (weight 0): output close to 0
  (∀ x : Input m, hammingWeight x = 0 → MvPolynomial.eval (toReal x) p ≤ ε) ∧
  -- On weight-n inputs: output close to 1
  (∀ x : Input m, hammingWeight x = n → MvPolynomial.eval (toReal x) p ≥ 1 - ε)

/--
**Promise Approximate Degree** for collision.

Key insight: This is MUCH SMALLER than standard approximate degree.
- stdApproxDegree(OR on m bits) = Θ(√m) by Paturi
- promiseApproxDegree(collision) = Θ(n^{1/3}) by Aaronson

Why? Standard degree must work on all 2^m inputs.
Promise degree only needs weight-0 vs weight-n distinction.

Parameters:
- m = number of pair-bits (≈ 2n²)
- n = collision count for 2-to-1 case
- ε = approximation error (use 1/3 for bounded error)
-/
noncomputable def promiseApproxDegree (m n : ℕ) (ε : ℝ) : ℕ :=
  if h : ε > 0 ∧ ε < 1/2 ∧ n > 0 then
    @Nat.find (fun d => ∃ p : MvPolynomial (Fin m) ℝ,
      p.totalDegree ≤ d ∧ IsPromiseApproximating p n ε)
      (Classical.decPred _)
      (promise_approx_exists m n ε ⟨h.1, h.2.1⟩ h.2.2)
  else 0
where
  promise_approx_exists (m n : ℕ) (ε : ℝ) (hε : ε > 0 ∧ ε < 1/2) (hn : n > 0) :
      ∃ d : ℕ, ∃ p : MvPolynomial (Fin m) ℝ,
        p.totalDegree ≤ d ∧ IsPromiseApproximating p n ε := by
    -- The exact polynomial for OR works (outputs 0 at weight 0, 1 at weight ≥ 1)
    -- Use orFunction which has type Input m → Bool
    obtain ⟨p, hp_deg, hp_eval⟩ := boolean_multilinear_representation (orFunction (n := m))
    use m, p
    constructor
    · exact hp_deg
    · constructor
      · -- Boundedness: p(x) ∈ {0, 1} ⊆ [0, 1] for Boolean inputs
        intro x
        rw [hp_eval]
        by_cases h : orFunction x = true
        · simp only [h]; constructor <;> norm_num
        · simp only [h]; constructor <;> norm_num
      · constructor
        · intro x hx
          -- At weight 0: orFunction = false, so p(x) = 0 ≤ ε
          have hor : orFunction x = false := by
            simp only [orFunction, decide_eq_false_iff_not]
            intro ⟨idx, hidx⟩
            have hpos : hammingWeight x > 0 := by
              simp only [hammingWeight, Finset.card_pos, Finset.filter_nonempty_iff]
              exact ⟨idx, Finset.mem_univ _, hidx⟩
            omega
          rw [hp_eval, hor]
          norm_num
          linarith [hε.1]
        · intro x hx
          -- n > 0, so weight n > 0, so orFunction = true
          have hor : orFunction x = true := by
            simp only [orFunction, decide_eq_true_eq]
            by_contra h
            push_neg at h
            have hzero : hammingWeight x = 0 := by
              simp only [hammingWeight, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro idx _
              exact fun hidx => h idx hidx
            omega
          rw [hp_eval, hor]
          norm_num
          linarith [hε.2]

/--
**Axiom: Two-Point Distinguishing Bound** (Standard Approximation Theory)

This is the core approximation-theoretic result used in Aaronson's proof.

**Statement**: For a polynomial q on integers [0, m] that:
- Has |q(k)| ≤ 1 for all k ∈ {0, 1, ..., m}
- Satisfies q(0) ≤ 1/3 and q(k₀) ≥ 2/3 for some k₀

The degree must be at least Ω((k₀ · m / k₀²)^{1/3}) = Ω((m/k₀)^{1/3}).

For collision: m = numPairs(2n) ≈ 2n², k₀ = n
Bound: Ω((2n²/n)^{1/3}) = Ω((2n)^{1/3}) = Ω(n^{1/3})

**Proof outline** (standard approximation theory):
1. Rescale polynomial to [-1, 1]
2. Use Chebyshev polynomial properties: Tₐ grows like cosh(d·√(2ε)) at -1+ε
3. For the polynomial to jump by 1/3 near the boundary, need sufficient degree
4. The relationship m ≈ n², k₀ = n gives the n^{1/3} bound

**References**:
- Cheney, *Introduction to Approximation Theory* (1966)
- Rivlin, *Chebyshev Polynomials* (1990)
- The specific bound derivation follows Aaronson-Shi (2004), but uses only
  standard approximation theory (Chebyshev, Markov)
-/
axiom two_point_distinguishing_bound (m k₀ : ℕ) (hm : m > 0) (hk : k₀ > 0) (hk_le : k₀ ≤ m) :
    ∃ c : ℝ, c > 0 ∧
      ∀ d : ℕ,
        -- If a degree-d polynomial can distinguish 0 from k₀ on [0,m]
        (∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
          q.eval 0 ≤ 1/3 ∧
          q.eval (k₀ : ℝ) ≥ 2/3 ∧
          (∀ k : ℕ, k ≤ m → |q.eval (k : ℝ)| ≤ 1)) →
        -- Then d ≥ c · (m / k₀)^{1/3}
        (d : ℝ) ≥ c * ((m : ℝ) / (k₀ : ℝ)) ^ (1/3 : ℝ)

/--
**Axiom: Symmetrization Preserves Promise Approximation**

This connects multivariate promise approximation to univariate polynomials.

If a multivariate polynomial p of degree d satisfies:
- p ≤ 1/3 on weight-0 inputs (average)
- p ≥ 2/3 on weight-n inputs (average)

Then there exists a univariate polynomial q of degree ≤ d with:
- q(0) ≤ 1/3
- q(n) ≥ 2/3
- |q(k)| ≤ 1 for all k ∈ [0, m]

This follows from the symmetrization lemma (Minsky-Papert) applied to
bounded polynomials on the Boolean hypercube.
-/
axiom symmetrization_promise {m d : ℕ} (p : MvPolynomial (Fin m) ℝ)
    (hp_deg : p.totalDegree ≤ d)
    (hp_bound : ∀ x : Input m, 0 ≤ MvPolynomial.eval (toReal x) p ∧
                               MvPolynomial.eval (toReal x) p ≤ 1)
    (n : ℕ) (hn : n ≤ m)
    (hp_zero : ∀ x : Input m, hammingWeight x = 0 → MvPolynomial.eval (toReal x) p ≤ 1/3)
    (hp_n : ∀ x : Input m, hammingWeight x = n → MvPolynomial.eval (toReal x) p ≥ 2/3) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ d ∧
      q.eval 0 ≤ 1/3 ∧
      q.eval (n : ℝ) ≥ 2/3 ∧
      (∀ k : ℕ, k ≤ m → |q.eval (k : ℝ)| ≤ 1)

/--
**Theorem: Promise Approximate Degree of Collision** (Aaronson 2002)

This is the central technical result, **derived** from:
1. `symmetrization_promise` (Minsky-Papert 1969)
2. `two_point_distinguishing_bound` (standard approximation theory)

For the collision problem with m = numPairs(2n) ≈ 2n² bits and
promise inputs at weight 0 (1-to-1) and weight n (2-to-1):

  promiseApproxDegree(m, n, 1/3) ≥ c · n^{1/3}

**Proof** (standard approximation theory):
1. m = numPairs(2n) = n(2n-1) ≥ n² for n ≥ 1
2. By symmetrization_promise: any promise-approximating polynomial
   yields a univariate q with q(0) ≤ 1/3, q(n) ≥ 2/3, bounded on [0,m]
3. By two_point_distinguishing_bound: degree(q) ≥ c · (m/n)^{1/3}
4. Since m/n = 2n-1 ≥ n, we get degree ≥ c · n^{1/3}

**Aaronson's contribution**: Recognizing that collision reduces to this
framework, not the approximation theory itself.
-/
theorem collision_promise_degree_lower_bound (n : ℕ) (hn : n > 0) :
    ∃ c : ℝ, c > 0 ∧
      (promiseApproxDegree (numPairs (2 * n)) n (1/3) : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ) := by
  -- Let m = numPairs(2*n) = n(2n-1)
  let m := numPairs (2 * n)
  -- Get the constant from two_point_distinguishing_bound
  have hm_pos : m > 0 := by
    simp only [m, numPairs]
    -- (2n)(2n-1)/2 > 0 when n > 0
    -- (2n)(2n-1) ≥ 2 when n ≥ 1, so /2 ≥ 1
    have h1 : (2 * n) * (2 * n - 1) ≥ 2 := by
      have : 2 * n ≥ 2 := by omega
      have : 2 * n - 1 ≥ 1 := by omega
      calc (2 * n) * (2 * n - 1) ≥ 2 * 1 := Nat.mul_le_mul ‹2 * n ≥ 2› ‹2 * n - 1 ≥ 1›
        _ = 2 := by ring
    exact Nat.div_pos h1 (by norm_num : 2 > 0)
  have hn_le_m : n ≤ m := by
    simp only [m, numPairs]
    have h : (2 * n) * (2 * n - 1) / 2 ≥ n := by
      have h1 : (2 * n) * (2 * n - 1) = 2 * (n * (2 * n - 1)) := by ring
      rw [h1, Nat.mul_div_cancel_left _ (by norm_num : 2 > 0)]
      have h2 : n * (2 * n - 1) ≥ n * 1 := Nat.mul_le_mul_left n (by omega)
      omega
    exact h
  obtain ⟨c, hc_pos, hdist⟩ := two_point_distinguishing_bound m n hm_pos hn hn_le_m
  use c
  constructor
  · exact hc_pos
  · -- Show promiseApproxDegree ≥ c * n^{1/3}
    -- First, handle the case where the conditions for promiseApproxDegree are met
    have hε : (1/3 : ℝ) > 0 ∧ (1/3 : ℝ) < 1/2 := by constructor <;> norm_num
    -- The definition of promiseApproxDegree uses Nat.find when conditions are met
    simp only [promiseApproxDegree]
    have h_cond : (1/3 : ℝ) > 0 ∧ (1/3 : ℝ) < 1/2 ∧ n > 0 := ⟨hε.1, hε.2, hn⟩
    simp only [dif_pos h_cond]
    -- Let d be the promiseApproxDegree
    set d := @Nat.find (fun d => ∃ p : MvPolynomial (Fin m) ℝ,
      p.totalDegree ≤ d ∧ IsPromiseApproximating p n (1/3))
      (Classical.decPred _)
      (promiseApproxDegree.promise_approx_exists m n (1/3) hε hn) with hd_def
    -- By Nat.find_spec, there exists p with degree ≤ d and promise-approximating
    have h_spec := @Nat.find_spec (fun d => ∃ p : MvPolynomial (Fin m) ℝ,
      p.totalDegree ≤ d ∧ IsPromiseApproximating p n (1/3))
      (Classical.decPred _)
      (promiseApproxDegree.promise_approx_exists m n (1/3) hε hn)
    obtain ⟨p, hp_deg, hp_bound, hp_zero, hp_n⟩ := h_spec
    -- Convert 1 - 1/3 to 2/3 in hp_n
    have hp_n' : ∀ x : Input m, hammingWeight x = n → MvPolynomial.eval (toReal x) p ≥ 2/3 := by
      intro x hx
      have h := hp_n x hx
      linarith
    -- Apply symmetrization_promise to get univariate q
    have hp_bound' : ∀ x : Input m, 0 ≤ MvPolynomial.eval (toReal x) p ∧
                                    MvPolynomial.eval (toReal x) p ≤ 1 := hp_bound
    obtain ⟨q, hq_deg, hq_zero, hq_n, hq_bound⟩ :=
      symmetrization_promise p hp_deg hp_bound' n hn_le_m hp_zero hp_n'
    -- Apply two_point_distinguishing_bound
    have hdist_applied := hdist d ⟨q, hq_deg, hq_zero, hq_n, hq_bound⟩
    -- Now we need: d ≥ c * (m/n)^{1/3} implies d ≥ c * n^{1/3}
    -- This follows because m/n = 2n-1 ≥ n (for n ≥ 1)
    have h_m_div_n_ge_n : (m : ℝ) / n ≥ n := by
      simp only [m, numPairs]
      have hn_pos : (n : ℝ) > 0 := by exact_mod_cast hn
      have h1 : (2 * n) * (2 * n - 1) / 2 = n * (2 * n - 1) := by
        have h : (2 * n) * (2 * n - 1) = 2 * (n * (2 * n - 1)) := by ring
        rw [h, Nat.mul_div_cancel_left _ (by norm_num : 2 > 0)]
      rw [h1]
      rw [Nat.cast_mul]
      -- Goal: n * (2n-1) / n ≥ n, i.e., 2n-1 ≥ n (for n ≥ 1)
      have h2 : (↑n * ↑(2 * n - 1) : ℝ) / ↑n = ↑(2 * n - 1) := by
        field_simp
      rw [h2]
      have h3 : (2 * n - 1 : ℕ) ≥ n := by omega
      exact_mod_cast h3
    -- (m/n)^{1/3} ≥ n^{1/3} because m/n ≥ n and x^{1/3} is monotone
    have h_pow_mono : ((m : ℝ) / n) ^ (1/3 : ℝ) ≥ (n : ℝ) ^ (1/3 : ℝ) := by
      apply Real.rpow_le_rpow
      · exact_mod_cast Nat.zero_le n
      · exact h_m_div_n_ge_n
      · norm_num
    calc (d : ℝ) ≥ c * ((m : ℝ) / n) ^ (1/3 : ℝ) := hdist_applied
      _ ≥ c * (n : ℝ) ^ (1/3 : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_pow_mono
          linarith

end PolynomialMethod
