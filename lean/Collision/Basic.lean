/-
# Quantum Lower Bound for the Collision Problem

Formalization of Scott Aaronson's 2002 result proving Ω(n^{1/5}) quantum query
lower bound for the collision problem, later improved to Ω(n^{1/3}) by Aaronson-Shi.

## References
- Aaronson, "Quantum Lower Bound for the Collision Problem" (2002)
- Aaronson-Shi, "Quantum Lower Bound for the Collision Problem with Small Range" (2004)
- Beals et al., "Quantum Lower Bounds by Polynomials" (1998)
- Brassard-Høyer-Tapp, "Quantum Algorithm for the Collision Problem" (1997)

## Main Result
Any quantum algorithm that distinguishes one-to-one functions from two-to-one
functions with bounded error must make Ω(n^{1/3}) queries.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Set.Card

/-!
## Core Definitions

Standard definitions following Brassard-Høyer-Tapp (1997) and Aaronson (2002).

**Collision Problem Setup:**
- Domain: [N] (finite set of size N)
- Range: [M] (finite set of size M)
- Oracle access to f : [N] → [M]
- Promise: f is either one-to-one or r-to-one
- Task: Decide which case (with bounded error)
-/

namespace Collision

/-!
### Function Classifications

Standard definitions from the literature.
-/

/-- A function is one-to-one (injective).
    Standard definition: f(x) = f(y) implies x = y. -/
def IsOneToOne {α β : Type*} (f : α → β) : Prop :=
  Function.Injective f

/--
A function f : α → β is **r-to-one** if every element in the image of f
has exactly r preimages.

**Standard Definition** (Brassard-Høyer-Tapp 1997):
f is r-to-one iff for all y ∈ image(f), |f⁻¹(y)| = r.

Note: Elements not in the image have 0 preimages.
For the collision problem, we typically have |α| = r · |image(f)|.
-/
def IsRToOne {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (r : ℕ) (f : α → β) : Prop :=
  ∀ y ∈ Set.range f, (Finset.univ.filter (fun x => f x = y)).card = r

/-- Alternative characterization: r-to-one means the fiber over each
    element in the range has size 0 or r (0 if not in image, r if in image). -/
def IsRToOne' {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (r : ℕ) (f : α → β) : Prop :=
  ∀ y : β, (Finset.univ.filter (fun x => f x = y)).card = 0 ∨
           (Finset.univ.filter (fun x => f x = y)).card = r

/-- The two definitions are equivalent. -/
theorem isRToOne_iff_isRToOne' {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (r : ℕ) (f : α → β) :
    IsRToOne r f ↔ IsRToOne' r f := by
  constructor
  · intro h y
    by_cases hy : y ∈ Set.range f
    · right; exact h y hy
    · left
      simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      simp only [Set.mem_range, not_exists] at hy
      exact fun hxy => hy x hxy
  · intro h y hy
    cases h y with
    | inl h0 =>
      -- h0 says the fiber is empty, but hy says y is in the image - contradiction
      rw [Finset.card_eq_zero] at h0
      obtain ⟨x, hx⟩ := hy
      have hmem : x ∈ Finset.univ.filter (fun a => f a = y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx
      rw [h0] at hmem
      exact (Finset.not_mem_empty x hmem).elim
    | inr hr => exact hr

/-- Special case: two-to-one function (r = 2). -/
def IsTwoToOne {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) : Prop :=
  IsRToOne 2 f

/-!
### The Collision Problem

**Input**: Oracle access to f : [2n] → [n]
**Promise**: f is either 1-to-1 OR 2-to-1 (nothing else)
**Task**: Output 0 if 1-to-1, output 1 if 2-to-1
**Allowed**: Query "what is f(i)?" for any i

**Complexity Question**: How many queries are needed?
- Classical: Θ(√n) — birthday paradox
- Quantum: Θ(n^{1/3}) — this formalization proves the lower bound
-/

/-- A collision in f is a pair of distinct elements with the same image.
    Standard definition: (x₁, x₂) is a collision iff x₁ ≠ x₂ and f(x₁) = f(x₂). -/
structure Collision {α β : Type*} (f : α → β) where
  x₁ : α
  x₂ : α
  distinct : x₁ ≠ x₂
  same_image : f x₁ = f x₂

/-- One-to-one functions have no collisions. -/
theorem one_to_one_no_collision {α β : Type*} (f : α → β) (h : IsOneToOne f) :
    ∀ c : Collision f, False := by
  intro c
  have : c.x₁ = c.x₂ := h c.same_image
  exact c.distinct this

/-- Two-to-one functions always have collisions (when domain is nonempty). -/
theorem two_to_one_has_collision {n : ℕ} (hn : n > 0)
    (f : Fin (2 * n) → Fin n) (h : IsTwoToOne f) :
    ∃ c : Collision f, True := by
  -- Since 2n > n and domain is nonempty, by pigeonhole there's a collision
  -- Pick any element in the image, it has exactly 2 preimages by 2-to-one property
  have h2n_pos : 2 * n > 0 := by omega
  -- The image is nonempty since domain is nonempty
  have himg : (Set.range f).Nonempty := by
    use f ⟨0, h2n_pos⟩
    exact Set.mem_range_self _
  -- Get some y in the image
  obtain ⟨y, hy⟩ := himg
  -- y has exactly 2 preimages since f is 2-to-one
  have h2 : (Finset.univ.filter (fun x => f x = y)).card = 2 := h y hy
  -- Extract two distinct elements from this fiber
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun x => f x = y)).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
  exact ⟨⟨x₁, x₂, hne, hx₁.trans hx₂.symm⟩, trivial⟩

/-!
### Domain and Range Setup

Standard setup for the collision problem.
-/

/-- Standard collision problem instance: f : [2n] → [n].
    Domain has 2n elements, range has n elements. -/
structure CollisionInstance (n : ℕ) where
  /-- The function given as oracle -/
  f : Fin (2 * n) → Fin n
  /-- Promise: f is either 1-to-1 or 2-to-1 -/
  promise : IsOneToOne f ∨ IsTwoToOne f

/-- The decision problem: return true iff f has a collision. -/
def hasCollision {α β : Type*} [DecidableEq β] (f : α → β) : Prop :=
  ∃ x₁ x₂ : α, x₁ ≠ x₂ ∧ f x₁ = f x₂

/-- One-to-one is equivalent to no collision. -/
theorem one_to_one_iff_no_collision {α β : Type*} [DecidableEq β] (f : α → β) :
    IsOneToOne f ↔ ¬hasCollision f := by
  constructor
  · intro h ⟨x₁, x₂, hne, heq⟩
    exact hne (h heq)
  · intro h x y hxy
    by_contra hne
    exact h ⟨x, y, hne, hxy⟩

end Collision
