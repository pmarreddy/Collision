# Quantum Lower Bound for the Collision Problem

Lean 4 formalization proving Q(collision) = Θ(n^{1/3}).

## Result

**Theorem:** Any bounded-error quantum algorithm distinguishing 1-to-1 from 2-to-1 functions f : [2n] → [n] requires Ω(n^{1/3}) queries.

Combined with the O(n^{1/3}) upper bound (BHT 1997):

```
Q(collision) = Θ(n^{1/3})
```

Classical algorithms require Θ(√n) queries, giving quantum speedup of n^{1/6}.

## Structure

```
Collision/
├── lean/
│   ├── Collision.lean              -- Root module
│   └── Collision/
│       ├── Basic.lean              -- Function classifications
│       ├── QuantumQuery.lean       -- Query model, approximate degree
│       ├── PolynomialMethod.lean   -- Symmetrization, degree bounds
│       └── MainTheorem.lean        -- Encoding, main theorems
├── docs/
│   ├── AXIOMS.md                   -- Axiom documentation
│   ├── AXIOM_VERIFICATION.md
│   ├── ARCHITECTURE.md
│   └── DEFINITION_VERIFICATION.md
├── scripts/
│   └── install.sh                  -- Installation script
├── lakefile.lean
└── lean-toolchain
```

## Proof

```
T-query quantum algorithm
         ↓
Acceptance is degree-2T polynomial [Beals et al.]
         ↓
Encode collision as Boolean string [Aaronson]
         ↓
Symmetrization → univariate [Minsky-Papert]
         ↓
Approximation theory → deg̃ ≥ Ω(n^{1/3})
         ↓
Q(collision) ≥ Ω(n^{1/3})
```

## Installation

### Prerequisites

- macOS or Linux
- `curl` (for downloading elan)

### Quick Start

```bash
# Clone the repository
git clone https://github.com/pmarreddy/Collision.git
cd Collision

# Run install script (installs Lean 4 + builds project)
./scripts/install.sh
```

### Manual Installation

1. **Install elan** (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Restart shell** or run:
   ```bash
   source ~/.profile  # or ~/.bashrc, ~/.zshrc
   ```

3. **Build the project**:
   ```bash
   lake update   # Download Mathlib (first run takes ~10-15 min)
   lake build    # Build the formalization
   ```

## Build

```bash
lake build Collision
```

## Status

**Complete** — 0 sorries

## Axioms

12 axioms, all standard results:

| Category | Count |
|----------|-------|
| Foundational | 2 |
| Approximation Theory | 6 |
| Query Complexity | 4 |
| **Total** | **12** |

**Derived theorems** (not axioms):
- `collision_promise_degree_lower_bound`
- `polynomial_method_implies_quantum_lower_bound`

See [docs/AXIOMS.md](docs/AXIOMS.md) for details.

## Key Theorems

- `encoding_indicator_bridge`: Connects oracle to polynomial model
- `collision_promise_degree_lower_bound`: deg̃ ≥ Ω(n^{1/3})
- `polynomial_method_implies_quantum_lower_bound`: Q ≥ Ω(n^{1/3})
- `collision_query_complexity_tight`: Q(collision) = Θ(n^{1/3})

## References

1. Aaronson, ["Quantum Lower Bound for the Collision Problem"](https://arxiv.org/abs/quant-ph/0111102), STOC 2002 — [PDF](https://www.scottaaronson.com/papers/collision.pdf)
2. Aaronson-Shi, ["Quantum Lower Bounds for Collision and Element Distinctness"](https://dl.acm.org/doi/10.1145/1008731.1008735), JACM 2004
3. Brassard-Høyer-Tapp, "Quantum Algorithm for the Collision Problem", 1997
4. Beals et al., "Quantum Lower Bounds by Polynomials", FOCS 1998
5. Minsky-Papert, "Perceptrons", 1969
6. Paturi, "On the degree of polynomials that approximate symmetric Boolean functions", STOC 1992
