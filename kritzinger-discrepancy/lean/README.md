# Lean 4 formalization of Kritzinger's greedy sequence

The project uses Lean 4.19.0 and mathlib v4.19.0. The manifest pins all
dependency revisions. For the full project, import `Kritzinger.Lp`.
Indices are zero-based, so `Finset.range N` indexes the first (N) points.

| Declaration (in namespace `Kritzinger`) | Result |
| --- | --- |
| `star_discrepancy_from_objective` | The unnormalized star discrepancy is at most `log(2N) + 3/2` for the empty start, directly from the minimization objective in the paper. |
| `finite_Lp` | The unnormalized Lᵖ discrepancy is Oₚ(√log(2N)) for every finite p ≥ 1. |
| `star_discrepancy_from_seed` | Starting with any s points in [0,1], the star bound is `log(2N) + 3 max(1/2,s) + 1` for positive N ≥ s. |
| `finite_Lp_from_seed` | The same Oₚ,ₛ(√log(2N)) estimate holds uniformly over all initial configurations of length s. |
| `chord_bound`, `chord_from_seed` | One-sided chord inequalities for the discrepancy primitive, with factor s + 1 in the seeded bound. |
| `integrated_discrepancy`, `integrated_discrepancy_from_seed`, `tent_bound` | Uniform integrated discrepancy bounds, and the empty-start upper tent bound. |

The hypotheses allow arbitrary global ties. The seed may contain repeated
points or endpoints. The seeded constants use the length s of the seed,
which gives a coarser bound than using the star discrepancy of the seed
in the paper. The norm uses Lebesgue measure on (0,1], equivalent to [0,1]
for integration. The finite-moment proof sums the rises between successive
large drops, bounds the moments of the neighboring-cell differences, and
uses the cancellation between the two children at each dyadic subdivision.

## Build

With Elan installed, run these commands in the project directory:

```sh
lake exe cache get Mathlib.Analysis.SpecialFunctions.Integrals Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.LinearCombination Mathlib.Tactic.Positivity Mathlib.Tactic.Push Mathlib.Tactic.Ring Mathlib.Analysis.SpecificLimits.Normed Mathlib.Data.Nat.Choose.Bounds Mathlib.Analysis.MeanInequalities Mathlib.Data.Nat.Log Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
lake build
```

The build prints the axioms used by the headline theorems. The expected
list is `propext`, `Classical.choice`, and `Quot.sound`.
