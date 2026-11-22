# Step 7: the bottom of the gain bound

2026-11-22

[Back to step 6](step6-inputs-chain.md) · [Back to the
README](../README.md)

[Step 6](step6-inputs-chain.md) followed the gain bound to the input
structure `DivInputsR`, whose fields carry the divisor inequality. This
step follows those fields until each one is either *proved* or
*defined*. Paths are relative to `src/` at `40e56bab`. Each level was
found with a graph query: which declarations in the cone call a
structure’s constructor `.mk`, or which theorems conclude a given
predicate.

## Summary

The divisor inequality in `divClausesR_of` combines three kinds of
input:

| Input | How it is obtained | Kind |
|----|----|----|
| `L3main`: $\sum_j \ell_3(j) \le \sum_j \sum_\rho p_j w_{j\rho} \log\Omega + E_{l3}$ | `levelThree_bound_closed`, after rewriting with `ClosedScale3.l3m` | **holds by definition**: the scale is defined so that both sides are equal |
| `boundsMu`: the dual slope $\mu_{CC}$ is at most $\mathrm{meanLog}\,\kappa + \sum_j \ell_3(j) + \ldots$ | `Formalism.DivisorInequality.slope_bounds` | **a proved theorem** of the geometry of numbers |
| Gram, index and twisted-sum bounds (`bi`, `biv`, `twisted_third_sum_le`, `borderedMinorImage`) | named lemmas such as `places_ell_weighted_sum_le_one` and `gram_valuation_le_extended` | **proved** |
| `Q`, `deQ`, `la_le`, `constant_ge_twenty_eight`, `eig6` | fields of `ArithAt`, proved in `arithAt_scale3` and `arithmetic_fixed_scale` from the definitions of the scale | **arithmetic on defined constants** |

## `L3main` holds by definition

`ArithAt.l3` asks for $E_{l3}$ with

$$\sum_j \ell_3(j) \le \sum_j \sum_\rho p_j \, w_{j\rho} \log\Omega + E_{l3}.$$

`arithAt_scale3` supplies it with `levelThree_bound_closed`
(`Formalism/LocalToGlobal/Divisibility/EigenvalueSumLeClosedOf.lean`).
That proof rewrites $\ell_3(j) = \ell_{3m}(j) + C \ell_{3u}$ with
`hZ.l3m`, a field of `ClosedScale3`:

``` lean
structure ClosedScale3 ... : Prop where
  l3m : ∀ Zs j, (Zsc Zs).l3m j = ∑ ρ, ((k + (j+1) - 1) - (m - (j+1))) * Nd.w (j+1) ρ * Nd.logOm
  l3u : ∀ Zs, (Zsc Zs).l3u = Nd.B0 * Real.log (Real.log Nd.sc.x)
  ...
```

The scale that is used, `ZscFix3`, is constructed with these values, and

``` lean
theorem closedScale3_fix ... : ClosedScale3 A3 Nd eJz Nc (ZscFix3 A3 P0 ψ0 Nd eJz Nc Cf) :=
  ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
```

So the level-three quantity $\ell_{3m}$ is *defined* to be the main-term
sum, and `L3main` compares a quantity with itself. This is the same
pattern as the height equation `hExpl6` that Nielsen and nomad421
discuss. It is not vacuous, because the inequality is true. It is a
choice of definition, and it moves the content into the statement that
uses $\ell_3$: `boundsMu`.

## `boundsMu` is a proved theorem

``` lean
theorem boundsMu : BoundsMu := slope_bounds          -- Formalism/DivisorInequality/BaseLevelBoundsWithCovolume.lean
```

`slope_bounds`
(`Formalism/DivisorInequality/DivisorInequalityProofs/BaseLevelBoundsWithCovolumeHolds.lean`)
proves `BoundsMu`, a universally quantified statement with about sixty
hypotheses on a number field $K$, lattices over $\mathcal{O}_K$, their
Gram matrices and local data. It calls `divisor_bounds_chain_weak` and
the identities `dual_lattice_measure` and `log_covolume_slope_mu`. Its
conclusion bounds the dual slope of a lattice by the mean log of the
archimedean norms, the level-three terms, and local error terms.

The dependency graph measures its cone:

| Quantity | Value |
|----|----|
| project declarations in the cone of `slope_bounds` | 720 |
| share of the proof term | 0.05% |
| dependencies on Nielsen’s four witnesses | 0 |
| definitions with body `True` in the cone | 0 |
| theorems in the cone that use analytic notions from Mathlib | 0 |
| most used Mathlib notions | `Matrix.det`, `NumberField.RingOfIntegers`, `NumberField.InfinitePlace`, `IsDedekindDomain.HeightOneSpectrum`, `Module.Free` |

This is the first point on the gain side where the estimate is a theorem
with its own proof, and not a field passed in from above. It is geometry
of numbers over number fields, a small and self-contained piece. It
contains no analysis.

## What follows for the gain bound

The gain bound is the combination of:

1.  a geometry-of-numbers slope inequality (`slope_bounds`), which is
    proved;
2.  definitions that make the level-three terms equal to the main term
    of the explicit formula (`ClosedScale3`, by `rfl`);
3.  local bounds on Gram matrices, indices and twisted sums, which are
    proved by named lemmas;
4.  hypotheses on the lattice data, the binders of `BoundsMu` (`hLB`,
    `hG`, `hH`, `hP`, …), which the caller supplies through
    `DivInputsDef3`.

Items 1 to 3 have no connection to primes or L-functions. The connection
to the arithmetic must come through item 4: the lattices and their local
data are built from the host and the family. Their slopes then compare
to the prime sum through the record of step 5. The Riemann Hypothesis
strength of the gain bound therefore sits in the *construction of the
lattices from the arithmetic data*, together with the claim that the
main term $\sum_\rho p_j w_{j\rho} \log\Omega$ is the right one. Neither
of these has been read.

## Where the trace stands

| Side | Reached | Status |
|----|----|----|
| Gain bound | `slope_bounds`, a proved lattice theorem, plus definitions by `rfl` | bottom reached for the inequality. The source of the lattice data has not been read |
| Loss bound | `losses_of_small_share_weight` from `LinkG` | not followed |
| Host analytic data | `QH.pairEx` from zero-density and mean-square bounds | read in the side branch of the semantic trace |

The next code to read is the construction of the lattices (`Nu`, `RR`,
the Gram matrices `XE`, `Xc`) from the host and the family, and how
their slopes relate to primes. On the gain side, this construction is
where the link between geometry of numbers and the primes has to be
made.
