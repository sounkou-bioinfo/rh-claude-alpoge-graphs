# Step 6: the chain of input structures, and a census of the proof

2026-11-22

[Back to step 5](step5-record.md) · [Back to the README](../README.md)

[Step 5](step5-record.md) reduced the bound with the strength of the
Riemann Hypothesis to a loss bound and a gain bound. These are proved in
`linkCore` from hypotheses on a family `FamP`. This step follows the
gain bound down with the dependency graph. It then measures the whole
proof to show where its mass is. Paths are relative to `src/` at
`40e56bab`.

## Method

Each step down is found with one query on the graph: which declarations
in the cone of `riemannHypothesis` use a given predicate, or which ones
call a structure’s constructor `.mk`. The source is then read at that
declaration. The graph queries use recursive SQL in DuckDB. The DuckPGQ
property-graph extension does not load in the DuckDB version used.

## The gain bound, followed down

The gain bound needs the divisor inequality, the clause of `LinkDIV_at`
(`Formalism/SharpRestriction/GlobalTheoremInputs.lean`) that reads

$$\mu_{\mathrm{dual}} + h(u) - F_o \le \mathrm{MAIN}(u) + \text{small}.$$

| Level | Declaration | What it does | The clause comes from |
|----|----|----|----|
| 1 | `linkDIV_at_words` | assembles `LinkDIV_at` | `(hW u).2.2`, a field of `WordFacts` |
| 2 | `wordFacts_of` | proves `WordFacts` by `linarith` | `c3 : μ_C − κ + h_u − F_o ≤ rhs` and `tR : rhs ≤ MAIN + small` |
| 3 | `wordFacts_of_clauses` | supplies `c3` | clause 3 of `DivClausesR` |
| 4 | `divClausesR_of` (`Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`) | proves `DivClausesR` | fields of an input structure `I : DivInputsR`: `L3main`, `twisted_third_sum_le`, `boundsMu`, the passage inequality `deQ` |
| 5 | `DivisionPackageFace.ofOpen` (`Formalism/LocalToGlobal/Divisibility/RecBridgeMkF.lean`) | builds the package | takes `inp : ∀ u, DivInputs0R …` and `H : ∀ u, NumFacts …` **as parameters** |
| 6 | `DivisionPackageColumns.ofTied` | the only user of `ofOpen` in the cone | not read |

At level 1, the rewrite `rw [hh u, hh u']` and the step `exact h5 u u'`
are the lines that nomad421’s note quotes. They are in the same lemma,
but they prove a different clause, the comparison of $h$ between two
words. The divisor inequality comes from `WordFacts`.

Each level that was read has the same form. The theorem takes a
structure of input inequalities and combines the inequalities by
`linarith`, `nlinarith` or rewriting. The numerical content is in the
structure’s fields. Those fields arrive as parameters from the level
above. The proofs at these levels are correct and short. They do not
create the estimate. In this part of the proof, the estimate is a field
of a structure that is passed upward until a construction supplies it.
The construction has not been reached.

`RecNums` (`Formalism/LocalToGlobal/Divisibility/Inputs.lean`) shows the
form of these records. It has about 40 real-valued fields and two
inequality fields:

``` lean
weight_height_sum_le : ∀ j ρ, (∑ i, ph (ν j ρ i)) - logH j ρ ≤ (if ρ ∈ TT then ph (aT ρ) else 0) + eE j ρ
weight_sum_eq : ∀ j ρ, (∑ i, ν j ρ i) = (if ρ ∈ TT then aT ρ else 0) + k * w j ρ + δ j ρ
```

`rhs` is a closed expression in these fields. `tR` asks that it is at
most $\mathrm{MAIN}(u)$ plus small terms, so that the record matches the
arithmetic.

## Census of the proof

| Quantity                                             | Value         |
|:-----------------------------------------------------|:--------------|
| project theorems in the cone                         | 1,067,052     |
| their proof-term nodes                               | 2,039,022,780 |
| theorems using an analytic Mathlib notion directly   | 34,374        |
| theorems using L-functions or zeta directly          | 674           |
| theorems using the prime sum ASK directly            | 15            |
| share of theorem mass in the 10,000 largest theorems | 23.2%         |

The proof has 1,067,052 project theorems, with 2,039,022,780 proof-term
nodes. These counts show where the content can be:

- **Arithmetic is rare.** 34,374 theorems (3%) use any analytic notion
  from Mathlib directly: von Mangoldt, L-series, zeta, derivatives,
  integrals, limits, summability. 674 use L-functions or zeta. 15 use
  the prime sum `ASK` directly. The rest work on the project’s own
  structures: lattices, frames, records and families.
- **The mass is spread.** The 10,000 largest theorems hold 23.2% of the
  theorem mass. No single theorem or small group of theorems holds the
  proof.
- **The largest theorems are transport.** They carry a structure across
  an identification of two copies of the data. They work by case
  analysis and `subst`, and they do no analysis.

| Theorem | Namespace | Proof-term nodes |
|:---|:---|:---|
| `lam_copy` | `GlobalTheory.HeightCounting.SideCopy.LamCopy` | 5,538,153 |
| `sigSpan_copy` | `GlobalTheory.HeightCounting.SideCopy` | 4,598,215 |
| `goodTw_transfer` | `GlobalTheory.TwistChoice` | 2,507,534 |
| `fullRk_basisOf_transfer` | `GlobalTheory.TwistChoice` | 2,327,659 |
| `heckeTie_of_same` | `GlobalTheory.TwInputs.Move` | 2,304,825 |
| `ampLimit` | `Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim` | 2,167,688 |
| `same_basic` | `GlobalTheory.TwistChoice` | 2,132,966 |
| `move_xd` | `GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations` | 2,033,225 |
| `diff_key` | `Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim` | 1,525,941 |
| `listPin_copy` | `GlobalTheory.HeightCounting.Up.ListCarry` | 1,454,964 |
| `ac_le` | `Formalism.L2.SG.Pf.CarrierXAll` | 1,406,850 |
| `transfer` | `GlobalTheory.HeightCounting.Rigid` | 1,181,043 |

For example, `lam_copy`
(`Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamCopy.lean`)
states that a `Lam` witness for a frame on `D` gives one for the same
frame on a copy `D'`. Its proof destructs both records and substitutes
the equal fields. The term is large because the records are large, not
because the statement is deep.

## What this shows, and what it does not

The proof is built as a long chain of input structures. The statement
with the strength of the Riemann Hypothesis enters as fields of such
structures, and each layer passes it upward. Reading layer by layer does
not reach the place where a field is proved from arithmetic. The
arithmetic objects themselves appear in only a few percent of the
theorems.

This is the shape of an argument whose essential inequalities are
supplied by the construction of the top-level family (`FamP`, through
the supply of `TopG` and the bundle `HypsAlt`), and not proved where
they are used. It is not evidence of an error. A sound kernel checked
that every field is supplied. It does mean that the place where the
Riemann Hypothesis strength is established is the construction of these
structures. That construction is 60% of the proof term and is spread
over hundreds of thousands of theorems. The next query is: for the
fields `L3main`, `twisted_third_sum_le` and `weight_height_sum_le`,
which declarations construct the values that fill them, and what those
declarations use from Mathlib.

Continued in [step 7](step7-gain-bottom.md), which reaches the bottom of
the gain bound.
