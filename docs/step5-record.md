# Step 5: the abstract record and where its inequalities come from

2026-11-22

[Back to the semantic trace](semantic-trace.md) · [Back to the
README](../README.md)

The [semantic trace](semantic-trace.md) stopped at `Deduction.ch_top`.
There the bound with the strength of the Riemann Hypothesis had become
inequalities on an abstract record `Data`, tied to a real prime sum by
the hypothesis `IdentU`. This document follows those hypotheses to their
supply. Paths are relative to `src/` at `40e56bab`. Only code that was
read is described.

## Summary

| Question | Answer | Read |
|----|----|----|
| Is the abstract record honestly tied to the prime sum? | Yes. The concrete record defines `ASK` as the prime sum, and `IdentU` holds by `rfl` | in full |
| Where are the record’s inequalities proved? | In `linkCore`, from hypotheses carried by the family `Fm : FamP eps` | statement and assembly |
| What do the inequalities reduce to? | Two real inequalities: a **loss bound** (prime sum ≤ local gain + small) and a **gain bound** (local gain ≤ main term + small) | statements |
| Is anything vacuous on this path? | No `True` slot was found. One `if … else True` branch is discharged correctly. None of these declarations depends on the four witnesses | read; checked in the graph |
| What is `ErrorFormsWeakWindowsFalse`? | A proposition that is defined and never proved. It is not in the compiled proof | in full; checked in the export |
| Where is the strength now? | In the hypotheses of the family `FamP`: `LinkG`, `LinkDIV`, `FrameF`, slope and lattice bounds | not read |

## The chain from `CoreAtH` to the record

`CoreAtH` is built by `tiedCore_of_chainTied` from `ChainTied`
(`Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean`).
`ChainTied` asserts that a record `Dd`, constants `C`, and windows exist
with these properties:

``` lean
IdentU Dd id D N ell TT a w eT eP ∧
SizeData₂ Dd C Xpp ∧ ErrWindows Dd C Xpp eK K ∧ BNBoundsU Dd T2 ∧ ...
```

`ChainTied` is supplied by `linkCore`
(`Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean`,
515 lines). Its statement:

``` lean
theorem linkCore (Fm : FamP eps) (Cabs CH eL C5 c6 : ℝ) ...
    (hCount : CountF Fm) (hSM : SlopesMF Fm) (hSN : SlopesNF Fm) (hLat : LatF Fm) (hNodes : NodesF Fm)
    (hFr : FrameF Fm CH) (hLoss : LossFS Fm eL) (hChar : CharF Fm) (hWin : WinF Fm)
    (cTT : ChosenTT Fm) (cQD : ChosenQD Fm C5) (cTh : ChosenThin Fm c6) (lI : LinkIRR Fm) (lD : LinkDIV Fm Cabs CH) :
    ∃ K cHH eK CL x0 : ℝ, ∀ x ≥ x0, x ∈ Fm.Win → ChainTied Fm Cabs eL K cHH eK CL x
```

It instantiates the record with `M.data …` and proves each condition
separately (`L1` to `L8`, `liftZP_newton`, `ParameterUpperBound`,
`liftZP_unit`, `E0`, `E1`, `B1`). The proofs of the individual
conditions were not read.

## The record is the arithmetic

The concrete record `M.data`
(`Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`)
fills each field from the family at scale $x$:

| Field | Value |
|----|----|
| `ASK u0` | `∑ t ∈ M.TT, ∑ j, ASK M.AD N (M.a t) t (M.w u0 j)`, **the prime sum itself** |
| `gam` | `Real.eulerMascheroniConstant` |
| `LpL` | `logDerivativeAtOne` of the family, fixed equal to `dlogL D 1` by a field of `SizeData₂` |
| `Ga`, `Fo`, `Ta` | sums over a finite set of places of the local functions `gain`, `F`, `tau` of a `SizeData₂` |
| `d`, `T`, `h`, `muN`, `muMaxN`, `muM`, `muMaxM` | ranks, heights and slopes of lattices in the family’s divisor data |
| `etaBar`, `eBar` | parameters `etaB`, `eB` that `linkCore` chooses |

The tie `IdentU` is proved by `M.ident`. The proof is `rfl` for every
component except the log-derivative component, which is a hypothesis
about `ell`. Because the record’s `ASK` is *defined* as the prime sum,
no equivocation can enter here.

## What the record’s inequalities say

`each_unit_bound_statement`
(`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`)
proves $\mathrm{ASK} - \mathrm{Main} \le$ error. It combines two bounds.

**Loss bound** (`LossBounds`,
`Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean`):

$$\mathrm{ASK}(u_0) - \mathrm{Ga}(u_0) \le C_{\mathrm{Loss}} \, n_T \, m \, b \, x^{e_{\mathrm{Loss}} \varepsilon}$$

The prime sum is at most the local gain `Ga` plus a loss that is small
on the scale of the windows. Its source is `Loss_at` and
`LossesSmallShares`, proved by `losses_of_small_share_weight`
(`Formalism/LocalToGlobal/GlobalTheory/LossRequirementsOfSmallShares.lean`)
from `ChosenTT`, `ChosenBadp` and `LinkG`.

**Gain bound** (`Ga_bound5`, same file as `each_unit_bound_statement`):

$$\mathrm{Ga}(u_0) \le \mathrm{Main}(u_0) + \log |W_{u_0}| + K_0 + \text{(mean of the slope losses)}
+ (1 - \bar\delta)^{-1}\left(\ldots + (\bar\eta + 4\sqrt{\bar e})\, x^{c_{HH}} b\right)$$

It uses the eleven conditions of `SizeData₂`. These include
`HidaSetting` (positivity, and $\bar e \le 1/4$), `DIV` (a degree
inequality for the divisor: `muCC + h − Fo` is at most a sum over the
top characters plus small terms), `HComp`, `Slopes`,
`QuotientSlopeBoundsWith`, `SlopeIneq`, `HHBound` and `FParams`. They
are inequalities about lattices: their slopes, successive minima and
heights.

`ErrWindows` then makes the last term small. Its key clause is
$(\bar\eta + 4\sqrt{\bar e})\, x^{c_{HH}} b \le K x^{\varepsilon} n_T a$.

So the strength of the Riemann Hypothesis is split into two real
inequalities. The prime sum is close to a local gain, and the local gain
is bounded by the main term through Arakelov-type inequalities for
lattices. The geometry in this part of the proof is real: lattice slopes
and divisor degrees. It is not the `anyGeometry` slot.

## `ErrorFormsWeakWindowsFalse`

`Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean` defines

``` lean
def ErrWindowsWeak (D : Data U0 W Top m f) (C : Consts) (Xpp eK K : ℝ) : Prop :=
  ErrWindows0 D C Xpp eK K ∧ D.etaBar ≤ 1 ∧ D.eBar ≤ 1

def ErrorFormsWeakWindowsFalse : Prop := ∀ ... , ErrWindowsWeak D C Xpp eK K → LargeX ... →
    errorTermWith D C Xpp ≤ D.x ^ (CErr C * D.ε) * ErrText D
```

It is a proposition. Nothing proves it or its negation. It is not in the
kernel export. The name records that the error bound needs the strong
windows. With only $\bar\eta, \bar e \le 1$, the term
$(\bar\eta + 4\sqrt{\bar e})\, x^{c_{HH}} b$ is not small. The compiled
proof uses `ErrWindows`, the strong form.

## A conditional that is discharged correctly

`MatS_at`
(`Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean`)
has the form
`if 1 < D.R.m then (Hilbert–Schmidt bounds on the matrices) else True`.
The `else True` branch would be vacuous. `matSF_of` supplies the
conditions through `hS (cPr x e1' i)`, the conclusion of
`linkS_of_standing_hypotheses`. That conclusion holds when its proviso
is proved, and here the proviso is proved. The `True` branch is not
where the content comes from.

## Where the strength is now

The inequalities above are proved in `linkCore` from fourteen hypotheses
on the family `Fm : FamP eps`. Three of them carry the analytic weight:

| Hypothesis | Content (statement only) | Feeds |
|----|----|----|
| `LinkG` | for large $x$ and every member $i$, `LinkG_at (Fm.Gx x i) Fm.GK C (b ^ δ x)` with $\delta(x) \to 0$ | the loss bound |
| `LinkDIV`, `FrameF`, `SlopesMF`, `SlopesNF`, `LatF` | the divisor and lattice inequalities for each member | the gain bound |
| `ChosenTT`, `ChosenBadp`, `ChosenQD`, `ChosenThin` | choices of windows and auxiliary data | both |

These are fields or consequences of the family `FamP`, which the supply
of `TopG` builds. That supply is the 60% of the proof term measured in
the README. Its largest piece on this path is `placesF_min'`.

None of the declarations read here depends on Nielsen’s four witnesses
(checked in the graph: `linkCore`, `losses_of_small_share_weight`,
`Ga_bound5`, `M.ident`, `tiedCore_of_chainTied`, `placesF_min'`).

## Next

Continued in [step 6](step6-inputs-chain.md), which follows the gain
bound.

1.  `LinkG_at` and its supply, which is the source of the loss bound:
    `linkG_without_kernels`, `linkG_fam_noKer`, `placesF_min'`.
2.  `LinkDIV` and `FrameF`, which are the source of the gain bound.
3.  How `FamP` is constructed in the supply of `TopG`.
