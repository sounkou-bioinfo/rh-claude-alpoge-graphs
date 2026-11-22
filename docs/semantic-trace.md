# Semantic trace of the endgame

2026-11-22

This document follows the proof from the zero-free conclusion back
toward its hardest estimate. Each step records what the Lean source
states, what it assumes, and whether it adds strength or only moves it
into a hypothesis. Only code that was read is described. The places that
were not read are marked. Line references are to
`leanprover-community/riemann-hypothesis` at `40e56bab`. Paths are
relative to `src/`.

[Back to the README](../README.md)

## Summary

| Step | Lean | Read | Kind | Vacuous parts |
|----|----|----|----|----|
| 1 | `formB` | statement | Landau-type: bound on $G_m$ ⇒ zero-free half-plane | none seen |
| 2 | `core_gm` | in full (74 lines) | unpacks `CoreAtH`, calls steps 3 and 4 | none |
| 3 | `Deduction.ch_core` | theorem and `core` lemma; helpers skimmed (446 lines) | averaging over a subgroup by character orthogonality | none |
| 4 | `Deduction.ch_top` | in full (76 lines) | bound on the prime-sum gap from an abstract record | none |
| 5 | `each_unit_bound_statement`, `SizeData₂`, `ErrWindows` supply | see [step 5](step5-record.md) | loss bound and gain bound from hypotheses on the family `FamP` | none found |
| side | `QH.pairEx` host supply | statements and key lemmas | auxiliary primes from zero-density and mean-square bounds | none |

Every step that was read is a valid reduction, and none of them contains
a vacuous condition. Each one moves the hard estimate into a hypothesis.
The strength of the Riemann Hypothesis has not yet been found as a
proved statement. [Step 5](step5-record.md) follows it into the
hypotheses on the family `FamP`.

## Step 1. `formB`: bound on the host sums ⇒ zero-free

The source defines, with the von Mangoldt function $\Lambda$ and Euler’s
constant $\gamma$ (`Formalism/StatementOC.lean`),

$$S(x) = \sum_{n \le x} \Lambda(n)\left(\frac{x}{n} - 1\right), \qquad
G_z(x) = S(x) - x \log x + (1 + \gamma) x$$

and
$G_m(x) = G_z(x) + \sum_{\psi} w_\psi \mathrm{Re}\left(g_{\chi_\psi}(x)\right)$
for a level with characters $\psi$ and weights $w_\psi$. `formB` turns a
one-sided bound $G_m(x) \le x^{1/2 + O(\varepsilon)}$ for large $x$ into
$L(s, \chi) \ne 0$ for $\mathrm{Re}(s) > 1/2$. This is the classical
Landau-type argument. It is sound if the weighted Dirichlet series has
nonnegative coefficients. That condition was not checked here.

## Step 2. `core_gm`: host ⇒ bound on $G_m$

`Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean`, 74
lines, read in full.

``` lean
theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps)
```

The level $\Lambda$ is fixed before $x$ and before the host. So $G_m$
does not move with the host, and the Landau step in step 1 is applied to
one function.

- `EAtH` has five analytic conditions on the host’s characters. They are
  pointwise bounds on twisted Chebyshev sums, bounds on $L'/L(1, \chi)$,
  primitivity, and a kept-character condition. None is vacuous.
- `CoreAtH` unpacks into about 40 components, one of them a window
  bundle of 28 fields. `core_gm` passes them to `Deduction.ch_core` and
  `Deduction.ch_top`. The proof does no estimate of its own.

## Step 3. `Deduction.ch_core`: averaging

`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`,
446 lines. The theorem and the lemma `core` were read. The helpers were
skimmed.

The conclusion is

$$G_{mA}(x) \le x^{1/2 + (C+3)\varepsilon} + \mathrm{Sig}_A(x),$$

where $G_{mA}$ is a weighted sum of $\mathrm{Re}\, G_\psi$ over the kept
characters and $\mathrm{Sig}_A$ sums $\|G_\psi\|$ over the other
characters of the subgroup $A_0$. The proof averages over $A_0$. `sum_A`
uses `AddChar.sum_eq_zero_iff_ne_zero` (orthogonality of characters) to
keep only the characters that are trivial on $A_0$. The essential
hypothesis is

``` lean
(∀ u ∈ A0, gapA D N ell TT a w u ≤ x ^ (C * ε) * errorBracketSizeWindows x ε ...)
```

This is a bound on the gap between a prime sum and its main term.
`ch_core` turns it into the bound on $G_{mA}$. It does not prove the gap
bound. Step 4 supplies it.

## Step 4. `Deduction.ch_top`: the gap bound from an abstract record

`Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`,
76 lines, read in full.

The gap is

$$\mathrm{gapA}(u) = \sum_{t \in TT} \sum_{j} \left( \mathrm{ASK}(a_t, t, w_{u,j}) - \mathrm{Re}\,\mathrm{MAIN}(a_t, w_{u,j}) \right),$$

and `ASK` is a real arithmetic object
(`Development/AutomorphicArithmetic/DedekindLFunctions/RunBaseDimensionLeRankAddGenusTerm.lean`):

``` lean
def ASK (τ : F.G) (a : ℝ) (w : F.G → ℝ) : ℝ :=
  (∑' p : ℕ, if F.Inert p then
      2 * Real.log p * ∑' i : ℕ, if Odd i then max (a / (p : ℝ) ^ i - w (F.partner τ (F.frob p ^ i))) 0 else 0 else 0) +
    Real.log F.d * ∑' i : ℕ, max (a / (F.d : ℝ) ^ (i + 1) - w (F.partner τ (F.gd (i + 1)))) 0
```

It is a smoothed sum over inert primes, twisted through a Frobenius map.
A bound of size about $x^{1/2+\varepsilon}$ on its distance from the
main term has the strength of the Riemann Hypothesis.

`ch_top` does not prove this bound from primes. It works on an abstract
record `Data U0 W Top m f`
(`Formalism/RankGapBounds/MeanBoundSecondForm.lean`). The record has
about 40 real-valued fields, among them `ASK`, `Ga`, `Fo`, `Ta`, `IO`,
`HH`, `etaBar` and `eBar`. Three hypotheses connect the record to the
arithmetic and bound it:

| Hypothesis | Content |
|----|----|
| `h1 : IdentU …` | identifies the record’s `ASK` and `Main` with the real prime sum and main term |
| `h2 : SizeData₂ …` | 11 inequalities on the record’s fields. `each_unit_bound_statement` turns them into $\mathrm{ASK} - \mathrm{Main} \le$ error |
| `h3 : ErrWindows …` | makes the error small. The key clause is $(\bar\eta + 4\sqrt{\bar e})\, x^{c_{HH}} b \le K x^{\varepsilon} n_T a$ |

## Step 5. Where the strength must enter

Continued in [`step5-record.md`](step5-record.md). The rest of this
section records the question as it stood at `ch_top`.

After step 4, the estimate with the strength of the Riemann Hypothesis
has become this statement: the real prime sum `ASK`, identified with an
abstract record by `IdentU`, satisfies the 11 inequalities of
`SizeData₂` with the smallness of $\bar\eta$ and $\bar e$ that
`ErrWindows` requires. These hypotheses are packed into `CoreAtH`. They
come from the supply of `TopG` and the bundle `HypsAlt`.

A hidden equivocation would show at this step, if there is one. The
abstract fields could satisfy the inequalities without being honestly
tied to the arithmetic. The tie consists of `IdentU` and the definitions
of the fields that it does not fix. The next code to read:

1.  `each_unit_bound_statement` and `Ga_bound5`
    (`Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`).
2.  The definition of `SizeData₂` and `IdentU`, and which fields of
    `Data` `IdentU` fixes.
3.  The declarations that supply `IdentU`, `SizeData₂` and `ErrWindows`
    to `CoreAtH`, in the supply of `TopG`.

### An observation not yet examined

`ErrWindows` is defined in
`Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`. The same
file defines a weaker `ErrWindowsWeak`, which only asks $\bar\eta \le 1$
and $\bar e \le 1$, and a proposition named
`ErrorFormsWeakWindowsFalse`. The name suggests that the error bound
fails under the weak windows. Then the smallness of $\bar\eta$ and
$\bar e$ would be where the argument is tight. Whether that proposition
is proved, refuted or unused has not been checked.

## Side branch: the host supply

`Development/AutomorphicArithmetic/MeanSquareBounds/`. Statements and
key lemmas were read.

`QH.pairEx` builds each host from two auxiliary primes
$q \equiv 3 \pmod 8$ and $d \equiv 7 \pmod{16}$. The twists
$\xi \cdot (\cdot/q)$ and $\xi \cdot (\cdot/q)(\cdot/d)$ then satisfy
`Box`:

- their Chebyshev sum is at most $y^{1/2+\tau}$ on the finite window
  $[Y, Y^K]$,
- $L'/L(1)$ is at most $C \log Y$,
- there is no exceptional zero.

The primes exist because of `count_bad`, a zero-density count (at most
$C Q^{1/4}$ bad primes have a zero with $\mathrm{Re}(s) > 1 - 1/400$,
$|\mathrm{Im}(s)| \le Q$), and `meanSq_abs`, a mean-square bound over
the quadratic twists. `box_of_S` turns the finite sum bound into `Box`.
These are real conditions with $\varepsilon$ and $\tau$ free, and none
of them is `True`. They control the twists only on average and on finite
windows. They are inputs to `EAtH`. They are not the bound with the
strength of the Riemann Hypothesis.
