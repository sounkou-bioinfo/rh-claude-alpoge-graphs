# Step 8: the loss side

2026-11-22

[Back to step 7](step7-gain-bottom.md) · [Back to the
README](../README.md)

[Step 5](step5-record.md) split the bound with the strength of the
Riemann Hypothesis into a gain bound and a loss bound. [Step
7](step7-gain-bottom.md) reached the bottom of the gain bound. This step
follows the loss bound,

$$\mathrm{ASK}(u_0) - \mathrm{Ga}(u_0) \le C_{\mathrm{Loss}} \, n_T \, m \, b \, x^{e_{\mathrm{Loss}} \varepsilon},$$

which says that the prime sum is at most the sum of the local gains plus
a small term. Paths are relative to `src/` at `40e56bab`.

## Summary

| Level | Declaration | What it does | Read |
|----|----|----|----|
| 1 | `losses_of_small_share_weight` | proves `LossesSmallShares` from `ChosenTT`, `ChosenBadp`, `LinkG` and `askIsF` | statement and assembly |
| 2 | `askIsF`, `askRec_at`, `inert_sum` | rewrite the prime sum `ASK` as a finite sum over primes of local terms | in full |
| 3 | `loss_setting_family`, `lossHyp_at` | assemble the per-prime hypotheses | in full |
| 4 | `LinkG_at` | per prime: local prime term − local loss ≤ local gain − $\tau$ | definition, in full |
| 5 | `linkG_at_core` | proves `LinkG_at` from the per-prime inequality `AuxBlock8.Conclusion1` and fill identities | statement |
| 6 | `linkG_concrete5`, `loc_proved` | supply `LinkG` for every family in the class | statements |

No vacuous condition and no definition with body `True` is in any of
these cones.

## The prime sum becomes a sum over primes of local terms

`inert_sum`
(`Formalism/SharpRestriction/GlobalSchurBounds/FrameCodeOfAdditive.lean`)
proves

$$\sum_{p} \mathbf{1}_{\mathrm{inert}}(p)\, 2 \log p \cdot \mathrm{askP}(p)
= \sum_{p \in \mathrm{askPrimes}} 2 \log p \cdot \mathrm{vonMangoldtClassSum}(p),$$

where `askP` is the local term
$\sum_{e \text{ odd}} \max\left(0, a/p^e - \mathrm{fill}(\ldots)\right)$.
So the prime sum of [step 4 of the trace](semantic-trace.md) is a finite
sum of local contributions, one for each inert prime below the cut-off.
`askIsF` applies this to every member of the family.

## The per-prime inequality

`LinkG_at` (`Formalism/SharpRestriction/GlobalTheoremInputs.lean`) asks,
for each place $w$ over an inert prime $p \le X''$,

$$0 \le \mathrm{gain}_j(w) \le \frac{4\,|TT|\,a}{p}, \qquad
\sum_j \sum_{t} \left(\mathrm{vMCS}_j(t, p) - \mathrm{lo}(p)\right) - m\,\mathrm{fl}(p)
\le \sum_j \mathrm{gain}_j(w) - \tau(w),$$

plus lattice conditions on the local lengths. `linkG_at_core`
(`Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean`)
proves it from `AuxBlock8.Conclusion1`, the same inequality written with
the explicit local functions:

- `askG`: the local prime term,
  $\sum_{e \text{ odd}} \max\left(0, a_s/p^e - \mathrm{fillG}(\ldots)\right)$;
- `gainP`: the local gain, a sum over residue orbits $t_0$ of
  $\max\left(g_U - \mathrm{Pr}, \max(g_0, 0)\right)$;
- `tauP`: a count of orbits weighted by $m$;
- `lo`, `fl`: explicit small error terms in $\log x$, $a$, $b$ and the
  scale parameters.

The fill identities (`ParametersFill`) state that the record’s local
fields equal these explicit functions. This is the same tie as in step
5.

## Where `LinkG` comes from

The graph gives the path from the main theorem to the supply of `LinkG`:

``` text
riemannHypothesis → … → zero_free_all_of_green_v_win → shape_closed_link_n_of_green
  → closed_linkG_of_duty → linkG_concrete5 → linkG_concrete_noKer → link_of_local_closed
```

`linkG_concrete5` proves `LinkG` for every family in a class. It uses
`loc_proved`, group compatibility, and `Adm2F`. `Adm2F` is proved by
`admissible_tops_mertens`, a Mertens-type estimate. `loc_proved` is a
theorem with no hypotheses. It applies `stmtE`, which fixes the
constants `26, 2, 24, 60` by `norm_num` and then calls `stmt`.

| Cone | Declarations | Share of proof | Vacuous dependencies | `True` definitions | Theorems using analysis |
|----|----|----|----|----|----|
| `loc_proved` | 11,767 | 0.53% | 0 | 0 | 2 |
| `linkG_fam_noKer` | 6,944 | 0.30% | 0 | 0 | 38 |
| `losses_of_small_share_weight` | 4,126 | 0.09% | 0 | 0 | 12 |
| `AuxBlock8.Pf.stmtF` (per-prime inequality) | 3,085 | 0.08% | 0 | 0 | 32 |
| `linkG_at_core` | 1,586 | 0.01% | 0 | 0 | 1 |

A name is not a reliable guide. `UnusedSlot33.field_lemmas_except_seven`
is used in `linkG_fam_noKer`. It is a real theorem that bundles eight
field lemmas, and it has no vacuous dependency.

## What the two sides together say

The trace now reaches a proved statement on both sides.

- **Loss side.** For each inert prime $p$, the local contribution to the
  prime sum is at most a local gain plus explicit small terms. This is a
  per-prime inequality between explicit local functions. Summed over
  $p$, it gives
  $\mathrm{ASK} \le \sum_p \mathrm{gain}(p) + \text{small}$.
- **Gain side.** The sum of the local gains is bounded by the main term
  $\sum_\rho p_j w_{j\rho} \log \Omega$. The bound comes through a
  lattice whose dual slope is controlled by `slope_bounds`, a proved
  theorem in the geometry of numbers over number fields.

Read together, the argument’s form is: *write the prime sum as a sum of
local contributions, bound each one by a local gain, and bound the total
gain by the degree of an arithmetic lattice.* This is an Arakelov-style
argument: the global bound comes from a slope inequality for a lattice
built from local data. If it is correct, the essential content is that
the sum of the local gains is the degree, or is bounded by the degree,
of a lattice whose slope can be controlled.

That identification of the total local gain with a lattice degree is the
one statement this report has not seen proved. It is the link between
the two sides: the construction of the lattices `Nu`, `XE`, `Xc` from
the local data. It is the place to read next. A competent human reader
would judge the whole argument there.

Continued in [step 9](step9-lattice-link.md), which reads the link
between the two sides.
