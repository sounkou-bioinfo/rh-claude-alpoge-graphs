# Where does the trivial geometry certificate go?

2026-11-22

This is an agent exploration. The investigation, the tools and this text
were made in the [Pi coding agent](https://github.com/earendil-works/pi)
with Fable 5.2 and Claude Opus 5.5, directed by
[sounkou-bioinfo](https://github.com/sounkou-bioinfo). The proof under
study is reported to be generated with Claude, and one of the analysing
models is Claude. Read the conclusions with that conflict in mind and
check them against the data in `results/` and the tools in `tool/`.

## The question

On 20 November 2026 Levent Alpöge released a proof of the Riemann
Hypothesis as a Lean library. J. L. Nielsen’s paper *The Invalidity of
Alpöge’s Proposed Proof of the Riemann Hypothesis* (PhilArchive
NIEIOT-2) reports that the hypothesis bundle in the proof rests on
witnesses that are vacuously true. In the source, the geometry predicate
is

``` lean
def anyGeometry : GeoP := fun _ _ _ => True
```

Her §10 says that she did not run a compiled dependency trace.
nomad421’s note “What follows from the dependency trace in the Riemann
Hypothesis proof?” asks for the step where the formal proof needs a
geometric fact and accepts the trivial certificate in its place.

This repository runs the trace on the compiled proof, the kernel export
that the independent checkers accepted.

**In short:** the vacuous witnesses are in the compiled proof, as
Nielsen says. Nothing reads them, as nomad421 says. They reach the main
theorem through one lemma, by the premises that assemble the hypothesis
bundle. The step that derives nonvanishing does not depend on them. What
the rest of the proof contains is the open question.

## Why a vacuous witness can be harmless

Take a lemma that is uniform in the geometry parameter $\Gamma$ and
whose conclusion $C$ does not mention $\Gamma$:

$$L : \forall \Gamma : \mathrm{GeoP}, \quad H(\Gamma) \to \mathrm{GeoCl}\ \Gamma \to C$$

Instantiate it at the constant predicate
$\Gamma^{\top} := \lambda D J X. \top$, which is `anyGeometry`. The
certificate $\mathrm{GeoCl}(\Gamma^{\top})$ is then free, and $L$ proves
$C$ from $H(\Gamma^{\top})$ alone. The certificate carries information
to $C$ only if some step *eliminates* it: a recursor on
$\mathrm{GeoCl}$, a projection of its field, or a lemma such as
`geoOf_surf` that extracts a surface from it. If no step does, the
vacuous witness is dead weight. It makes the names misleading. It does
not make $C$ easier to reach than $H$ alone.

So the question becomes a graph question: is there a path from
`riemannHypothesis` to the witnesses, and does any declaration on such a
path eliminate them?

## The dependency graph

![Every dependency path from riemannHypothesis to the four vacuous
witnesses that Nielsen names (red). Orange: depends on a vacuous
witness. Green: does not. An arrow points from a declaration to a
constant that its compiled term uses directly.](figures/depgraph.svg)

| Witness | Namespace | Dependents | Steps from riemannHypothesis |
|:---|:---|---:|---:|
| `anyGeometry` | `GlobalTheory.Mem.Top.Bl` | 31 | 8 |
| `x0` | `GlobalTheory.Mem.Top.DivRec` | 52 | 16 |
| `divXFl` | `Formalism.L2.Geo` | 28 | 20 |
| `geoDegenerate` | `Formalism.L2.Geo` | 53 | 21 |

The export holds 1,468,418 declarations. The walk from the five theorems
in `Main.lean` reaches 1,468,414 of them. Of those, only **85** depend
on any of the four witnesses.

- **Every path to the witnesses goes through one lemma**,
  `every_character_of_theta_integrals_local_matching`. If that lemma is
  removed from the graph, 0 witnesses remain reachable from
  `riemannHypothesis`.
- **The paths enter that lemma through the premises that assemble the
  hypothesis bundle**: `parametersOfDependence` and
  `nonempty_hyps_definite_side_of_closed_bound`.
- **The other premises of the lemma do not depend on the witnesses.**
  Neither does the step that derives nonvanishing from the bundle:

| Declaration | Depends on a vacuous witness |
|:---|:---|
| `every_character_of_theta_integrals_local_matching` | yes |
| `nonempty_hyps_definite_side_of_closed_bound` | yes |
| `zeroFreeOn_of_tiedWin_cyc` | no |
| `Compl3` | no |
| `DivInputsR` | no |
| `WordFacts` | no |
| `linkDIV_at_words` | no |
| `rh_of_every` | no |
| `every_character_of_green_v_win` | no |
| `zero_free_all_of_green_v_win` | no |

## Is the content of a certificate ever read?

| Constant                   | Used by                 |
|:---------------------------|:------------------------|
| `GeoCl.rec`                | GeoCl                   |
| `OAt.geo`                  | oAt_setDiv, divEx_geoCl |
| `OAt.rec`                  | none                    |
| `FrobeniusOrbitPlaceCount` | not in the export       |
| `geoOf`                    | not in the export       |
| `geoOf_surf`               | not in the export       |
| `oAt_geoOf`                | not in the export       |

`GeoCl.rec` is used only by the `GeoCl` block itself. `OAt.rec` has no
users. The two users of `OAt.geo` pass the field to `GeoCl.step` and
`geoCl_of`, which build another certificate. The lemmas that would
extract a surface from the real geometry predicate are not in the
export.

## Nielsen’s four checks

Nielsen’s §9 lists four checks that would confirm or refute her
analysis.

1.  **Independent kernel replay.** Andrew Sutherland reports that nanoda
    accepts the export, con-leche accepts all 1,468,418 declarations and
    justifies the five statements against a Mathlib-only challenge, and
    lean4lean accepts all 175,187 modules. The Lean 4.36.0 Comparator
    run has passed the statement comparison and the axiom check. Its
    kernel stages were still running when this was written. nanoda and
    con-leche check the exported term without code compiled by Lean
    4.33.1.
2.  **Dependency walk.** All four witnesses are in the closure. *This
    confirms her finding in the compiled term.*
3.  **The degree equation.** `FrobeniusOrbitPlaceCount` is not in the
    export. *The concern does not arise.*
4.  **The remaining hypotheses.** The content of the proof must be in
    the premises that do not depend on the witnesses (green in the
    figure). *What they contain is not examined here. This check is
    open.*

## Assessment

**Nielsen is right that** the geometry predicate is `True`, that the
vacuous witnesses are in the dependency closure, that the lemmas written
to extract geometric content are never used, and that the geometric
story in the source is not the argument that derives the theorem. A
reader who follows the names in the source is misled.

**nomad421 is right that** no step uses the trivial certificate as
evidence for a geometric object. The graph confirms this for every
reachable declaration.

**On validity.** A vacuous definition can make a step easier. It cannot
make a false statement derivable in a sound kernel. The derivation that
was checked does not get its conclusion from the witnesses. If the proof
is wrong, the fault is in kernel soundness, in the meaning of the
statement (Mathlib’s `riemannZeta` and `RiemannHypothesis` at the pinned
version, and the challenge comparison), or in the identity of the
checked artifact. Nielsen’s argument addresses none of these. What the
green premises contain, and whether it is the mathematics that a proof
of the Riemann Hypothesis needs, has not been explained by anyone.

## Limits

- No kernel was run for this work. Acceptance of the export comes from
  Sutherland’s runs.
- The graph records which constants a term contains, not how the term
  uses them. “Never read” rests on the absence of eliminations and
  projections.
- The green premises do not depend on the four witnesses that Nielsen
  names. They can contain other vacuous definitions.
- A reference to any name in an inductive block brings in the whole
  block, so the graph over-approximates the dependencies.

## Method

| Quantity                              | Value         |
|:--------------------------------------|:--------------|
| NDJSON lines                          | 1,080,769,508 |
| Expression nodes                      | 1,065,214,335 |
| Declaration records                   | 1,468,418     |
| Reachable from the five main theorems | 1,468,414     |
| Direct dependency edges               | 116,225,516   |
| Structure projections (Expr.proj)     | 88,149        |

`tool/rhgraph.c` streams Sutherland’s export
(`https://math.mit.edu/~drew/grh/solution.ndjson.zst`, SHA-256
`61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381`,
built from `leanprover-community/riemann-hypothesis` at `40e56bab`) and
keeps the expression DAG in memory. It walks the type, value and
recursor rules of every declaration reachable from the roots, and writes
one edge per constant that a declaration uses directly. The edges are
queried in DuckDB: `tool/anc.sh` computes the dependents of a
declaration by breadth-first search on the reversed edges.

### Reproduction

Requirements: a C compiler, `zstd`, DuckDB 1.x, about 60 GB of RAM and
about 10 minutes for the graph build. Rendering this file needs Quarto,
R with knitr, and Graphviz.

``` sh
curl -LO https://math.mit.edu/~drew/grh/solution.ndjson.zst
gcc -O2 -o rhgraph tool/rhgraph.c
mkdir out
zstd -dc --long=31 solution.ndjson.zst | ./rhgraph out riemannHypothesis \
  riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re \
  LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
cp out/stats.txt results/
cd out
duckdb graph.duckdb < ../sql/load.sql
../tool/anc.sh graph.duckdb anc_any    GlobalTheory.Mem.Top.Bl.anyGeometry
../tool/anc.sh graph.duckdb anc_geodeg Formalism.L2.Geo.geoDegenerate
../tool/anc.sh graph.duckdb anc_divxfl Formalism.L2.Geo.divXFl
../tool/anc.sh graph.duckdb anc_x0     GlobalTheory.Mem.Top.DivRec.x0
duckdb graph.duckdb < ../sql/queries.sql
sed "s#RESULTS#$PWD/../results#g" ../sql/export_results.sql | duckdb graph.duckdb
cd .. && quarto render README.qmd
```

| Path | Content |
|----|----|
| `README.qmd` | This document. It renders `README.md` and `rh-claude-alpoge-graphs.pdf` |
| `tool/rhgraph.c` | Export reader and graph builder |
| `tool/anc.sh` | Dependents of one declaration, in DuckDB |
| `sql/` | Load script, the queries behind each result, and the export of `results/` |
| `results/` | The result tables that this document reads |
| `figures/` | The graph, generated when this document is rendered |

Nielsen’s paper is not redistributed. The export and the full graph
tables (about 5 GB) are not included. They can be rebuilt with the
commands above.
