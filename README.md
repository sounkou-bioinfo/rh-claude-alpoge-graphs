# rh-claude-alpoge-graphs

A dependency graph of the compiled Lean proof of the Riemann Hypothesis that
Levent Alpöge released on 20 November 2026. The graph tests the claim in
J. L. Nielsen's *The Invalidity of Alpöge's Proposed Proof of the Riemann
Hypothesis* (PhilArchive NIEIOT-2) that the proof rests on vacuously true
geometric witnesses. It answers the question in nomad421's note "What follows
from the dependency trace in the Riemann Hypothesis proof?".

The report is [`report/geometry-slot.pdf`](report/geometry-slot.pdf).

## Findings

- The four witnesses that Nielsen names (`anyGeometry`, `geoDegenerate`,
  `divXFl`, `x0`) are transitive dependencies of `riemannHypothesis` in the
  compiled term.
- 85 of the 1,468,414 reachable declarations depend on them. All of these paths
  go through one lemma, `every_character_of_theta_integrals_local_matching`.
  They enter it through the premises that assemble the hypothesis bundle.
- No declaration eliminates the geometry closure `GeoCl` or reads the content of
  a certificate. `geoOf`, `geoOf_surf` and `FrobeniusOrbitPlaceCount` are not in
  the export.
- The lemmas that derive nonvanishing from the bundle do not depend on the four
  witnesses.

The graph shows which constants each term contains. It does not show how a term
uses them. What the premises without these dependencies contain is not
examined here. The report gives the limits in full.

## Contents

| Path | Content |
|---|---|
| `tool/rhgraph.c` | Streams a lean4export NDJSON file and writes the dependency graph of the given root declarations |
| `tool/anc.sh` | Breadth-first search for the dependents of one declaration, in DuckDB |
| `sql/load.sql` | Loads the `rhgraph` output into DuckDB |
| `sql/queries.sql` | The queries behind each result in the report |
| `results/` | Small result tables: dependents of each witness, the figure subgraph, run statistics |
| `report/` | Quarto source, PDF and the graph figure (`depgraph.dot`, `depgraph.svg`) |

## Input

Andrew Sutherland's export of the proof,
`https://math.mit.edu/~drew/grh/solution.ndjson.zst`. It is 7.7 GB compressed
and 61.6 GB uncompressed, with SHA-256
`61a8938a…05381`. Check the full hash against his `SHA256SUMS`. The export
was built from `leanprover-community/riemann-hypothesis` at `40e56bab`.

## Reproduction

Requirements: a C compiler, `zstd`, DuckDB 1.x, about 60 GB of RAM and about
10 minutes for the graph build.

```sh
curl -LO https://math.mit.edu/~drew/grh/solution.ndjson.zst
gcc -O2 -o rhgraph tool/rhgraph.c
mkdir out
zstd -dc --long=31 solution.ndjson.zst | ./rhgraph out riemannHypothesis \
  riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re \
  LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
cd out
duckdb graph.duckdb < ../sql/load.sql
../tool/anc.sh graph.duckdb anc_any    GlobalTheory.Mem.Top.Bl.anyGeometry
../tool/anc.sh graph.duckdb anc_geodeg Formalism.L2.Geo.geoDegenerate
../tool/anc.sh graph.duckdb anc_divxfl Formalism.L2.Geo.divXFl
../tool/anc.sh graph.duckdb anc_x0     GlobalTheory.Mem.Top.DivRec.x0
duckdb graph.duckdb < ../sql/queries.sql
```

`rhgraph` writes:

| File | Rows |
|---|---|
| `names.tsv` | name id, full name, declaration kind, 1 if the name is the primary name of its block |
| `closure.tsv` | name id of each declaration block reachable from the roots |
| `edges.tsv` | declaration, constant that occurs directly in its type, value or recursor rules |
| `projs.tsv` | declaration, structure, field index of each `Expr.proj` in its terms |
| `stats.txt` | counts |

A reference to any name in an inductive block brings in the whole block, so the
closure over-approximates the true dependencies.

## Not included

Nielsen's paper is not redistributed. It is on PhilArchive as NIEIOT-2. The
export and the full graph tables (5 GB) are not included. They can be rebuilt
with the commands above.
