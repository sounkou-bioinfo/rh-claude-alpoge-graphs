# Task: read the lattice construction in the Lean RH proof

You are reading part of a 175,187-file Lean 4 library that claims a proof of the Riemann
Hypothesis (Alpöge, Nov 2026). Source: `/tmp/rh-src/orig/src` (commit 40e56bab). Read only.
Do not edit any file outside `/tmp/rh-agent/`.

## Context (established earlier, verify anything you rely on)

The endgame reduces RH strength to two proved ends:

- Loss side (docs: `/tmp/rh-claude-alpoge-graphs/docs/step8-loss-side.md`): the prime sum
  `ASK` is a sum over inert primes of local terms, each bounded by a local gain
  (`LinkG_at`, `AuxBlock8.Conclusion1`, functions `askG`, `gainP`, `tauP`).
- Gain side (`docs/step7-gain-bottom.md`): `divClausesR_of` (file
  `Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean`) bounds the dual slope
  `muCC` via `Formalism.DivisorInequality.slope_bounds` (geometry of numbers over number
  fields; `BoundsMu`), and `L3main` holds by definition (`ClosedScale3`, `rfl`).
  The record of step 5 (`docs/step5-record.md`, `M.data` in
  `Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean`) fills `Ga`, `Fo`, `Ta`,
  `d`, `T`, `h`, `muN`, `muM` from local data and lattices.

## The question

How are the lattices (fields such as `L.NuLat`, `Nu`, `RR`, Gram matrices `XE`, `Xc`, the
data passed to `BoundsMu` / `slope_bounds` binders `hLB`, `hG`, `hH`, `hP`) built from the
arithmetic/local data, and is the **total local gain** `Σ_p gain(p)` (the `Ga` field) really
bounded by the lattice's degree/slope through a *proved* statement? Concretely:

1. Find the definition of the lattice(s) whose slope `slope_bounds` controls, and the
   declarations that construct them for the family `FamP` (`Fm.L x i`, `Fm.D x i`).
2. Find the statement that relates `Ga` (sum of `gain`) or `Fo`/`h` to the lattice degree,
   slope, covolume or height. Is it proved, a field passed as a hypothesis, or definitional
   (`rfl`, a `def` chosen to make sides equal)?
3. Check for vacuity: `True` bodies, `if … else True`, unused slots, degenerate data
   (zero lattices, empty sets, trivial Gram matrices), definitions that make an inequality an
   identity.
4. Say plainly whether this link carries real arithmetic content, and where exactly.

## Tools

- `grep -rn --include=*.lean` over `/tmp/rh-src/orig/src`.
- Compiled dependency graph in DuckDB: `duckdb -readonly /tmp/rh-graph/graph5.duckdb`.
  Tables: `names(id,name,kind,primary_name)`, `edges(src,dst)` (decl uses constant),
  `sizes(id,type_nodes,value_nodes,type_prop,type_head,value_head,value_args)`,
  view `d` (names+sizes+`type_head_name`,`value_head_name`), `c_rh(id)` (cone of
  riemannHypothesis), `vac(id)` (depends on Nielsen's vacuous witnesses), `vt(id)` (project
  defs with body `True`), `projset(id,m)`.
  Example: who uses X in the cone:
  `SELECT s.name FROM edges e JOIN names t ON t.id=e.dst JOIN names s ON s.id=e.src WHERE t.name='X' AND s.id IN (SELECT id FROM c_rh)`.
  Who builds structure S: edges into `'...S.mk'`. Who concludes predicate P: `d.type_head_name`.
- `/tmp/rh-graph/desc.sh` (forward cone), `/tmp/rh-graph/anc.sh` (dependents),
  `/tmp/rh-graph/chase.sh S` (callers of S.mk). Use `-readonly` for queries; the helper
  scripts write tables, so give new table names prefixed `fa_`.

## Rules

- Report only what you read. Mark everything else "not read". Quote Lean with file:line.
- Do not overstate. Previous readers overstated twice; prefer "not established" to a guess.
- Write the report to `/tmp/rh-agent/lattice-report.md`: summary table (declaration, file,
  read/not read, kind: proved / hypothesis / definitional / vacuous), then sections with
  quoted code, then "what is still open". Plain English, short sentences.
