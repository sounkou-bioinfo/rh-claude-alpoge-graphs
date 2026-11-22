-- Queries behind the report. Run after sql/load.sql and after tool/anc.sh has
-- built the dependent tables:
--   tool/anc.sh graph.duckdb anc_any    GlobalTheory.Mem.Top.Bl.anyGeometry
--   tool/anc.sh graph.duckdb anc_geodeg Formalism.L2.Geo.geoDegenerate
--   tool/anc.sh graph.duckdb anc_divxfl Formalism.L2.Geo.divXFl
--   tool/anc.sh graph.duckdb anc_x0     GlobalTheory.Mem.Top.DivRec.x0

-- Declarations that the walk from the five main theorems does not reach.
SELECT name, kind FROM names
WHERE primary_name = 1 AND kind <> '' AND id NOT IN (SELECT id FROM closure);

-- Union of the dependents of the four vacuous witnesses.
CREATE OR REPLACE TABLE vac AS
  SELECT id FROM anc_any UNION SELECT id FROM anc_geodeg
  UNION SELECT id FROM anc_divxfl UNION SELECT id FROM anc_x0;
SELECT count(*) AS dependents_of_vacuous_witnesses FROM vac;

-- Distance of riemannHypothesis from each witness.
SELECT 'anyGeometry' AS witness, depth FROM anc_any a JOIN names n ON n.id = a.id WHERE n.name = 'riemannHypothesis'
UNION ALL SELECT 'geoDegenerate', depth FROM anc_geodeg a JOIN names n ON n.id = a.id WHERE n.name = 'riemannHypothesis'
UNION ALL SELECT 'divXFl', depth FROM anc_divxfl a JOIN names n ON n.id = a.id WHERE n.name = 'riemannHypothesis'
UNION ALL SELECT 'x0', depth FROM anc_x0 a JOIN names n ON n.id = a.id WHERE n.name = 'riemannHypothesis';

-- Does a declaration depend on a vacuous witness?
SELECT n.name, n.id IN (SELECT id FROM vac) AS depends_on_vacuous_witness
FROM names n WHERE n.name IN (
  'UpperTheory.Top.zero_free_all_of_green_v_win',
  'UpperTheory.Top.every_character_of_green_v_win',
  'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound',
  'UpperTheory.Lit.every_character_of_theta_integrals_local_matching',
  'Formalism.VW.rh_of_every',
  'Formalism.L2.DIV.linkDIV_at_words',
  'Formalism.L2.DIV.Compl3');

-- Direct premises of the lemma where all paths to the witnesses join.
SELECT d.name, d.kind, d.id IN (SELECT id FROM vac) AS depends_on_vacuous_witness
FROM edges e JOIN names s ON s.id = e.src JOIN names d ON d.id = e.dst
WHERE s.name = 'UpperTheory.Lit.every_character_of_theta_integrals_local_matching'
ORDER BY 3 DESC, 1;

-- Cut test: remove one declaration and check whether the witnesses stay
-- reachable from riemannHypothesis inside the dependent subgraph.
WITH RECURSIVE r(id) AS (
  SELECT id FROM names WHERE name = 'riemannHypothesis'
  UNION
  SELECT e.dst FROM r JOIN edges e ON e.src = r.id
  WHERE e.src IN (SELECT id FROM vac) AND e.dst IN (SELECT id FROM vac)
    AND e.dst <> (SELECT id FROM names
                  WHERE name = 'UpperTheory.Lit.every_character_of_theta_integrals_local_matching' AND kind <> ''))
SELECT n.name AS still_reachable FROM r JOIN names n ON n.id = r.id
WHERE n.name IN ('GlobalTheory.Mem.Top.Bl.anyGeometry', 'Formalism.L2.Geo.geoDegenerate',
                 'Formalism.L2.Geo.divXFl', 'GlobalTheory.Mem.Top.DivRec.x0');

-- Consumers of certificate content: recursors and projections of GeoCl and OAt.
WITH t AS (SELECT id, name FROM names WHERE name IN (
  'GlobalTheory.Mem.Top.Bl.GeoCl.rec', 'GlobalTheory.Mem.Top.Bl.GeoCl.casesOn',
  'GlobalTheory.Mem.Top.Bl.OAt.geo', 'GlobalTheory.Mem.Top.Bl.OAt.rec',
  'GlobalTheory.Mem.Top.Bl.OAt.casesOn', 'GlobalTheory.Mem.Top.Bl.geoOf_surf',
  'GlobalTheory.Mem.Top.Bl.oAt_geoOf', 'GlobalTheory.Mem.Top.Bl.geoOf'))
SELECT t.name AS consumer_of, s.name AS used_by
FROM t LEFT JOIN edges e ON e.dst = t.id AND e.src <> t.id LEFT JOIN names s ON s.id = e.src
ORDER BY 1, 2;

-- Raw Expr.proj nodes on the OAt structure.
SELECT p.idx, s.name FROM projs p JOIN names s ON s.id = p.src
WHERE p.struct = (SELECT id FROM names WHERE name = 'GlobalTheory.Mem.Top.Bl.OAt');

-- Constants from Nielsen's checks that may be absent from the export.
SELECT name, kind FROM names
WHERE regexp_extract(name, '([^.]+)$', 1) IN ('geoOf', 'geoOf_surf', 'oAt_geoOf', 'FrobeniusOrbitPlaceCount');
