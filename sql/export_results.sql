-- Write the small result tables in results/ that README.qmd reads.
-- Run after sql/load.sql, tool/anc.sh for the four witnesses, and the `vac`
-- table in sql/queries.sql. Run from the rhgraph output directory; RESULTS is
-- the repository's results/ directory:
--   sed "s#RESULTS#$PWD/../results#g" ../sql/export_results.sql | duckdb graph.duckdb

COPY (
  SELECT 'anyGeometry' AS witness, a.depth, n.name, v.name AS via FROM anc_any a JOIN names n ON n.id = a.id LEFT JOIN names v ON v.id = a.via
  UNION ALL SELECT 'geoDegenerate', a.depth, n.name, v.name FROM anc_geodeg a JOIN names n ON n.id = a.id LEFT JOIN names v ON v.id = a.via
  UNION ALL SELECT 'divXFl', a.depth, n.name, v.name FROM anc_divxfl a JOIN names n ON n.id = a.id LEFT JOIN names v ON v.id = a.via
  UNION ALL SELECT 'x0', a.depth, n.name, v.name FROM anc_x0 a JOIN names n ON n.id = a.id LEFT JOIN names v ON v.id = a.via
  ORDER BY 1, 2, 3
) TO 'RESULTS/witness_dependents.tsv' (DELIMITER '\t', HEADER true);

COPY (
  SELECT name, kind FROM names
  WHERE primary_name = 1 AND kind <> '' AND id NOT IN (SELECT id FROM closure) ORDER BY 1
) TO 'RESULTS/not_reachable.tsv' (DELIMITER '\t', HEADER true);

COPY (
  SELECT d.name, d.kind, d.id IN (SELECT id FROM vac) AS depends_on_vacuous_witness
  FROM edges e JOIN names s ON s.id = e.src JOIN names d ON d.id = e.dst
  WHERE s.name = 'UpperTheory.Lit.every_character_of_theta_integrals_local_matching'
    AND d.name LIKE '%Theory.%'
  ORDER BY 3 DESC, 1
) TO 'RESULTS/join_lemma_premises.tsv' (DELIMITER '\t', HEADER true);

COPY (
  SELECT n.name, n.id IN (SELECT id FROM vac) AS depends_on_vacuous_witness
  FROM names n WHERE n.kind <> '' AND n.name IN (
    'UpperTheory.Top.zero_free_all_of_green_v_win', 'UpperTheory.Top.every_character_of_green_v_win',
    'UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound',
    'UpperTheory.Lit.every_character_of_theta_integrals_local_matching',
    'Formalism.VW.rh_of_every', 'Formalism.HC.zeroFreeOn_of_tiedWin_cyc',
    'Formalism.L2.DIV.linkDIV_at_words', 'Formalism.L2.DIV.Compl3',
    'Formalism.L2.DIV.WordFacts', 'Formalism.L2.DIV.DivInputsR')
  ORDER BY 2 DESC, 1
) TO 'RESULTS/key_declarations.tsv' (DELIMITER '\t', HEADER true);

COPY (
  WITH t AS (SELECT id, name FROM names WHERE name IN (
    'GlobalTheory.Mem.Top.Bl.GeoCl.rec', 'GlobalTheory.Mem.Top.Bl.OAt.geo', 'GlobalTheory.Mem.Top.Bl.OAt.rec'))
  SELECT t.name AS constant, s.name AS used_by
  FROM t LEFT JOIN edges e ON e.dst = t.id AND e.src <> t.id LEFT JOIN names s ON s.id = e.src
  ORDER BY 1, 2
) TO 'RESULTS/certificate_consumers.tsv' (DELIMITER '\t', HEADER true);

COPY (
  SELECT x.n AS constant, count(n.id) AS present_in_export
  FROM (VALUES ('geoOf'), ('geoOf_surf'), ('oAt_geoOf'), ('FrobeniusOrbitPlaceCount')) x(n)
  LEFT JOIN names n ON n.kind <> '' AND regexp_extract(n.name, '([^.]+)$', 1) = x.n
  GROUP BY 1 ORDER BY 1
) TO 'RESULTS/absent_constants.tsv' (DELIMITER '\t', HEADER true);

COPY (
  WITH RECURSIVE r(id) AS (
    SELECT id FROM names WHERE name = 'riemannHypothesis'
    UNION
    SELECT e.dst FROM r JOIN edges e ON e.src = r.id
    WHERE e.src IN (SELECT id FROM vac) AND e.dst IN (SELECT id FROM vac)
      AND e.dst <> (SELECT id FROM names
                    WHERE name = 'UpperTheory.Lit.every_character_of_theta_integrals_local_matching' AND kind <> ''))
  SELECT 'every_character_of_theta_integrals_local_matching' AS removed,
         count(*) FILTER (WHERE n.name IN ('GlobalTheory.Mem.Top.Bl.anyGeometry', 'Formalism.L2.Geo.geoDegenerate',
                                           'Formalism.L2.Geo.divXFl', 'GlobalTheory.Mem.Top.DivRec.x0')) AS witnesses_still_reachable
  FROM r JOIN names n ON n.id = r.id
) TO 'RESULTS/cut_test.tsv' (DELIMITER '\t', HEADER true);

-- Figure subgraph: every 'via' path from riemannHypothesis to each witness,
-- plus the named premises of the lemma where the paths join.
CREATE OR REPLACE TEMP TABLE fig_ids AS
WITH RECURSIVE ch(id, t) AS (
  SELECT n.id, x.t FROM names n, (VALUES ('any'), ('geodeg'), ('divxfl'), ('x0')) x(t) WHERE n.name = 'riemannHypothesis'
  UNION
  SELECT CASE ch.t WHEN 'any' THEN (SELECT via FROM anc_any a WHERE a.id = ch.id)
                   WHEN 'geodeg' THEN (SELECT via FROM anc_geodeg a WHERE a.id = ch.id)
                   WHEN 'divxfl' THEN (SELECT via FROM anc_divxfl a WHERE a.id = ch.id)
                   ELSE (SELECT via FROM anc_x0 a WHERE a.id = ch.id) END, ch.t
  FROM ch WHERE ch.id IS NOT NULL)
SELECT DISTINCT id FROM ch WHERE id IS NOT NULL
UNION
SELECT id FROM names WHERE kind <> '' AND name IN (
  'GlobalTheory.GreenBridge.green_of_regular', 'UpperTheory.Top.VWin', 'UpperTheory.Top.every_character_of_green_v_win',
  'UpperTheory.Zero.LLC.RecTExists', 'UpperTheory.N.boundAtTwoThree_linked_of_recT',
  'GlobalTheory.Mem.Top.Bl.parametersOfDependence',
  'GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree',
  'UpperTheory.Top.zero_free_all_of_green_v_win');

COPY (
  SELECT n.id, regexp_extract(n.name, '([^.]+)$', 1) AS short, n.name, n.kind,
         n.id IN (SELECT id FROM vac) AS vac,
         n.name IN ('GlobalTheory.Mem.Top.Bl.anyGeometry', 'Formalism.L2.Geo.geoDegenerate',
                    'Formalism.L2.Geo.divXFl', 'GlobalTheory.Mem.Top.DivRec.x0') AS witness
  FROM fig_ids f JOIN names n ON n.id = f.id
) TO 'RESULTS/fig_nodes.tsv' (DELIMITER '\t', HEADER false);

COPY (
  SELECT e.src, e.dst FROM edges e
  WHERE e.src IN (SELECT id FROM fig_ids) AND e.dst IN (SELECT id FROM fig_ids) AND e.src <> e.dst
) TO 'RESULTS/fig_edges.tsv' (DELIMITER '\t', HEADER false);
