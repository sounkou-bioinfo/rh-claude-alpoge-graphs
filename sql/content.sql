-- Where the proof's content is. Run after sql/load.sql, loading sizes.tsv,
-- and tool/desc.sh for each cone below:
--   tool/desc.sh graph.duckdb c_formb 'UpperTheory.Comparison₂.formB'
--   tool/desc.sh graph.duckdb c_gm    'UpperTheory.Comparison₂.level_gm_le_on_family_scales'
--   tool/desc.sh graph.duckdb c_zf    UpperTheory.Top.zeroFreeAll_of_topG
--   tool/desc.sh graph.duckdb c_shape UpperTheory.Top.shape_closed_link_n_of_green
--   tool/desc.sh graph.duckdb c_green GlobalTheory.GreenBridge.green_of_regular
--   tool/desc.sh graph.duckdb c_hyps  UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound
--   tool/desc.sh graph.duckdb c_tlift UpperTheory.TP.K.tLiftK
--   tool/desc.sh graph.duckdb c_vwin  UpperTheory.One.vwin_of_row
--   tool/desc.sh graph.duckdb c_rect  UpperTheory.Zero.LLC.recTExists
--   tool/desc.sh graph.duckdb c_covol SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt
--   tool/desc.sh graph.duckdb c_rh    riemannHypothesis
-- Then: sed "s#RESULTS#$PWD/../results#g" ../sql/content.sql | duckdb graph.duckdb

CREATE OR REPLACE TABLE sizes AS SELECT * FROM read_csv('sizes.tsv', delim = '\t', header = false,
  columns = {'id': 'UINTEGER', 'type_nodes': 'UBIGINT', 'value_nodes': 'UBIGINT', 'type_prop': 'INTEGER',
             'type_head': 'UINTEGER', 'value_head': 'UINTEGER', 'value_args': 'UINTEGER'});

-- Declarations from the project's own namespaces and modules.
CREATE OR REPLACE TABLE projset AS
SELECT n.id, s.value_nodes AS m FROM names n JOIN sizes s ON s.id = n.id
WHERE n.kind <> '' AND (
  regexp_matches(n.name, '^(GlobalTheory|Formalism|GroundTheory|PositivityTheory|UpperTheory|ReciprocityTheory|PI|LateralTheory|CompanionTheory|CrystallineSemistableComparison|FunctorialResolution|DiscreteGroups|Gp91|PIW|KStar|RootFieldNumerics|MainStatements|SelfIntersectionVolumeEstimates|LevelTowerAlt|SheetDecomposition|TeichLift|MassData[A-Za-z]*|RestTerms|Lemmata|Supplements|BuildAid|Development)(\.|$)')
  OR regexp_matches(n.name, '^_private\.(Development|Formalism|GroundTheory|Lemmata|PositivityTheory|ReciprocityTheory|Supplements|CompanionTheory|BuildAid)\.'));

-- Project mass in each cone, and mass that is in exactly one of the premise cones.
COPY (
  WITH c AS (
    SELECT 'formB' AS cone, id FROM c_formb
    UNION ALL SELECT 'level_gm_le_on_family_scales', id FROM c_gm
    UNION ALL SELECT 'shape_closed_link_n_of_green', id FROM c_shape
    UNION ALL SELECT 'green_of_regular', id FROM c_green
    UNION ALL SELECT 'nonempty_hyps_definite_side_of_closed_bound', id FROM c_hyps
    UNION ALL SELECT 'tLiftK', id FROM c_tlift
    UNION ALL SELECT 'vwin_of_row', id FROM c_vwin
    UNION ALL SELECT 'recTExists', id FROM c_rect
    UNION ALL SELECT 'topCovolSlim2_use_alt_alt', id FROM c_covol
    UNION ALL SELECT '*zeroFreeAll_of_topG', id FROM c_zf
    UNION ALL SELECT '*riemannHypothesis', id FROM c_rh),
  k AS (SELECT id, count(*) FILTER (WHERE cone NOT LIKE '*%') AS k FROM c GROUP BY id)
  SELECT c.cone, count(p.id) AS project_decls, sum(p.m) AS project_nodes,
         count(p.id) FILTER (WHERE k.k = 1 AND c.cone NOT LIKE '*%') AS exclusive_decls,
         coalesce(sum(p.m) FILTER (WHERE k.k = 1 AND c.cone NOT LIKE '*%'), 0) AS exclusive_nodes
  FROM c JOIN projset p ON p.id = c.id JOIN k ON k.id = c.id
  GROUP BY 1 ORDER BY 3 DESC
) TO 'RESULTS/cone_mass.tsv' (DELIMITER '\t', HEADER true);

-- Project definitions whose body is the constant True, and the cones they are in.
COPY (
  SELECT n.name,
         n.id IN (SELECT id FROM c_zf) AS in_zeroFreeAll_of_topG,
         n.id IN (SELECT id FROM c_shape) AS in_shape_of_green,
         n.id IN (SELECT id FROM c_hyps) AS in_hyps_bundle,
         n.id IN (SELECT id FROM c_vwin) AS in_vwin_of_row
  FROM names n JOIN sizes s ON s.id = n.id JOIN names h ON h.id = s.value_head
  WHERE n.id IN (SELECT id FROM projset) AND n.kind IN ('def', 'opaque') AND h.name = 'True' AND s.value_args = 0
  ORDER BY 1
) TO 'RESULTS/true_defs.tsv' (DELIMITER '\t', HEADER true);
