-- Load the rhgraph output into DuckDB.
-- Run from the directory that holds the rhgraph output files:
--   duckdb graph.duckdb < sql/load.sql
CREATE TABLE names AS SELECT * FROM read_csv('names.tsv', delim = '\t', header = false, quote = '', escape = '',
  columns = {'id': 'UINTEGER', 'name': 'VARCHAR', 'kind': 'VARCHAR', 'primary_name': 'INTEGER'});
CREATE TABLE closure AS SELECT * FROM read_csv('closure.tsv', delim = '\t', header = false,
  columns = {'id': 'UINTEGER'});
CREATE TABLE edges AS SELECT * FROM read_csv('edges.tsv', delim = '\t', header = false,
  columns = {'src': 'UINTEGER', 'dst': 'UINTEGER'});
CREATE TABLE projs AS SELECT * FROM read_csv('projs.tsv', delim = '\t', header = false,
  columns = {'src': 'UINTEGER', 'struct': 'UINTEGER', 'idx': 'UINTEGER'});
-- Reversed edges without self-loops, for "who depends on X".
CREATE TABLE rev AS SELECT dst, src FROM edges WHERE src <> dst;
