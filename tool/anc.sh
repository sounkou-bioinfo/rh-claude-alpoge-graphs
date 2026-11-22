#!/bin/sh
# anc.sh DB TABLE ROOTNAME : ancestors (transitive dependents) of ROOTNAME, with depth and one successor
db=$1; t=$2; root=$3
duckdb "$db" -c "CREATE OR REPLACE TABLE $t AS SELECT id, 0 AS depth, NULL::UINTEGER AS via FROM names WHERE name='$root' AND kind<>'';"
d=1
while :; do
  n=$(duckdb "$db" -noheader -csv -c "INSERT INTO $t SELECT r.src, $d, min(r.dst) FROM rev r JOIN $t a ON a.id=r.dst AND a.depth=$d-1 WHERE r.src NOT IN (SELECT id FROM $t) GROUP BY r.src; SELECT count(*) FROM $t WHERE depth=$d;")
  [ "$n" = "0" ] && break
  d=$((d+1))
done
