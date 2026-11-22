#!/bin/sh
# desc.sh DB TABLE ROOTNAME : forward dependency cone of ROOTNAME (everything its term uses, transitively)
db=$1; t=$2; root=$3
duckdb "$db" -c "CREATE OR REPLACE TABLE $t AS SELECT id, 0 AS depth FROM names WHERE name='$root' AND kind<>'';"
d=1
while :; do
  n=$(duckdb "$db" -noheader -csv -c "INSERT INTO $t SELECT DISTINCT e.dst, $d FROM edges e JOIN $t a ON a.id=e.src AND a.depth=$d-1 WHERE e.dst NOT IN (SELECT id FROM $t); SELECT count(*) FROM $t WHERE depth=$d;")
  [ "$n" = "0" ] && break
  d=$((d+1))
done
