#!/bin/sh
# chase.sh STRUCT : for a structure, list which declarations in the RH cone call STRUCT.mk
duckdb -readonly /tmp/rh-graph/graph5.duckdb -noheader -list -c "SELECT s.name || ' (' || sz.value_nodes || ')' FROM edges e JOIN names t ON t.id=e.dst JOIN names s ON s.id=e.src JOIN sizes sz ON sz.id=s.id WHERE regexp_matches(t.name,'\.$1\.mk\$') AND e.src<>e.dst AND s.id IN (SELECT id FROM c_rh) AND s.name NOT LIKE '%.$1' ORDER BY sz.value_nodes DESC"
