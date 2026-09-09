#!/usr/bin/env bash
set -euo pipefail
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$PROJECT_ROOT"
# Bacon_Book_ZF_Modal_Semantics and all other core sessions come from ROOT.
./check_isabelle.sh
OUTPUT_DIR="$PROJECT_ROOT/isabelle-kg/bacon"
mkdir -p "$OUTPUT_DIR"
CLASSES_DIR="$(mktemp -d "$OUTPUT_DIR/classes.XXXXXX")"
ISABELLE_SCALA_JAR="$(isabelle getenv -b ISABELLE_SCALA_JAR)"
ISABELLE_CLASSPATH="$(isabelle getenv -b ISABELLE_CLASSPATH)"
isabelle scalac -classpath "$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH" \
  -d "$CLASSES_DIR" tools/isabelle_kg/src/Isabelle_KG.scala
# Session identifiers in ROOT contain no whitespace.
SESSIONS="$(sed -n 's/^session \([A-Za-z_][A-Za-z_0-9]*\) .*/\1/p' ROOT)"
# Intentional word splitting of the identifiers, not of filesystem paths.
# shellcheck disable=SC2086
isabelle java -classpath "$ISABELLE_SCALA_JAR:$ISABELLE_CLASSPATH:$CLASSES_DIR" \
  isabelle.Isabelle_KG "$PROJECT_ROOT" "$OUTPUT_DIR/graph.json" $SESSIONS
python3 tools/isabelle_kg/check_c_proof_dependencies.py "$OUTPUT_DIR/graph.json" \
  > "$OUTPUT_DIR/dependency-audit.txt"
python3 tools/isabelle_kg/query_graph.py stats
