#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ $# -gt 1 || ( $# == 1 && "$1" != "--core" ) ]]; then
  echo "Usage: $0 [--core]" >&2
  exit 2
fi
python3 -m unittest discover -s "$ROOT_DIR/tools/tests" -p 'test_*.py'
python3 "$ROOT_DIR/tools/check_isabelle_trust.py"
python3 "$ROOT_DIR/tools/check_core_source_boundary.py"
python3 "$ROOT_DIR/tools/check_release.py"
# The selected core sessions are declared in ROOT; applications are absent.
# One build job at a time. Do not run another build/export concurrently.
exec isabelle build -j 1 -d "$ROOT_DIR" -o timeout=60 -o export_theory=true \
  Bacon_Base \
  Bacon_Source_Vocabulary_Development \
  Bacon_Book_Environment_Development \
  Bacon_Source_Model_Development \
  Bacon_Parametric_Signature_Development \
  Bacon_Parametric_Canonical_Development \
  Bacon_Parametric_Countable_Development \
  Bacon_Book_Classicism_Development \
  Bacon_Book_Modal_Representation \
  Bacon_Book_ZF_Modal_Semantics \
  Bacon_Book_ZF_Modal_Interpretation \
  Bacon_Book_ZF_Model_Regressions \
  Bacon_Book_ZF_Modal_Representation \
  Bacon_Classicism_Action_Development \
  Bacon_Classicism_ZF_Representation \
  Bacon_Core_Audit_Catalog \
  Bacon_Core_Audit_First \
  Bacon_Core_Theorem_Audit \
  Bacon_Classicism \
  Bacon_C_Equivalence_Development \
  Bacon_C_Presentation_Development \
  Bacon_H_Only_Classicism_Development \
  Bacon_H_Henkin_Equality_Development \
  Bacon_H_Henkin_Substitution_Development \
  Bacon_BBK_Semantics_Development \
  Bacon_Auxiliary_Bridge_Development \
  Bacon_General_Model_Development \
  Bacon_H_BBK_Canonical_Development \
  Bacon_H_BBK_Countable_Development \
  Bacon_H_BBK_Strong_Completeness_Development
