# Instructions for work in this repository

Read README.md, STATUS.md, CONTRIBUTING.md, and docs/SOURCE_CORRESPONDENCE.md.
This repository's main development is the H/Classicism core. Applications
belong only under Applications/ and have their own instructions and checks.
The core must not import an application or the parent research checkout.
Goodman is an ordinary subfolder at Applications/goodman-isabelle, not a
submodule. Its presence does not expand the core's formal or audit scope.

Use the source book and paper, with the editions recorded in
docs/SOURCES_AND_CREDITS.md. Preserve source notation in Unicode comments.
Do not conflate F/R, local/global consequence, conditional/model-existence
claims, or HOL/HOL-ZF foundations.

Use ./check_isabelle.sh. Every Isabelle build, export and graph extraction
must be serialized. Sessions retain timeout=60; split slow proofs.
The root checker selects the core. Check Goodman separately with
./Applications/goodman-isabelle/check_isabelle.sh --export, also serially.
Do not change the core ROOT merely to include an application in its build.
No sorry, oops, admitted facts, quick_and_dirty, new oracles, or unexplained
axiomatizations. Check the actual theorem statement before reporting scope.

Do not delete or move files without explicit user approval. Preserve
unrelated edits. The countable-signature model-existence and generic
interpretation-existence theorems, with their audits, are selected in ROOT.
Neither result establishes generic full-C soundness or unrestricted modal
completeness. Interpretation uniqueness is on typed inputs, not on arbitrary
off-language values of the total evaluator.

The unchanged `book_ZF_modal_model` is the broad STRUCTURAL class.
Use the explicitly stronger `book_ZF_nontrivial_modal_model` for the
source-directed consistency target: every domain is inhabited and each
world has a false proposition. Its canonical/countable existence is checked.
The maintained singleton regression proves why the broad class is
insufficient. Read docs/MODAL_NONTRIVIALITY.md; do not erase this distinction.

Use the native graph via tools/isabelle_kg/query_graph.py, not Graphify.
Read docs/KNOWLEDGE_GRAPH.md. Rebuild it after source changes before relying
on exact dependencies. A graph edge is not a source-fidelity proof.

Update STATUS.md, the source table and audit coverage when changing claims.
Keep human documentation distinct from these operational instructions.
