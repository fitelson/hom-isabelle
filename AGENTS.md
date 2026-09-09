# Instructions for work in this repository

Read README.md, STATUS.md, CONTRIBUTING.md, and docs/SOURCE_CORRESPONDENCE.md.
This is a standalone H/Classicism core repository. Do not introduce
applications or import from the parent research checkout.

Use the source book and paper, with the editions recorded in
docs/SOURCES_AND_CREDITS.md. Preserve source notation in Unicode comments.
Do not conflate F/R, local/global consequence, conditional/model-existence
claims, or HOL/HOL-ZF foundations.

Use ./check_isabelle.sh. Every Isabelle build, export and graph extraction
must be serialized. Sessions retain timeout=60; split slow proofs.
No sorry, oops, admitted facts, quick_and_dirty, new oracles, or unexplained
axiomatizations. Check the actual theorem statement before reporting scope.

Do not delete or move files without explicit user approval. Preserve
unrelated edits. The countable-signature model-existence theorem and its audit
are selected in ROOT. Do not promote this result to generic soundness or
unrestricted full-type modal completeness.

Use the native graph via tools/isabelle_kg/query_graph.py, not Graphify.
Read docs/KNOWLEDGE_GRAPH.md. Rebuild it after source changes before relying
on exact dependencies. A graph edge is not a source-fidelity proof.

Update STATUS.md, the source table and audit coverage when changing claims.
Keep human documentation distinct from these operational instructions.
