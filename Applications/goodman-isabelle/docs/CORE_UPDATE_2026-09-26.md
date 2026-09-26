# Core compatibility update — 26 September 2026

This maintenance checkpoint adopts the enclosing core's new full-C modal
soundness/completeness development. It does not resume the open Goodman
research tasks or change an existing Goodman theorem.

## Core results and their scope

`Bacon_Book_ZF_Modal_Soundness` proves generic full-C soundness for the
independent **nontrivial** book modal models and, for countably declared
signatures, derivability iff root modal consequence and consistency iff
satisfiability. The language has full simple types and the book's minimal
primitive vocabulary; the variable stock is rich. Domains are inhabited
and each world has a false proposition. The documented future-restricted
implication convention remains. Open formulas and infinite premise sets
are allowed. Soundness itself does not require countability.

See the [core source guide](../../../docs/SOURCE_CORRESPONDENCE.md) and
[completeness theory](../../../theories/classicism/book/modal_semantics/soundness/Bacon_Book_ZF_Full_C_Completeness.thy).
Its 31-endpoint audit is separate from Goodman's 1,708 integration entries.

## What this changes for Goodman

`book_full_C_theory_derivable Σ G T A` is ordinary theory consequence:
C theorems are supplied globally, but additional premises need only hold
at the root under all typed assignments there. `goodman_book_proves Σ G T A`
is an **axiom extension**: PE, and hence derived Necessitation, can operate
above T. Root truth of T alone does not discharge the global extension-
soundness premises in Goodman's existing model theorems.

The existing `goodman_book_closure_theory_iff` and
`goodman_book_closure_consistency_iff` identify this extension with ordinary
C consequence/consistency of its full deductive closure Cl(T), not of the
original raw stock T. The new completeness theorem can be applied at that
closure, with its language/countability hypotheses. It does not prove
Cl(T) consistent or construct a model of Goodman's PP target. No new
theorem packaging this application is claimed in this checkpoint.

Goodman's question, contributor tasks 6–9, and the arbitrary-carrier M1
model/extension-soundness adapters remain open in their documented scopes.
The exact no-PP models, L2 refutation and repaired M5 results retain their
existing statements. The exact-frame representation and Theorem 10.1 are
not reclassified as unrestricted syntactic completeness. No new Pure/Fun
model, backward old/new calculus equivalence or Functionality redundancy
is asserted.

## Reviewed dependency delta

The pin changes from 1,382 to **1,390** ROOT/ROOTS/theory/ML entries.
Exactly eight files were added under core
`theories/classicism/book/modal_semantics/soundness/`:

- `Bacon_Book_ZF_Modal_Naturality.thy`
- `Bacon_Book_ZF_Modal_Truth_Clauses.thy`
- `Bacon_Book_ZF_Modal_Identity_Clauses.thy`
- `Bacon_Book_ZF_Modal_Conversion.thy`
- `Bacon_Book_ZF_Modal_H_Soundness.thy`
- `Bacon_Book_ZF_Full_C_Soundness.thy`
- `Bacon_Book_ZF_Full_C_Completeness.thy`
- `Bacon_Book_ZF_Modal_Soundness_Audit.thy`

Exactly three pinned files changed: ROOT selects the new session;
`Bacon_Book_Classicism_Closed_Successor.thy` and
`Bacon_Book_Full_Classicism_Closed_Successor.thy` each update only a status
comment. No prior proof body changed and no file was removed. The
independent model definitions were not replaced. The staged core reviews
and saved clean audit were inspected with the actual theorem statements
and Goodman's existing closure bridge.

Previous manifest SHA-256:
`d29215c43c1051efdc4bab516240d2ebe2cabffe156659d2236c00b40fa8e204`;
recorded revision `8dc5940a664172459da3bddaba3d72b067b359c3`.
The refreshed manifest records base HEAD
`57ccf8e43b01f1431b195ae279bb0d4257abc194` **plus the reviewed working-tree
source checkpoint**. The base commit alone does not contain the new files.
This is not a claim that the checkpoint is committed or pushed. Embedded
checks use exact hashes; standalone use requires both the recorded revision
and matching source checkpoint. No hash or revision guard was disabled.

## Verification

Input checks initially passed: all 1,390 core entries matched, all 82
preserved Goodman files retained their hashes, and all ten packaging tests
passed. The full build/export is **pending**, not a successful new
compatibility certificate. A concurrent core-development job first
triggered the conservative process guard; subsequent changes added
`Bacon_Book_Named_Syntax_Cardinal.thy` and altered ROOT, so the exact-source
guard now rejects the moving checkout. Those unfinished changes have not
been silently included in this reviewed pin. See
[verification/README.md](../verification/README.md).
All 303 Goodman theories and 87 audit catalogs remain unchanged.

## Second delta, later the same day: ZF-small name carriers

The core then replaced the countability restriction of its full-C model
existence and completeness theorems by ZF-smallness of the whole name
carrier (`Bacon_Book_ZF_Small_Carrier_Existence.thy`,
`Bacon_Book_ZF_Full_C_Small_Carrier_Completeness.thy`), keeping the countably
declared theorems on arbitrary carriers. That development was
independently reviewed (an implementation review and a follow-up pass,
records kept by the maintainer); the complete serial core check and graph
rebuild passed. The pin was refreshed to that checkpoint: 1,396 entries, six added
core theories (`Bacon_Book_Named_Syntax_Cardinal`, `Bacon_Book_Ambient_Signature`,
`Bacon_Book_ZF_Coded_Frame`, `Bacon_Book_ZF_Small_Carrier_Existence`,
`Bacon_Book_ZF_Small_Carrier_Audit`,
`Bacon_Book_ZF_Full_C_Small_Carrier_Completeness`), 70 changed files (ROOT,
the book canonical-world/frame theories, whose world set gained a cardinal
reserve clause, and the HOL-ZF representation theories, now parameterised
by a bounded term code), none removed. Base revision still
`57ccf8e43b01f1431b195ae279bb0d4257abc194` plus the reviewed working-tree
checkpoint.

For Goodman nothing changes mathematically: no Goodman theory imports a
changed or added core theory; the closure-bridge reading above applies to
both completeness scopes. The full build/export passed with every audited
entry unchanged (see [verification/README.md](../verification/README.md)).

## Third refresh, later on 26 September 2026

The core then completed a comprehensive repository audit (sixteen module
reviews by two independent reviewers, verdict SOUND WITH CHANGES with no
blocker) and applied its changes: the relevant-language (λI) development
through original-signature model existence and global strong completeness
(session `Bacon_Book_Lambda_I_Development`, 72 theories) with a regression
session exhibiting an actual λI model, new audit coverage for the older
H–BBK completeness endpoints and the generic action-validity endpoint, three
countable-compatibility lemmas added to the book audits, and comment,
label, scope-banner and documentation corrections. The pin was refreshed to
that checkpoint: 1,473 entries, 77 added core files, 70 changed (comment,
banner and catalog edits; the base `Bacon_Deduction` header among them),
none removed, base revision unchanged. None of the core theories Goodman
imports changed in any theorem, definition or proof. The full serial
Goodman check and export passed (exit 0, 4 minutes 9 seconds, 60 sessions,
87 catalogs, 1,708 integration entries and 9 replay entries, all identical
to the retained certificates; two provenance proof-node counts changed).

