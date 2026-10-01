# Working on the Proposition 2.11 application

Read README.md, STATUS.md, CONTRIBUTING.md and docs/SOURCE_CORRESPONDENCE.md.
This application investigates Proposition 2.11 and footnote 42 of the
1 July 2022 draft of Bacon–Dorr's *Classicism*. It is not a change to the
core theory and must not be imported by a core session.

Run `./check_isabelle.sh`; all Isabelle builds and exports remain serial,
with timeout=60 per session. No admissions, unexplained axioms or oracles.
Never use fresh/force/clean rebuild flags (including `isabelle build -f`)
or remove heap databases without explicit user approval. Such operations
can invalidate Pure/HOL and unrelated applications; use the ordinary
checker, which rebuilds changed sources and their dependents as needed.
The standard HOL and HOL–ZF foundations, including metatheoretic choice,
remain explicit. The free ultrafilter is constructed using the standard
library's existence theorem, not introduced as a new local axiom.

Keep the layers distinct: concrete Boolean calculations; all-type carrier
and operator closure; the book's exact model and interpretation; the paper's
literal Definitions 3.18–3.20; and the refutation layer under
`theories/refutation/` (object-language formulas, the consequence relation
`c211_proves`, generic semantics, concrete lattice and rigidity results).
The end-to-end refutation `proposition_2_11_refuted` is checked for the
intended lower-bound clause; always state that qualification. Do not claim
the boxed hypotheses, the footnote's actual-LUB identification or the
printed-clause inconsistency as machine-checked; they are not.

Use published terminology and readable Unicode prose. Do not confuse
the atom selecting the intermediate world with an atom true at the root.
The paper's displayed LB inequality is reversed; the mathematical note
uses ordinary intended lower bounds, not that malformed literal formula.

Only this application and Goodman are authorized for public inclusion.
Do not publish other local applications, source PDFs, private research
records, or raw consultation journals. Do not delete or move existing files
without explicit approval. Use system TeX Live for the report, preserve
Lucida/Forbes formatting, write `\neq` rather than `\ne`, and inspect the PDF.

No model consultation is implied by a later routine build request. The
initial requested Opus 5.5 High consensus audit is recorded separately;
its findings must be distinguished from kernel checking.
