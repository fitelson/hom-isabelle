# The Isabelle Theories

::center::Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions

::center::9 November 2026

## 1. What is here

This folder holds one Isabelle/HOL theory with six companion theories, seven theories in all, and the three `ROOT` files that build them. Each theory proves its results in the Isabelle kernel. None adds an axiom, and no proof uses `sorry` or an oracle.

- **`ROOT`** (25 lines): the five sessions `PoP_Main`, `PoP_SYN`, `PoP_W`, `PoP_NUP` and `PoP_K6`.
- **`t/PoP_G100_Kernel.thy`** (1,602 lines; session `PoP_Main`): the main theory.
- **`syn/PoP_G100_Syn.thy`** (258 lines; session `PoP_SYN`): S. Its header comment's "the supplementary note" is *Weaker Theories That Still Refute Purity of Pure*, and S is that note's §5.
- **`w/PoP_G100_W_Not_PP.thy`** (35 lines; session `PoP_W`): W.
- **`nup/PoP_G100_NUP.thy`** (286 lines; session `PoP_NUP`): the main proof's named pieces.
- **`k6/PoP_G100_Kernel_ZF_Model.thy`** (56 lines; session `PoP_K6`): K6, the model of C_{FP}.
- **`psi/ROOT`** (5 lines): the session `PoP_PSI`.
- **`psi/Dowel_G100_PSI.thy`** (129 lines; session `PoP_PSI`): `syn_Psi`.
- **`ppt/ROOT`** (5 lines): the session `PoP_PPT`.
- **`ppt/PoP_G100_PPt.thy`** (273 lines; session `PoP_PPT`): the PP_{t} companion, the model of C_{FP} + PP_{t}.

**The sessions.** `PoP_Main` holds the main theory. `PoP_SYN`, `PoP_W` and `PoP_NUP` each build on it, and `PoP_PSI` builds on `PoP_SYN`. `PoP_K6` builds on the library's exact model, with `PoP_Main` named in its `sessions` clause, and `PoP_PPT` builds on `PoP_K6`. Two companions have their own `ROOT` files: `syn_Psi`'s theory, in `psi/`, and the PP_{t} companion, in `ppt/`.

**The library.** The theories use Branden Fitelson's hom-isabelle repository (`https://github.com/fitelson/hom-isabelle`), which holds a base library and, in `Applications/goodman-isabelle`, the Goodman library. **The version used** is the repository at its commit of 26 September 2026. Its files are, byte for byte, the ones the theories were built and checked on: the repository's own list of that commit's files names the same 2,053 paths as the copy used here, and each file's git hash is the same. The main theory imports two of its theories and nothing else:
- `Goodman_Legacy_01.Bacon_PP_Question`, from the Goodman library;
- `Bacon_Source_Vocabulary_Development.Bacon_Source_Syntax`, from the base library.

K6 also imports two theories of the library's exact model of C: `Goodman_Exact_Recombination.Bacon_PP_ZF_Exact_Recombination` and `Goodman_Exact_Legacy_07.Bacon_PP_ZF_Exact_CEV_Soundness`. The PP_{t} companion imports K6's theory and `Goodman_Legacy_01.Bacon_PP_Modalized_Functionality_Derived`, the library's proof that proposition-valued Modalized Functionality is a theorem of CEV. That theory's session is already below K6, so it adds three library theories past K6 and no library session.

**Getting the library.** The repository's page at that commit is `https://github.com/fitelson/hom-isabelle/tree/c53fa28c6655cf2190c65992a079e9bcd388f9e3`, and its archive downloads from `https://github.com/fitelson/hom-isabelle/archive/c53fa28c6655cf2190c65992a079e9bcd388f9e3.zip`. Unzipped, the archive is one folder, whose name begins `hom-isabelle-`, holding the repository's 2,053 files. Its licence, the BSD 2-Clause License, is in that folder's `LICENSE`.

**Checking the download.** Make a list of the unzipped folder's files: for each file, its SHA-256 hash in hexadecimal, two spaces, and its path from the folder, one line per file, each ending in a newline, with the lines sorted by path in byte order, as the command in `CHECKSUMS.md` sorts them (a sort that follows the locale gives a different result); leave out any macOS Finder file named `.DS_Store`. Then hash the list with SHA-256. The result should equal the library's line in `CHECKSUMS.md`, at the root of this zip.

`PoP_Main` sits on the library's base session, `Bacon_Base`, and loads the library theories it needs from source. So the five sessions without the HOL-ZF part need no library image but `Bacon_Base`'s; K6 and the PP_{t} companion rest on the library's exact model, which takes 27 more.

## 2. The results

Each result is stated here as formalized. The main theory and K6 hold ten:

| Name | What it states | Theory |
| :--- | :--- | :--- |
| `cfp2` | C_{FP} proves ¬PP_{u}, in the local calculus over C: Purity Is Not Pure | main |
| `u_S` | the calculus U (H with Propositional Equivalence at type t alone) proves S → ¬∃Uni: given the nine claims and PP_{u}, no proposition is universal | main |
| `k7_HT1` | for each type τ ≠ t built from t alone, C_{FP} proves ¬PP_{τ} | main |
| `cfp6` | the claims S6 prove Exhaustion_{0} | main |
| `u_S_C` | `u_S` carried to C | main |
| `k6` | C_{FP} does not prove ⊥ in the local calculus | K6 |
| `k6_plus` | the same for C_{FP} with its claims necessitated | K6 |
| `k6_model` | every claim of C_{FP} is valid in the library's exact generic model | K6 |
| `k6_ctl_PP` | in that model ¬PP_{u} is valid: a control | K6 |
| `k6_ctl_dist` | in that model, Recombination at n = 2 without its distinctness clause is not valid: a control | K6 |

**K6 rests on HOL-ZF:** its imports from the exact model bring HOL-ZF's set axioms. No theory below the main theory has ZF in its name (§3), so the main theory's results do not rest on HOL-ZF.

### S and W

| Name | What it states |
| :--- | :--- |
| `syn_S` | C proves, for every T of type u→t, that Φ_{T} fails. Φ_{T} says that T holds necessarily of P_{T} and P′_{T}; that T is closed under Y ↦ λz.Y(Q_{T}(z)); that each Y that T holds of satisfies Fun-WP; and EF. The context is empty, and no premise mentions Pure. With P-1. |
| `syn_S_term` | the same at each term T of type u→t |
| `s_pi` | the instance at π in U, in every context |
| `s_no_Pure` | the statement of `syn_S` mentions no Pure |
| `w_not_pp` | U proves that W's ten claims imply ¬PP_{u}; `w_not_pp_C` is the same in C. With P-2. |

**P-1, for `syn_S`.** The theories write F as □(¬R(x, ¬x) ∧ ¬R(¬x, x)), where the main note, *If a Proposition Is Fundamental, Purity Is Not Pure*, writes □¬N(x), with N(x) = R(x, ¬x) ∨ R(¬x, x). In C the two are one operator, by the vector rule: C's rule that operators proved to agree at every argument are identical. So `syn_S` is the theorem of C in §5 of *Weaker Theories That Still Refute Purity of Pure*, up to β and that identity of C, which is not kernel-checked here.

**P-2, for `w_not_pp`.** U cannot carry ¬(a ∨ b) = (¬a ∧ ¬b) under λ, so over U the two forms of F may give different claims, and that was not tested. **So `w_not_pp` is W ⊢ ¬PP_{u} for W with the conjunctive F.** W as Appendix A of *Weaker Theories That Still Refute Purity of Pure* writes it is machine-checked in C in this zip's Metamath file (`w-not-pp`), and over H + PE it holds at sketch level, by the main note's proof.

### The main proof's named pieces

Each piece is a theorem of U, and so of C (each has a `_C` form). F, Q, P, P′, R and U are the main note's (§4.2): F(x), "x is firm"; Q(x) := F(x) → x; P(z) := ¬z ∧ ¬F(z); P′(z) := z ∧ ¬F(z).

| Name | The piece, in the main note's words |
| :--- | :--- |
| `nup_lemA` | Lemma A: if x is firm, it is necessarily firm |
| `nup_lemB` | Lemma B: if x is firm, Q(x) = x |
| `nup_lemC` | Lemma C: F(¬x) = F(x) |
| `nup_lemD` | Lemma D: if Q(x) is false, Q(x) is firm |
| `nup_cor` | Step 1's claim: necessarily, no Q(x) has P |
| `nup_ident` | the identity: P′(z) = P(¬z) |
| `nup_step1` | Step 1: the four lemmas and Step 1's claim, for every proposition x |
| `nup_step2` | Step 2: if π(P) and π(P′) are necessary, every Q(x) is firm |
| `nup_step3` | Step 3: from the nine claims and PP_{u}, π(P) and π(P′) are necessary, every Q(x) is firm, and λz.Y(Q(z)) is pure when Y is |
| `nup_step3_T` | Step 3 again, from LP, Application, PP_{u} and Exhaustion_{0}, in the local calculus over C |
| `nup_step4` | Step 4: if every Q(x) is firm and λz.Y(Q(z)) is pure when Y is, no proposition is universal |
| `nup_NUP_U` | the assembly in U, from Steps 3 and 4 alone: the nine claims and PP_{u} give ¬∃x U(x), the statement of `u_S` |
| `nup_NUP` | the assembly over C: LP, Application, PP_{u} and Exhaustion_{0} give ¬∃x U(x), No Universal Proposition |
| `nup_F_eq` | the bridge: at each x, the theories' F(x) equals the main note's □¬N(x), with N(x) := R(x, ¬x) ∨ R(¬x, x) |

### `syn_Psi`

| Name | What it states |
| :--- | :--- |
| `syn_Psi` | In the calculus of `cfp2`, with the claims of C_{FP} as premises: C_{FP} ⊢ ∀T ¬Ψ_{T}, for T of type u→t. Ψ_{T} says that Pure(T); that T holds of P_{T} and P′_{T}; that T is closed under Y ↦ λz.Y(Q_{T}(z)); and that ∀Y(T(Y) → Pure(Y)). P_{T}, P′_{T} and Q_{T} are as for `syn_S`. The claims it uses are at most nine: LP at three closed terms, Application at three type pairs, Exhaustion_{0}, Recombination_{1} and EF. With P-1. |
| `syn_Psi_thm` | a theorem of C, with no claim as premise: the conjunction of those nine claims implies ∀T ¬Ψ_{T}. `syn_Psi` follows from it by modus ponens. |

It is the sharper form of `syn_S` over C_{FP}. What it leaves to the models, at sketch level, is the step from PP^{syn}'s condition at a world to Ψ_{T} at that world.

### The PP_{t} companion

| Name | What it states |
| :--- | :--- |
| `ppt_plus_CFP` | C_{FP} proves PP_{t}, that is Pure_{t→t}(Pure_{t}), in CEV with C_{FP}'s claims added as axioms and closed under C's rules, so that the claims are taken under necessitation. This is the calculus of `k6_plus`. |
| `ppt_plus_L` | the same from six claims: LP at ⊤, at ⊥, at λq.¬q and at NC := λp.(□p ∨ □¬p); Application at (t, t); and Exhaustion_{0}. Five of them, all but LP at NC, are used under necessitation. |
| `ppt_plus` | the same over any set of claims that contains those six |
| `ppt_L_sub` | the six are claims of C_{FP} |
| `ppt_valid` | PP_{t} is valid in K6's model |
| `ppt_model` | every claim of C_{FP}, and PP_{t}, is valid in K6's model |
| `ppt_k6` | C_{FP} + PP_{t} does not prove ⊥ in the local calculus |
| `ppt_k6_plus` | the same with the claims of C_{FP} and PP_{t} necessitated |

The proof goes by way of Pure_{t} = NC. The claims give Pure_{t}(p) ↔ NC(p). Propositional Equivalence, necessitation and the library's Modalized Functionality then give Pure_{t} = NC, and LP at NC gives PP_{t}. The last four results rest on K6's model, and so on HOL-ZF.

## 3. What sits below

Counted by theory list:

| The result's theory | Theories below, with itself | Main | HOL past Main | Library | Ours |
| :--- | ---: | ---: | ---: | ---: | ---: |
| the main theory | 129 | 99 | 7 | 22 | 1 |
| S, W and the named pieces | 130 each | 99 | 7 | 22 | 2 |
| `syn_Psi`'s theory | 131 | 99 | 7 | 22 | 3 |
| K6 | 155 | 99 | 15 | 39 | 2 |
| the PP_{t} companion | 159 | 99 | 15 | 42 | 3 |

- **HOL past Main,** below the main theory: five `HOL-Library` theories (Countable, Countable_Set, Infinite_Set, Nat_Bijection and Old_Datatype), `HOL.Rat` and `HOL.Archimedean_Field`.
- **Four ancestors of the main theory carry completeness names:** `Bacon_Completeness`, `Bacon_Clean_Completeness`, `Bacon_Supported_Canonical` and `Bacon_Clean_Canonical_Base`. They come in through `Bacon_PP_Question`.
- **No result reaches any of them by name.** A walk of each result's proof dependencies, by a session that did not build the theories, reaches no theorem with "completeness" in its name, in any case. A completeness theorem planted in a result was caught each time.
- **K6 rests on HOL-ZF and the library's exact model:** past the main theory's ancestors, its own add eight more HOL theories, HOL-ZF's MainZF, HOLZF, Zet and LProd among them, and the exact model's theories. None of these is below the main theory.
- **The PP_{t} companion rests on K6's model.** Past K6's ancestors it adds three theories of the library's `Goodman_Legacy_01`: `Bacon_PP_Intensionality`, `Bacon_PP_Modalized_Functionality` and `Bacon_PP_Modalized_Functionality_Derived`.

## 4. To check it

You need Isabelle2025-2 and the repository's archive at that commit (§1). Write LIB for the unzipped archive's folder. From the top folder of this zip, the folder that holds `3-isabelle/`, run:

| The command |
| :--- |
| `isabelle build -d LIB -d LIB/Applications/goodman-isabelle -d 3-isabelle -d 3-isabelle/psi -d 3-isabelle/ppt PoP_Main PoP_SYN PoP_W PoP_NUP PoP_PSI PoP_K6 PoP_PPT` |

It should print "Finished" for each of the seven sessions and exit 0. To leave out the part on HOL-ZF, drop `PoP_K6` and `PoP_PPT`, which rests on it:

| The command |
| :--- |
| `isabelle build -d LIB -d LIB/Applications/goodman-isabelle -d 3-isabelle -d 3-isabelle/psi PoP_Main PoP_SYN PoP_W PoP_NUP PoP_PSI` |

- **What it builds.** Isabelle2025-2 comes with HOL and its libraries, HOL-ZF among them, already built. From the library's sources in LIB, the first command builds the 28 library sessions the theories rest on, from `Bacon_Base` up to `Goodman_Exact_Recombination`, and then the seven. The second builds `Bacon_Base` and the five.
- **What was run.** On a fresh copy of this zip, with Isabelle2025-2 and no stored images but its own, and with LIB a copy of the repository whose files are byte for byte those at that commit, the first command passed in 4 minutes 9 seconds on a MacBook Air, with 4 threads. Two settings that the machine's sandbox needs, a folder for temporary files and the thread count, were set; a reader needs neither.

## 5. How it was checked

Each check below was made by a session that did not build what it checked.

- **No shortcuts.** Twenty-eight results are checked by name: the ten of the main theory and K6, `syn_S`, `syn_S_term`, `s_pi`, `s_no_Pure`, `w_not_pp`, `w_not_pp_C`, `nup_NUP`, `nup_NUP_U`, `syn_Psi` and `syn_Psi_thm`, and the eight of the PP_{t} companion. At each, Isabelle records no oracle, no skipped proof, no hypothesis and no open pair of terms to unify. No named fact of any of the seven theories has an oracle or a skipped proof. A planted skipped proof is reported.
- **Cut, not rewritten.** The main theory was cut from nine theories built earlier by Dowel and Loupe. Each kept block is its source's text, byte for byte, and each kept fact's statement equals its source's.
- **Moved without change.** The theories were then moved onto the two imports used here, with the imports line changed and nothing else. Every fact equals its twin in the earlier build, both ways, as an exact term. The companions in `psi/` and `ppt/` were then rebuilt on them, and every fact of each equals its twin in its original build.
- **This edition.** For this zip, the comments were rewritten and nothing formal changed. Each theory opens with a title block, its sections carry numbered headers, and its text blocks and the `ROOT` comments name no working records or labels. The sessions were renamed, with the six imports lines that name them. Theory names, statements and proofs are unchanged, and every file keeps its line count.
- **Checked on this edition.** Built from a fresh copy of the zip, all 530 facts of the seven theories equal their earlier twins, both ways, as exact terms, and the 28 results checked by name carry no oracle.
- **The PP_{t} companion.** Its paper argument was checked, while the build ran, by a session that had not seen it.
- **The walk:** §3.
- **A reader's build:** a session that did not build the theories built them from a fresh copy; and the build from nothing in §4.

## 6. Where the results sit in the notes

- *If a Proposition Is Fundamental, Purity Is Not Pure*: `cfp2` is §3's result, and §4.3 puts it together from FMU (§4.1) and NUP (§4.2). The named pieces are §4.2's, and `nup_NUP` is NUP over C.
- *Weaker Theories That Still Refute Purity of Pure*: `syn_S` is §5's theorem of C, with P-1, and `syn_Psi` is the sharper form over C_{FP} that §7 names. `w_not_pp` backs §2.2's W ⊢ ¬PP_{u}, with P-2.
- *Purity Is Not Pure at Higher Types*: `k7_HT1` is §2's first result. `ppt_model` and `ppt_k6` give the fact that §7's class B and §8 ("At t") use: C_{FP} + PP_{t} holds in a model, and derives no ⊥.
- *How the Result Was Checked*: §3's paragraph on *Purity Is Not Pure at Higher Types* names the PP_{t} results, and §8, *Where to look*, maps each result in the notes to its name here, with a row for them.

## Acknowledgements

The theories are by Dowel and Loupe. Tamis moved them onto narrow imports and made this edition. Helm, Rabbet, Reticle and Tamis inspected them, each a session that had not built what it inspected. The route to PP_{t} is Reticle's, and Caltrop put it in C_{FP}'s terms; Rabbet checked its paper argument. The library is Branden Fitelson's, under its BSD licence, and was built for Fitelson by chatbot instances. We thank Fitelson, and those instances, for it.
