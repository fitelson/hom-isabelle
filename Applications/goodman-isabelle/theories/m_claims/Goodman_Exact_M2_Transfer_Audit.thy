theory Goodman_Exact_M2_Transfer_Audit
  imports Goodman_Exact_M2_Transfer
begin

section \<open>Kernel audit of M2 on Bacon's exact carriers\<close>

ML \<open>
local
  val names = [
    "gi_exact_M2_extract_action",
    "gi_exact_M2_view_condition_admissible",
    "gi_exact_M2_classifier_member",
    "gi_exact_M2_classifier_apply",
    "gi_exact_M2_classifier_raw",
    "gi_exact_M2_raw_equivariant_commutes",
    "gi_exact_M2_raw_equivariant_invariant",
    "gi_exact_M2_classifier_invariant",
    "gi_exact_M2_classifier_in_stock",
    "gi_exact_M2_classifier_injective",
    "gi_exact_M2_invariant_representation",
    "gi_exact_M2_classifier_bijection",
    "gi_exact_M2_proposition_bijection",
    "gi_exact_M2_invariants_outnumber_propositions",
    "gi_exact_M2_collision",
    "gi_exact_M2_evaluation_not_injective",
    "gi_exact_M2_invariance_QSS_fails"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 17 then () else error "exact-M2: unexpected catalog size"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-M2: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-M2: residual obligations in " ^ name)
  val report = "EXACT-M2-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Classifiers are proved members of Bacon's exact unary carrier; exact substitution-action invariance and representation yield a bijection from all sets of raw propositions to exact invariant unary values. Exact proposition carriers are compared by their embed/extract bijection. Cantor gives strict cardinal excess, and a concrete pair of distinct exact invariant values agrees at every proposed typed fundamental proposition. HOL-ZF foundations retained. Invariant is not identified with logical purity; no PP/model-consistency claim or blanket native QSS-formula interpretation is asserted.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m2-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-m2-statements.txt")) [XML.Text statements]
in end
\<close>

end
