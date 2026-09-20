theory Goodman_Native_Finite_PC_Audit
  imports Goodman_Native_Finite_PC
begin

section \<open>Kernel audit of arbitrary-finite pure comprehension\<close>

ML \<open>
local
  val names = ["gi_PC_disj_type",
    "gi_PC_selector_type",
    "gi_PC_disj_reindex",
    "gi_PC_selector_apply_beta",
    "gi_PC_step_builder_type",
    "gi_PC_step_builder_logical",
    "gi_PC_step_beta1",
    "gi_PC_step_beta2",
    "gi_PC_step_beta3",
    "gi_PC_pure_beta_from",
    "gi_PC_empty_selector_pure",
    "gi_PC_selector_pure_from",
    "gi_PC_membership_theorem",
    "gi_PC_hyp_elim",
    "gi_PC_matrix_theorem",
    "gi_PC_sentence_theorem",
    "gi_CEV_finite_PC",
    "gi_CEV_finite_PC_exact_stock",
    "gi_CEV_finite_PC_empty",
    "gi_finite_PC_typed",
    "gi_PC_disj_translation",
    "gi_PC_disj_shift_translation",
    "gi_PC_selector_translation",
    "gi_PC_shifted_selector_translation",
    "gi_PC_hyp_translation",
    "gi_PC_membership_translation",
    "gi_PC_matrix_translation",
    "gi_PC_sentence_translation",
    "gi_finite_PC_native_translation",
    "gi_finite_PC_admitted",
    "gb_finite_PC_axioms_language",
    "gb_finite_PC_axioms_closed",
    "gb_finite_PC_axioms_subset_T1",
    "gi_finite_PC_stock_inclusion",
    "gi_finite_PC_axiom_from_native",
    "gi_finite_PC_native_preservation",
    "gi_native_finite_PC",
    "gi_native_finite_PC_empty",
    "gi_native_finite_PC_T1_stock",
    "gi_native_empty_selector_pure",
    "gb_finite_PC_language_closed"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "native-finite-pc: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("native-finite-pc: residual obligations in " ^ name)
  val report = "NATIVE-FINITE-PC-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Arbitrary-finite pure comprehension at every type: for n parameters of type sigma, Pure(a_i) for all i implies purity of the selector lambda x. (x = a_n or ... or x = a_1 or bottom) and its material membership biconditional; n = 0 is the empty selector. Stock = logical-purity schema + application-closure schema only (no PP, Exhaustion, Recombination). Explicit induction on n in the constructor calculus; literal chart translation; k-free native endpoints in gb_signature. Not infinite PC and not T9 external full PC.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-finite-pc-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-finite-pc-statements.txt")) [XML.Text statements]
in end
\<close>

end
