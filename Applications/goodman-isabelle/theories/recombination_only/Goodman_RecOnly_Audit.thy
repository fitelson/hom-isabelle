theory Goodman_RecOnly_Audit
  imports Goodman_RecOnly_Final
begin

text \<open>
  Audit catalog for Recombination without Exhaustion (hand proof:
  reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11).  This theory adds no proof.
  It lists the 31 principal theorems, the final statements last, and fails the build if any of
  them depends on an oracle (this includes skipped proofs) or has residual hypotheses or
  flex-flex pairs.  The statements export also gives the three U-statements with the premise
  abbreviations unfolded.
\<close>

ML \<open>
local
  val names = ["ro_ClW", "ro_base", "ro_boxed", "ro_ClG", "ro_mW", "ro_piW", "ro_pure_a",
    "ro_closure_true", "ro_lemA", "ro_lemB", "ro_lemC", "ro_lemD", "ro_cor", "ro_ident",
    "ro_guarded", "ro_relative", "ro_Phi_pure", "ro_Phi_pres", "ro_actual", "ro_certificate",
    "ro_Fa", "ro_uni_rel", "ro_Rae", "ro_contra", "ro_thm1", "ro_thm1_U", "ro_cor_EF_U",
    "ro_cor_U", "ro_thm1_CEVs", "ro_recombination_refutes_PP", "ro_recombination_PP_inconsistent"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then ()
    else error "Recombination-only audit: oracle dependency"
  fun check (n, t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("Recombination-only audit residual obligations: " ^ n)
  fun str t = XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} t))
  fun unfolded n = str (Thm.prop_of (Local_Defs.unfold @{context}
    @{thms roLA_def roHC0_def roHF_def roPrem_def roHC_def pp_target_PP_def pp_purity_of_pure_def}
    (Proof_Context.get_thm @{context} n)))
  val report = "RECOMBINATION-ONLY-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: Recombination without Exhaustion, built on Jacob Lettie's unmodified kernel PoP_Main. "
    ^ "ro_thm1_U is a closed theorem of Lettie's calculus U_proves (no added-axiom rule) whose antecedents are "
    ^ "twenty Logical Purity and Application instances (roLA) and Purity of Pure at type t->t; its consequent "
    ^ "denies that a universal proposition exists. ro_cor_EF_U and ro_cor_U add a fundamental proposition and "
    ^ "Lettie's H5 (Logical Purity at negation, Application at (u,u), unary Recombination). "
    ^ "ro_thm1_CEVs, ro_recombination_refutes_PP and "
    ^ "ro_recombination_PP_inconsistent are in the ordinary-premise relation CEV_set_derivable over C. "
    ^ "No Exhaustion is used. The other entries are the steps of the hand proof.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "recombination-only-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n, t) => n ^ ":\n" ^ str (Thm.prop_of t)) entries)
    ^ "\n\nUNFOLDED FINAL STATEMENTS\n"
    ^ cat_lines (map (fn n => n ^ ":\n" ^ unfolded n) ["ro_thm1_U", "ro_cor_EF_U", "ro_cor_U"])
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "recombination-only-statements.txt"))
    [XML.Text statements]
in end
\<close>

end
