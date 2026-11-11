theory Goodman_Lettie_Audit
  imports PoP_W.PoP_G100_W_Not_PP PoP_NUP.PoP_G100_NUP PoP_K6.PoP_G100_Kernel_ZF_Model
    PoP_PSI.Dowel_G100_PSI PoP_PPT.PoP_G100_PPt
begin

text \<open>
  Audit catalog for Jacob Lettie's Isabelle formalization (Purity of Pure team),
  included with permission and unmodified in \<open>theories/lettie_pp\<close> (sessions
  \<open>PoP_Main\<close>, \<open>PoP_SYN\<close>, \<open>PoP_W\<close>, \<open>PoP_NUP\<close>, \<open>PoP_K6\<close>, \<open>PoP_PSI\<close>,
  \<open>PoP_PPT\<close>; file hashes in \<open>verification/provenance/external.json\<close>).  This
  theory adds no proof.  It lists the principal theorems, \<open>w_not_pp\<close> first,
  and fails the build if any of them depends on an oracle (this includes
  skipped proofs) or has residual hypotheses or flex-flex pairs.
\<close>

ML \<open>
local
  val names = ["w_not_pp", "w_not_pp_C", "u_S", "u_S_C", "u_fun_ExUni", "nup_NUP_U", "nup_NUP",
    "cfp2_thm", "cfp2", "cfp6", "k7_HT1", "k6", "k6_plus", "syn_S", "syn_Psi", "ppt_k6",
    "ppt_plus_CFP"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then ()
    else error "Lettie audit: oracle dependency"
  fun check (n, t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("Lettie audit residual obligations: " ^ n)
  val report = "LETTIE-W-NOT-PP-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: Jacob Lettie's formalization (Purity of Pure team), included with permission and unmodified; theories/lettie_pp. "
    ^ "w_not_pp is a closed theorem of his calculus U_proves (no added-axiom rule) whose ten premises are antecedents of an implication concluding the negation of Purity of Pure at type t->t; "
    ^ "w_not_pp_C is the same implication in CEV_proves. "
    ^ "The remaining entries are his companion results (S, NUP, C_FP, K6, PSI, PPt) as stated in the statements export; "
    ^ "k6, k6_plus and ppt_k6 are consistency results proved in his HOL-ZF model, not refutations.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "lettie-w-not-pp-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n, t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "lettie-w-not-pp-statements.txt"))
    [XML.Text statements]
in end
\<close>

end
