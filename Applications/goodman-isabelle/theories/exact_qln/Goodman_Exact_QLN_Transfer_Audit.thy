theory Goodman_Exact_QLN_Transfer_Audit
  imports Goodman_Exact_QLN_Transfer
begin

section \<open>Kernel audit and native QLN statement export\<close>

ML \<open>
local
  val names = ["pp_e_constants.gi_exact_goodman_closed_global_translation",
    "pp_e_constants.gi_exact_goodman_empty_equivalence_transport",
    "pp_e_constants.gi_exact_goodman_closed_equivalence_transfer",
    "gi_exact_zeroary_recombination_vocabulary",
    "gi_exact_unary_recombination_vocabulary",
    "gi_exact_zeroary_exhaustion_vocabulary",
    "gi_exact_unary_exhaustion_vocabulary",
    "gi_exact_zeroary_recombination_admitted",
    "gi_exact_unary_recombination_admitted",
    "gi_exact_zeroary_exhaustion_admitted",
    "gi_exact_unary_exhaustion_admitted",
    "gi_exact_QLN_constants",
    "gi_exact_generic_zeroary_recombination_gvalid",
    "gi_exact_generic_unary_recombination_gvalid",
    "gi_exact_generic_zeroary_exhaustion_gvalid",
    "gi_exact_generic_unary_exhaustion_gvalid"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-QLN-transfer: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-QLN-transfer: residual obligations in " ^ name)
  val report = "EXACT-QLN-TRANSFER-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Native zeroary/unary Recombination and Exhaustion globally valid in the exact generic-seed interpretation, at every world and typed assignment; declared Goodman signature and source-name guards checked. HOL-ZF qualification retained. Not the distinct theorem-10.1 glued model, not a full-background assembly, and not PP.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-qln-transfer-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-qln-transfer-statements.txt")) [XML.Text statements]
in end
\<close>

end
