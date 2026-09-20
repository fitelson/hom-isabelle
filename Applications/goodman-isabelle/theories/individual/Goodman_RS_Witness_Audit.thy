theory Goodman_RS_Witness_Audit
  imports Goodman_TU_RS_Witness
begin

section \<open>Audit of exact statements and kernel proof objects\<close>

ML \<open>
local
  val names = ["gi_RS_plus_type",
    "gi_RS_plus_builder_type",
    "gi_RS_plus_builder_logical",
    "gi_RS_plus_builder_beta",
    "gi_RS_plus_pure",
    "gi_RS_plus_shift",
    "gi_RS_plus_subst",
    "gi_RS_plus_apply_type",
    "gi_RS_plus_beta",
    "gi_RS_plus_apply_iff",
    "gi_RS_plus_elim",
    "gi_RS_plus_intro",
    "gi_RS_plus_only_fun_prime",
    "gi_RS_plus_exist_intro",
    "gi_RS_plus_instantiated_from_fun_prime",
    "gi_RS_plus_instantiated",
    "gi_RS_standard_same_truth_equal",
    "gi_RS_plus_rigidity_local",
    "gi_RS_plus_rigid_parameter",
    "gi_RS_plus_rigid",
    "gi_CEV_TU_RS_explicit_witness",
    "gi_CEV_TU_Exhaustion_PP_exists_implies_RS",
    "gi_CEV_TU_RS_exact_witness",
    "gi_CEV_TU_RS_exact_stock"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "rs-witness: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("rs-witness: residual obligations in " ^ name)
  val report = "RS-WITNESS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Explicit true-and-fun-prime witness; PP+zeroary Exhaustion+exists fun-prime+TU; no L2/strong L2/T6 explosion. Constructor CEV+ endpoints.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "rs-witness-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "rs-witness-statements.txt")) [XML.Text statements]
in end
\<close>

end

