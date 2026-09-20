theory Goodman_Exact_10_1_Parametric_Audit
  imports Goodman_Exact_10_1_Parametric
begin

section \<open>Kernel audit of the name-parametric Theorem 10.1\<close>

ML \<open>
local
  val names = ["gi_named_consts_finite",
    "gi_named_consts_map",
    "gi_named_fv_map",
    "gi_exact_poly_propositional_string",
    "gi_exact_poly_propositional_map",
    "gi_exact_named_to_pterm_map",
    "gi_exact_decode_map",
    "gi_has_ptype_map",
    "gi_exact_poly_pterm_type",
    "gi_exact_renamed_decode_type",
    "gi_exact_renamed_decode_fragment",
    "gi_exact_decode_consts",
    "pp_e_eval_constant_agreement",
    "gi_exact_named_denote_constant_agreement",
    "gi_exact_finite_string_injection",
    "gi_exact_name_code_inj",
    "gi_exact_name_decode_code",
    "pp_e_eval_pterm_rename",
    "gi_exact_named_denote_rename",
    "gi_exact_poly_denote_string",
    "gi_exact_poly_denote_closed_assignment_independent",
    "gi_exact_poly_glued_as_string",
    "gi_exact_poly_glued_typed",
    "gi_exact_poly_glued_action",
    "gi_exact_poly_glued_renamed",
    "gi_exact_Bacon_10_1_parametric_action",
    "gi_exact_Bacon_10_1_parametric_truth_branch",
    "gi_exact_Bacon_10_1_parametric"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-10-1-parametric: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-10-1-parametric: residual obligations in " ^ name)
  val report = "EXACT-10-1-PARAMETRIC-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Bacon's Theorem 10.1 branch gluing for an arbitrary type of constant names: polymorphic evaluator gi_exact_poly_denote (coincides with gi_exact_named_denote at string names), alphabet-independent gluing gi_exact_poly_glued, and the action/truth/existence theorems for every closed named term of the t-generated fragment and every countable (nat-indexed) family typed at t-generated types. Name coding is per term on its finitely many constants; no injection of all names into strings and no countability of the signature is used or asserted. Type e remains excluded.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-10-1-parametric-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-10-1-parametric-statements.txt")) [XML.Text statements]
in end
\<close>

end
