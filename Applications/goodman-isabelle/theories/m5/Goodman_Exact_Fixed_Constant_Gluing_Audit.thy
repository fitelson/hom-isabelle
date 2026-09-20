theory Goodman_Exact_Fixed_Constant_Gluing_Audit
  imports Goodman_Exact_Fixed_Constant_Gluing
begin

section \<open>Kernel audit of exact gluing with a literally fixed primitive\<close>

ML \<open>
local
  val names = ["gi_exact_fixed_glued_constants_typed",
    "gi_exact_fixed_glued_constant_at",
    "gi_exact_fixed_glued_constant_other",
    "gi_exact_fixed_glued_completed_action",
    "gi_exact_fixed_glued_branch_action",
    "gi_exact_fixed_glued_closed_term_action",
    "gi_exact_fixed_glued_named_term_action",
    "gi_exact_fixed_glued_named_truth_branch",
    "gi_exact_Bacon_10_1_fixed_constant_named"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-fixed-constant-gluing: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-fixed-constant-gluing: residual obligations in " ^ name)
  val report = "EXACT-FIXED-CONSTANT-GLUING-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Explicit overwrite of one typed constant coordinate by exact typed invariant K; literal fixed value, completed-family action equations, and t-generated closed-term/named-term branch gluing. Countable family, common fixed coordinate, fragment and invariance premises retained. No all-Ind gluing or assertion that unmodified gluing fixes K; not a rebuilt Pure/Fun model. HOL-ZF foundation retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-fixed-constant-gluing-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-fixed-constant-gluing-statements.txt")) [XML.Text statements]
in end
\<close>

end

