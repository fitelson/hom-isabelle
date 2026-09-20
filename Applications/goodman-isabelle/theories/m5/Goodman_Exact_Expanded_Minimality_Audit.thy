theory Goodman_Exact_Expanded_Minimality_Audit
  imports Goodman_Exact_Expanded_Minimality
begin

ML \<open>
local
  val global_names = ["gi_M5_pconst_subst_eval", "gi_M5_pconst_removes_only_signature",
    "gi_M5_constant_abstractor_type", "gi_M5_constant_abstractor_logical",
    "gi_M5_abstracted_body_eval", "gi_M5_constant_abstractor_application",
    "gi_M5_expanded_basis_least", "gi_M5_application_hull_logical", "gi_M5_application_hull_K",
    "gi_M5_application_hull_closed", "gi_M5_expanded_basis_subset_application_hull"]
  val local_names = ["gi_M5_generated_in_expanded_basis", "gi_M5_expanded_basis_is_application_hull",
    "gi_M5_named_expanded_basis_is_application_hull"]
  val names = global_names @ map (fn name => "gi_exact_expanded_stock." ^ name) local_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 14 then () else error "expanded-minimality: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "expanded-minimality: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("expanded-minimality: residual obligations in " ^ name)
  val report = "EXPANDED-MINIMALITY-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Exact capture-avoiding typed-pair constant replacement preserves actual evaluator values. Every closed k-only term is a closed logical abstractor applied to K. Hence the COMPLETE expanded basis is the least all-type application-closed family containing every original logical denotation and K, and equals the three-rule inductive application hull; native expanded language inherits equality. No lambda-closure premise is assumed for candidate families. Typed K and displayed expanded-stock/richness assumptions retained, HOL-ZF foundations retained. Unsaturated basis only; no separate PP claim.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "expanded-minimality-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "expanded-minimality-statements.txt")) [XML.Text statements]
in end
\<close>

end
