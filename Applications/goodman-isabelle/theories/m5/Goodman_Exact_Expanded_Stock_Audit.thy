theory Goodman_Exact_Expanded_Stock_Audit
  imports Goodman_Exact_Expanded_Stock
begin

section \<open>Kernel audit of the complete expanded generating stock\<close>

ML \<open>
local
  val names = ["gi_M5_signature_occurrence_iff",
    "gi_M5_signature_translation_guard",
    "gi_M5_logical_in_expanded_signature",
    "gi_M5_expanded_basisI",
    "gi_M5_expanded_basisE",
    "gi_M5_expanded_basis_countable",
    "gi_exact_expanded_stock.gi_M5_basis_constants_typed",
    "gi_exact_expanded_stock.gi_M5_basis_constants_action",
    "gi_exact_expanded_stock.gi_M5_basis_named_constant_value",
    "gi_exact_expanded_stock.gi_M5_basis_reserved_names_default",
    "gi_exact_expanded_stock.gi_M5_basis_eval_action",
    "gi_exact_expanded_stock.gi_M5_expanded_closed_den_typed",
    "gi_exact_expanded_stock.gi_M5_expanded_closed_den_invariant",
    "gi_exact_expanded_stock.gi_M5_expanded_closed_eval_independent",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_typed",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_invariant",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_application",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_contains_logical",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_contains_K",
    "gi_exact_expanded_stock.gi_M5_named_expanded_basis_equal",
    "gi_exact_expanded_stock.gi_M5_expanded_basis_contains_native_logical"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-expanded-stock: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-expanded-stock: residual obligations in " ^ name)
  val report = "EXACT-EXPANDED-STOCK-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: All closed typed terms over one fresh constant declared ONLY at t-to-t, interpreted by an exact typed action-invariant K. Countability, typing, invariance, application closure, old logical inclusion and K membership; equality with the complete closed native string-language denotation set. The auxiliary C_K is NOT a Goodman Pure/Fun interpretation. No rebuilt model, saturation countability, or PP conclusion; HOL-ZF qualifications retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-expanded-stock-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-expanded-stock-statements.txt")) [XML.Text statements]
in end
\<close>

end

