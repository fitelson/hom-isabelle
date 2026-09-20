theory Goodman_Exact_Stock_Audit
  imports Goodman_Exact_Stock_Correspondence
begin

section \<open>Kernel audit of closed decoding and complete logical-stock correspondence\<close>

text \<open>
  Every declared lemma/theorem/corollary of the two bridge theories is
  included below. Multi-conclusion facts are expanded into separately
  numbered theorem objects. Displayed assumptions are exported without
  being discharged or conflated with residual kernel hypotheses.

  The audit retains the HOL–ZF foundational setting. Zero oracle
  dependencies is not a claim that HOL–ZF's foundational axioms have
  themselves been proved consistent.
\<close>

ML \<open>
local
  val names = [
    "gi_pterm_empty_signature_const_free",
    "gi_closed_named_decode_type",
    "gi_closed_logical_decode",
    "gi_exact_old_closed_evaluation",
    "gi_closed_logical_decode_denotation",
    "gi_empty_signature_name_map_language",
    "gi_empty_signature_name_map_closed_logical",
    "gi_logical_string_roundtrip",
    "gi_goodman_closed_logical_decode_denotation",
    "gi_exact_native_closed_den_decoded",
    "gi_exact_native_closed_den_member",
    "gi_exact_native_closed_den_independent",
    "gi_old_closed_logical_native_witness",
    "gi_exact_logical_denotation_sets_equal",
    "gi_exact_native_stock_iff_original",
    "gi_exact_native_stock_independent_of_rich_names"]
  fun expand name =
    map_index (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
      (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val labels = map fst entries
  val facts = map snd entries
  val _ = if length names = 16 andalso length facts = 19 then ()
    else error "exact-stock: unexpected catalog size; review all multi-conclusion facts"
  val _ = if length (distinct (op =) labels) = length labels then ()
    else error "exact-stock: duplicate numbered endpoint"
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-stock: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-stock: residual obligations in " ^ name)
  val report = "EXACT-STOCK-AUDIT: " ^ string_of_int (length facts) ^
    " clean endpoints from " ^ string_of_int (length names) ^ " named facts\n" ^
    "SCOPE: Every closed logical native term decodes to a closed constant-free old term; literal denotation-set equality and local-Leibniz-saturated stock equality at every represented type and world. Richness is retained where stated. HOL-ZF foundations retained. No generic Pure/Fun interpretation, QLN instance, L2 transfer, arbitrary enlarged stock, or PP consistency is certified by these endpoints alone.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-stock-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-stock-statements.txt")) [XML.Text statements]
in end
\<close>

end
