theory Goodman_Exact_L2_Transfer_Audit
  imports Goodman_Exact_L2_Transfer
begin

section \<open>Kernel audit and exact statements for the native fixed-stock counterexample\<close>

ML \<open>
local
  val names = [
    "gi_exact_native_operator_stock_eq",
    "gi_exact_native_operator_stockI",
    "gi_exact_native_operator_stockE",
    "gi_exact_native_operator_stock_countable",
    "gi_exact_native_identity_in_stock",
    "gi_exact_native_operator_stock_compose",
    "gi_exact_native_fun_prime_iff",
    "gi_exact_native_reversible_iff",
    "gi_exact_native_group_eq",
    "gi_exact_native_same_kind_iff",
    "gi_exact_native_L2_pair_iff",
    "gi_exact_native_L2_iff",
    "gi_exact_native_strong_L2_pair_iff",
    "gi_exact_native_strong_L2_iff",
    "gi_exact_native_right_cancellative_iff",
    "gi_exact_native_child_variation_logical_witness",
    "gi_exact_native_child_variation_in_stock",
    "gi_exact_native_fun_prime_exists",
    "gi_exact_native_child_variation_right_cancellative",
    "gi_exact_native_child_variation_nonreversible",
    "gi_exact_native_child_variation_preserves_fun_prime",
    "gi_exact_native_child_variation_not_identity_kind",
    "gi_exact_native_child_variation_certificate",
    "gi_exact_native_L2_counterexample",
    "gi_exact_native_L2_false",
    "gi_exact_native_strong_L2_false"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val labels = map fst entries
  val _ = if length names = 26 andalso length facts = 31 then ()
    else error "exact-native-L2: unexpected catalog size"
  val _ = if length (distinct (op =) labels) = length labels then ()
    else error "exact-native-L2: duplicate numbered endpoint"
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-native-L2: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-native-L2: residual obligations in " ^ name)
  val report = "EXACT-NATIVE-L2-AUDIT: " ^ string_of_int (length facts) ^
    " clean endpoints from " ^ string_of_int (length names) ^ " named facts\n" ^
    "SCOPE: Literal equality of the complete native closed-logical raw unary stock with the historical exact stock; independently stock-parametric fun-prime, reversible, same-kind, L2/strong-L2 definitions; logical child-variation denotability, surjectivity, noninjectivity, cancellation, nonreversibility, a nonempty fun-prime class, and a concrete id/child-variation L2 collision. Richness and HOL-ZF foundations retained. No object-language L2 evaluation or arbitrary/enlarged Pure stock is asserted by this catalog alone; no PP model or consistency conclusion.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-native-l2-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-native-l2-statements.txt")) [XML.Text statements]
in end
\<close>

end
