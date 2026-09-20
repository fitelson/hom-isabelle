theory Goodman_Exact_Basis_Seed_Audit
  imports Goodman_Exact_Basis_Seed
begin

ML \<open>
local
  val short_names = ["gi_basis_raw_stock_countable", "gi_basis_raw_stock_equivariant",
    "gi_basis_raw_stock_classifier", "gi_basis_classifier_indices_countable",
    "gi_basis_equalizer_indices_countable", "gi_basis_generic_indices_countable",
    "gi_basis_raw_seed_exists", "gi_basis_raw_seed_spec", "gi_basis_raw_seed_index_condition",
    "gi_basis_raw_seed_classifier_QLN", "gi_basis_raw_seed_separates", "gi_basis_raw_seed_fun_prime",
    "gi_basis_raw_seed_fun_prime_native_predicate", "gi_basis_root_seed_member", "gi_basis_root_seed_extract",
    "gi_basis_seed_at_member", "gi_basis_seed_at_action", "gi_basis_fundamental_admissible",
    "gi_basis_internal_constants_typed", "gi_basis_internal_constants_locale",
    "gi_basis_eval_Pure", "gi_basis_eval_Fun", "gi_basis_eval_pure_holds", "gi_basis_eval_fun_holds"]
  val names = map (fn name => "gi_exact_invariant_basis." ^ name) short_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 24 then () else error "exact-basis-seed: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-basis-seed: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-basis-seed: residual obligations in " ^ name)
  val report = "EXACT-BASIS-SEED-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Conditional exact invariant-basis construction; the countable classifier/equalizer index union supplies the ACTUAL chosen generic seed and root raw QSS separation. Typed root/moving seeds and admissible Fun yield typed internal Pure/Fun constants and guarded evaluation clauses. Locale premises and HOL-ZF foundations retained. Not a completed global QLN/model certificate or PP construction; no fixed seed all-view freeness assertion.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-basis-seed-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-basis-seed-statements.txt")) [XML.Text statements]
in end
\<close>

end
