theory Goodman_Exact_Kind_Root_Audit
  imports Goodman_Exact_Kind_Root
begin

section \<open>Kernel audit of actual root inverse and same-kind clauses\<close>

ML \<open>
local
  val names = [
    "gi_exact_raw_stock_iff",
    "gi_exact_identity_denotation",
    "gi_exact_identity_denotation_member",
    "gi_exact_root_compose_eq_iff",
    "gi_exact_root_inverse_eq_iff",
    "gi_exact_reversible_body_root",
    "gi_exact_reversible_value_witness",
    "gi_exact_reversible_root_iff",
    "gi_exact_group_member_root_iff",
    "gi_exact_same_kind_root_iff"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 10 then () else error "exact-kind-root: unexpected catalog size"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-kind-root: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-kind-root: residual obligations in " ^ name)
  val report = "EXACT-KIND-ROOT-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual root evaluation in the exact generic interpretation. Pure unary values correspond to the literal raw stock. pp_reversible asserts a stock inverse only; pp_group_member additionally asserts purity of the argument and matches pp_e_exact_reversible. pp_same_kind matches X=Y composed with a pure reversible input re-description. Typed terms, typed environments, and exact-domain premises remain explicit. HOL-ZF foundations retained; no non-root, enlarged-stock, full L2, or PP assertion in this catalog alone.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-kind-root-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-kind-root-statements.txt")) [XML.Text statements]
in end
\<close>

end
