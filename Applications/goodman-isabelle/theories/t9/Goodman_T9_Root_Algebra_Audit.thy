theory Goodman_T9_Root_Algebra_Audit
  imports Goodman_T9_Root_Algebra
begin

ML \<open>
local
  val global_names = ["gi_T9_compose_builder_type", "gi_T9_compose_builder_logical",
    "gi_T9_compose_builder_apply", "gi_T9_value_identity_member", "gi_T9_value_compose_apply",
    "gi_T9_value_identity_left", "gi_T9_value_identity_right", "gi_T9_value_compose_associative"]
  val local_names = ["gi_T9_root_pure_member", "gi_T9_compose_pure", "gi_T9_identity_pure",
    "gi_T9_identity_left", "gi_T9_identity_right", "gi_T9_compose_associative", "gi_T9_group_pure",
    "gi_T9_identity_in_group", "gi_T9_group_inverse", "gi_T9_group_compose", "gi_T9_group_inverse_action",
    "gi_T9_same_kind_refl", "gi_T9_same_kind_sym", "gi_T9_same_kind_trans", "gi_T9_kind_self_member",
    "gi_T9_kind_eq_iff", "gi_T9_kind_closed", "gi_T9_kind_represented", "gi_T9_kind_rep_spec",
    "gi_T9_kind_fibre_orbit", "gi_T9_kind_code_spec", "gi_T9_kind_fibre_code"]
  val names = global_names @ map (fn name => "gi_T9_native_purity." ^ name) local_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length names = 30 andalso length facts = 31 then () else error "T9-root-algebra: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "T9-root-algebra: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T9-root-algebra: residual obligations in " ^ name)
  val report = "T9-ROOT-ALGEBRA-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual exact-carrier root-pure unary values under a typed interpretation validating the native T6 common core. Composition purity is derived from a closed logical builder and actual application closure. Exact units/associativity, pure reversible group/inverses, right-composition kinds, choice of representatives and injective fibre codes are proved. Locale assumptions and HOL-ZF foundations retained. No PC, L2, subset-selector injection or counting conclusion is asserted here. No free-action premise is used.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-root-algebra-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-root-algebra-statements.txt")) [XML.Text statements]
in end
\<close>

end
