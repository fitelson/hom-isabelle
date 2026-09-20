theory Goodman_Native_Biconditional_Algebra_Audit
  imports Goodman_Native_Biconditional_Algebra
begin

section \<open>Kernel audit of the packaged biconditional-operator algebra\<close>

ML \<open>
local
  val names = ["gi_CEV_bic_self_inverse",
    "gi_CEV_bic_operator_pure",
    "gi_CEV_bic_group_member",
    "gi_bic_self_inverse_typed",
    "gi_bic_operator_pure_typed",
    "gi_bic_group_member_typed",
    "gi_bic_builder_shift",
    "gi_bic_self_inverse_translation",
    "gi_bic_operator_pure_translation",
    "gb_bic_builder_chart_alpha",
    "gi_bic_group_member_alpha",
    "gi_bic_self_inverse_admitted",
    "gi_bic_operator_pure_admitted",
    "gi_bic_group_member_admitted",
    "gi_T6_core_axioms_closed",
    "gi_T6_core_axiom_from_native",
    "gi_T6_core_native_preservation",
    "gi_native_bic_self_inverse_empty_stock",
    "gi_native_bic_self_inverse",
    "gi_native_bic_operator_pure",
    "gi_native_bic_group_member_translated",
    "gi_native_bic_group_member",
    "gb_bic_self_inverse_language_closed",
    "gb_bic_operator_pure_language_closed"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "native-biconditional-algebra: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("native-biconditional-algebra: residual obligations in " ^ name)
  val report = "NATIVE-BICONDITIONAL-ALGEBRA-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Biconditional operators B_a = lambda p.(p iff a): self-inverse (B_a o B_a = id) as a C+ theorem over every added stock including the empty one; Pure(a) implies Pure(B_a) and B_a in G over the native T6 PP core (purity, application closure, PP). Group membership reached by alpha transport of the literal translation. No WI, Inv, L2, Exhaustion or fun-prime; not the exact-root T9 algebra.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-biconditional-algebra-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-biconditional-algebra-statements.txt")) [XML.Text statements]
in end
\<close>

end
