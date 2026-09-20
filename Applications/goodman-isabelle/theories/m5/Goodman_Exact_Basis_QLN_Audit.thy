theory Goodman_Exact_Basis_QLN_Audit
  imports Goodman_Exact_Basis_QLN
begin

section \<open>Basis QLN: exact statements and kernel checks\<close>

ML \<open>
local
  val names = ["gi_exact_invariant_basis.gi_basis_fundamental_raw",
    "gi_exact_invariant_basis.gi_basis_raw_universal_iff",
    "gi_exact_invariant_basis.gi_basis_value_unary_QLN",
    "gi_exact_invariant_basis.gi_basis_pure_unary_representative",
    "gi_exact_invariant_basis.gi_basis_related_applications",
    "gi_exact_invariant_basis.gi_basis_pure_unary_QLN",
    "gi_exact_invariant_basis.gi_basis_proposition_world_constant",
    "gi_exact_invariant_basis.gi_basis_pure_prop_true_imp_box",
    "gi_exact_invariant_basis.gi_basis_unary_recombination_holds_iff",
    "gi_exact_invariant_basis.gi_basis_unary_recombination_holds",
    "gi_exact_invariant_basis.gi_basis_unary_exhaustion_holds_iff",
    "gi_exact_invariant_basis.gi_basis_unary_exhaustion_holds",
    "gi_exact_invariant_basis.gi_basis_zeroary_recombination_holds",
    "gi_exact_invariant_basis.gi_basis_zeroary_exhaustion_holds_iff",
    "gi_exact_invariant_basis.gi_basis_zeroary_exhaustion_holds",
    "gi_exact_invariant_basis.gi_basis_native_zeroary_recombination_gvalid",
    "gi_exact_invariant_basis.gi_basis_native_unary_recombination_gvalid",
    "gi_exact_invariant_basis.gi_basis_native_zeroary_exhaustion_gvalid",
    "gi_exact_invariant_basis.gi_basis_native_unary_exhaustion_gvalid"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "basis-qln: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("basis-qln: residual obligations in " ^ name)
  val report = "BASIS-QLN-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: countable invariant typed application-closed basis containing all logical denotations; QLN is derived from the proved generic seed, not assumed. Four source directions at every world and four native global-validity endpoints; zeroary/unary only, unchanged exact carriers, no PP or assembled-model claim.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-qln-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-qln-statements.txt")) [XML.Text statements]
in end
\<close>

end
