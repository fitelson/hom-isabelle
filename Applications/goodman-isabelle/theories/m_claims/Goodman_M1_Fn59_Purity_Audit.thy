theory Goodman_M1_Fn59_Purity_Audit
  imports Goodman_M1_Fn59_Purity
begin

section \<open>Kernel audit of the source-language footnote-59 purity proof\<close>

ML \<open>
local
  val names = ["typed_gi_M1_fn59_liar",
    "gi_M1_fn59_builder_constant_free",
    "typed_gi_M1_fn59_builder",
    "typed_gi_M1_fn59_instance",
    "typed_gi_M1_fn59_after_pure",
    "gi_M1_fn59_first_beta",
    "gi_M1_fn59_second_beta",
    "gi_M1_fn59_instance_beta_eta",
    "gi_M1_fn59_builder_purity_axiom",
    "gi_M1_fn59_application_closure",
    "gi_M1_fn59_PP",
    "gi_M1_fn59_purity_of_fun",
    "gi_M1_fn59_liar_pure",
    "gi_M1_fn59_liar_vocabulary",
    "gi_M1_fn59_liar_admitted",
    "gi_M1_fn59_native_shape",
    "gi_M1_native_fn59_liar_language",
    "gi_M1_native_fn59_liar_closed",
    "gi_M1_fn59_purity_of_fun_translation",
    "gi_M1_fn59_axioms_closed",
    "gi_M1_fn59_native_stock_inclusion",
    "gi_M1_fn59_native_axioms_language",
    "gi_M1_native_fn59_liar_pure",
    "gi_M1_fn59_translated_liar_pure"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "M1-fn59-purity: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("M1-fn59-purity: residual obligations in " ^ name)
  val report = "M1-FN59-PURITY-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Typed footnote59 liar and constant-free builder, two beta contractions, constructor CEV+ purity derivation, independent native liar/stock and source-language purity derivation in gb_signature. Stock retains logical purity, application closure, unary-classifier PP, AND Purity of Fun at t. No QSS/unique-fundamentality assumption is used in this purity proof; diagonal contradiction and model instantiation are separate.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m1-fn59-purity-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m1-fn59-purity-statements.txt")) [XML.Text statements]
in end
\<close>

end
