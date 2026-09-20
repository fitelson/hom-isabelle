theory Goodman_M5_Nested_Collision_Audit
  imports Goodman_M5_Nested_Collision
begin

ML \<open>
local
  val names = ["gi_M5_nested_input_type", "gi_M5_PC1", "gi_M5_PC2", "gi_M5_PC3",
    "gi_M5_local_PC2", "gi_M5_local_PC3", "gi_M5_box_mono", "gi_M5_modal_T", "gi_M5_modal_four",
    "gi_M5_box_branch_stable", "gi_M5_nested_stable", "gi_M5_nested_dense", "gi_M5_nested_NC_equivalent",
    "gi_M5_nested_F_true", "gi_M5_F_truth_true", "gi_M5_nested_outputs_equal",
    "gi_M5_nested_input_false_locally", "gi_M5_nested_local_collision", "gi_M5_nested_local_nonreversibility",
    "gi_M5_nested_native_collision_translated", "gi_M5_nested_native_nonreversibility_translated"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "m5-nested-collision: oracle dependency"
  (* Inspect proof dependencies, not imports: the old axiom-stock collision
     is available in an ancestor theory, but must not prove this repair. *)
  val forbidden = [
    "CEV_Goodman_M5_collision",
    "CEV_Goodman_M5_collision_operator_not_reversible",
    "gi_M5_collision_source", "gi_M5_collision_in_signature",
    "gi_M5_nonreversible_in_signature",
    "gi_fixed_fun_prime_theorem_collapses_minimal_stock",
    "gi_fixed_fun_prime_axiom_collapses_minimal_stock",
    "gi_fixed_fun_prime_axiom_native_refutation"]
  val thy = @{theory}
  fun visit (i, node) seen =
    if Inttab.defined seen i then seen
    else
      let
        val seen' = Inttab.update (i, ()) seen
        val _ =
          (case Global_Theory.lookup_thm_id thy (Proofterm.thm_id (i, node)) of
            SOME ((name, _), _) =>
              if member (op =) forbidden (Long_Name.base_name name)
              then error ("M5 repair reaches an old collision/collapse theorem: " ^ name)
              else ()
          | NONE => ())
      in fold visit (Proofterm.thm_node_thms node) seen' end
  val checked_nodes = fold (fold visit o Thm.thm_deps) facts Inttab.empty
  val provenance = "DIRECT-PROVENANCE: " ^ string_of_int (Inttab.size checked_nodes) ^
    " proof nodes traversed; no historical axiom-stock collision or fixed-fun-prime collapse endpoint used.\n"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("m5-nested-collision: residual obligations in " ^ name)
  val report = "M5-NESTED-COLLISION-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: actual object-language repair using q=NC(Box r), not NC(r). Output identity proved over EMPTY added stock before local fun-prime assumption; only input inequality uses T2-min and MP-only local reasoning. Repaired collision/nonreversibility implications and scoped native transfer; no global-fun-prime axiom or PP model.\n"
    ^ provenance ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-nested-collision-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-nested-collision-statements.txt")) [XML.Text statements]
in end
\<close>

end
