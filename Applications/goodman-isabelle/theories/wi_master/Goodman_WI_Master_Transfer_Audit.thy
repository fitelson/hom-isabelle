theory Goodman_WI_Master_Transfer_Audit
  imports Goodman_WI_Master_Transfer
begin

section \<open>Kernel objects and direct-derivation provenance\<close>

ML \<open>
local
  val names = [
    "gi_WI_master_source_closed",
    "gb_WI_master_stock_language",
    "gi_WI_master_stock_inclusion",
    "gi_WI_master_preservation",
    "gi_WI_master_a_admitted",
    "gi_WI_master_operator_admitted",
    "gi_WI_master_at_admitted",
    "gi_WI_master_family_admitted",
    "gi_WI_advertised_master_admitted",
    "gi_WI_advertised_claim_admitted",
    "gi_WI_master_pointwise_direct_translated",
    "gi_WI_master_operator_pointwise_direct_translated",
    "gi_WI_master_family_direct_translated",
    "gi_WI_advertised_family_direct_translated",
    "gi_WI_advertised_closed_claim_direct_translated",
    "gi_WI_master_family_inconsistent_translated"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "WI-master: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("WI-master: residual obligations in " ^ name)

  (* Traverse actual proof-node dependencies, not theory imports or source
     text. Local contradiction arguments remain allowed; the forbidden
     nodes are the already completed stock refutation and ex-falso route. *)
  val direct_names = [
    "gi_WI_master_pointwise_direct_translated",
    "gi_WI_master_operator_pointwise_direct_translated",
    "gi_WI_master_family_direct_translated",
    "gi_WI_advertised_family_direct_translated",
    "gi_WI_advertised_closed_claim_direct_translated"]
  val forbidden = [
    "CEV_Goodman_T6_WI",
    "CEV_Goodman_T6_WI_advertised_master_claim_ex_falso",
    "CEV_axiom_explosion",
    "CEV_T6_WI_master_family_inconsistent",
    "CEV_T6_WI_advertised_master_inconsistent",
    "gi_native_T6_WI_refutation",
    "gi_T6_WI_refutation"]
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
              then error ("WI-master direct derivation reaches forbidden theorem: " ^ name)
              else ()
          | NONE => ())
      in fold visit (Proofterm.thm_node_thms node) seen' end
  val direct_facts = map (Proof_Context.get_thm @{context}) direct_names
  val checked_nodes = fold (fold visit o Thm.thm_deps) direct_facts Inttab.empty
  val provenance = "DIRECT-PROVENANCE: " ^ string_of_int (Inttab.size checked_nodes) ^
    " proof nodes traversed; no completed WI refutation, master-family contradiction, or ex-falso endpoint used.\n"
  val report = "WI-MASTER-TRANSFER-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Direct parameter equations use native core+L2+WI and explicit fun-prime/purity antecedents, typed charts and occurrence-sensitive signature guards. The closed advertised theorem retains its exact original existence-augmented stock. Conclusions are translated, not independently native master definitions. The separate closed arbitrary-operator family contradiction has only Pure(top) and the full family as axioms.\n" ^
    provenance ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "wi-master-transfer-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "wi-master-transfer-statements.txt")) [XML.Text statements]
in end
\<close>

end

