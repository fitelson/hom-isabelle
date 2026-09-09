theory Bacon_Source_Relational_Positive_Diagram_Consistency
  imports Bacon_Source_Relational_Positive_Diagram Bacon_Source_Relational_Separating_Consistency
begin

section \<open>Instantiating the positive premises of the separating argument\<close>

text \<open>
  For an R BBK model M of an H-theory T closed under PE, distinct
  proposition values give consistency of T∪Δ(M)∪{¬(P↔Q)}.
  The diagram is now the defined set of true closed identities, rather
  than an arbitrary supplied premise set. Source: p.51–52 n.73.

  This theorem still assumes T in the current signature. Applying it
  after naming every element requires the separately constructed M⁺
  and an appropriately extended theory. Neither signature-extension
  closure nor a separating homomorphism follows from this lemma alone.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_positive_diagram_separating_consistent:
  assumes theory_h: "paper_R_H_theory signature stock T"
    and pe: "paper_R_PE_closed signature stock T"
    and theory_valid: "\<And>E. E \<in> T \<Longrightarrow> paper_R_valid E"
    and pl: "paper_R_in_language signature stock P Prop"
    and ql: "paper_R_in_language signature stock Q Prop"
    and typed: "named_env_typed domain stock g"
    and pa: "named_adequate g P" and qa: "named_adequate g Q"
    and different: "denote g P \<noteq> denote g Q"
  shows "paper_R_named_consistent signature stock
    (insert (named_paper_not (named_paper_iff stock P Q))
      (T \<union> paper_R_positive_diagram signature stock denote))"
proof (rule paper_R_identity_diagram_separating_consistent[
    OF theory_h pe _ theory_valid _ pl ql typed pa qa different])
  fix E
  assume member: "E \<in> paper_R_positive_diagram signature stock denote"
  show "\<exists>\<sigma> A B. E = named_paper_eq \<sigma> A B \<and>
    paper_R_in_language signature stock A \<sigma> \<and> paper_R_in_language signature stock B \<sigma>"
    using paper_R_positive_diagramE[OF member] by blast
next
  fix E
  assume member: "E \<in> paper_R_positive_diagram signature stock denote"
  show "paper_R_valid E" by (rule paper_R_positive_diagram_valid[OF member])
qed

end

end
