theory Bacon_Source_Reverse_Set_Preservation
  imports Bacon_Source_Reverse_Proof_Preservation Bacon_Source_Local_Cut
    "Bacon_Parametric_Signature_Development.Bacon_Parametric_Local_Derivability"
begin

section \<open>Reverse translation of local target proofs\<close>

text \<open>
  A target derivation from T becomes a source derivation from the image
  of T under reverse syntax translation and a type-respecting variable map.
  Source role: finite assumption/theorem/MP consequence for the Figure 2
  logic (Bacon–Dorr pp.7–8).

  Isabelle representation: a list derivation is translated first.
  Each used assumption carries its own target typing and signature guards.
  Actual target H theorem leaves use the proved pH_to_paper_global_H.
  MP uses the literal reverse translation of PImp, namely paper_imp.

  Status: reverse local-proof preservation for arbitrary name carriers
  and premise sets. Richness supplies the source stock needed by theorem
  translation; no model, finiteness of T, or complete set-correspondence
  theorem is assumed.
\<close>

lemma pH_derivable_to_paper_global_derivable:
  assumes derivation: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    and rich: "sg_rich G"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_derivable \<Sigma> G
    (image (\<lambda>B. srename r (pterm_to_paper B)) (set \<Delta>))
    (srename r (pterm_to_paper A))"
  using derivation
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have member: "srename r (pterm_to_paper A) \<in>
    image (\<lambda>B. srename r (pterm_to_paper B)) (set \<Delta>)"
    by (rule imageI[OF Assumption.hyps(1)])
  have target_language: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF Assumption.hyps(2,3)])
  have source_language: "sgterm_in_language paper_logical_type \<Sigma> G
    (srename r (pterm_to_paper A)) Prop"
    by (rule paper_back_embedding_language[where G=G and r=r, OF target_language map])
  show ?case by (rule paper_global_derivable.Assumption[OF member source_language])
next
  case (Theorem A)
  have source: "paper_global_H \<Sigma> G (srename r (pterm_to_paper A))"
    by (rule pH_to_paper_global_H[where G=G and r=r, OF Theorem.hyps rich map])
  show ?case by (rule paper_global_derivable.Theorem[OF source])
next
  case (MP A B)
  have implication: "paper_global_derivable \<Sigma> G
    (image (\<lambda>C. srename r (pterm_to_paper C)) (set \<Delta>))
    (paper_imp (srename r (pterm_to_paper A)) (srename r (pterm_to_paper B)))"
    using MP.IH(2) by (simp only: pterm_to_paper.simps srename_paper_imp)
  show ?case by (rule paper_global_derivable.MP[OF MP.IH(1) implication])
qed

theorem pH_set_to_paper_global_derivable:
  assumes derivation: "pH_set_derivable \<Sigma> \<Gamma> T A"
    and rich: "sg_rich G"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "paper_global_derivable \<Sigma> G
    (image (\<lambda>B. srename r (pterm_to_paper B)) T)
    (srename r (pterm_to_paper A))"
proof -
  obtain \<Delta> where support: "set \<Delta> \<subseteq> T" and local: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    using derivation unfolding pH_set_derivable_def by (elim exE conjE)
  have translated: "paper_global_derivable \<Sigma> G
    (image (\<lambda>B. srename r (pterm_to_paper B)) (set \<Delta>))
    (srename r (pterm_to_paper A))"
    by (rule pH_derivable_to_paper_global_derivable[where G=G and r=r, OF local rich map])
  have included: "image (\<lambda>B. srename r (pterm_to_paper B)) (set \<Delta>) \<subseteq>
    image (\<lambda>B. srename r (pterm_to_paper B)) T"
    by (rule image_mono[OF support])
  show ?thesis by (rule paper_global_derivable_mono[OF translated included])
qed

corollary pH_closed_set_to_paper_global_derivable:
  assumes derivation: "pH_set_derivable \<Sigma> [] T A" and rich: "sg_rich G"
  shows "paper_global_derivable \<Sigma> G (image pterm_to_paper T) (pterm_to_paper A)"
proof -
  have map: "G (id n) = \<rho>" if "lookup [] n = Some \<rho>" for n \<rho>
    using that by (simp add: lookup_def)
  have translated: "paper_global_derivable \<Sigma> G
    (image (\<lambda>B. srename id (pterm_to_paper B)) T) (srename id (pterm_to_paper A))"
    by (rule pH_set_to_paper_global_derivable[where G=G and r=id, OF derivation rich map])
  show ?thesis using translated by (simp only: paper_reverse_srename_id)
qed

end
