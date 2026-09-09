theory Bacon_Source_Relational_Identity_Proof_Basics
  imports Bacon_Source_Relational_Existence
begin

section \<open>Native β consequences use only H certificates and local MP\<close>

lemma paper_R_named_H_iff_forward:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A Prop"
    and right: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_iff G A B) (named_paper_imp G A B))"
proof -
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich left right])
  have cl: "paper_R_in_language \<Sigma> G (named_paper_imp G A B) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich left right])
  have whole: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_iff G A B) (named_paper_imp G A B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich il cl])
  have tautology: "sprop_tautology (SPImp (SPIff (SPAtom (0::nat)) (SPAtom 1)) (SPImp (SPAtom 0) (SPAtom 1)))"
    by (auto simp: sprop_tautology_def)
  show ?thesis by (rule paper_R_named_H_PC_instance[OF whole tautology,
    where v="\<lambda>i. if i=0 then A else B"]; simp)
qed

lemma paper_R_named_derivable_beta_iff:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A Prop"
    and right: "paper_R_in_language \<Sigma> G B Prop"
    and step: "named_compatible_step named_beta_contract A B"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow> paper_R_named_derivable \<Sigma> G S B"
proof -
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich left right])
  have conversion: "paper_R_named_H \<Sigma> G (named_paper_iff G A B)"
    by (rule paper_R_named_H.Beta[OF left right step il])
  have forward: "paper_R_named_H \<Sigma> G (named_paper_imp G A B)"
    by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_forward[OF rich left right]
      paper_R_named_paper_imp_language[OF rich left right]])
  have backward: "paper_R_named_H \<Sigma> G (named_paper_imp G B A)"
    by (rule paper_R_named_H.MP[OF conversion paper_R_named_H_iff_backward[OF rich left right]
      paper_R_named_paper_imp_language[OF rich right left]])
  show ?thesis
  proof
    assume a: "paper_R_named_derivable \<Sigma> G S A"
    show "paper_R_named_derivable \<Sigma> G S B"
      by (rule paper_R_named_derivable.MP[OF a paper_R_named_derivable.Theorem[OF forward] right])
  next
    assume b: "paper_R_named_derivable \<Sigma> G S B"
    show "paper_R_named_derivable \<Sigma> G S A"
      by (rule paper_R_named_derivable.MP[OF b paper_R_named_derivable.Theorem[OF backward] left])
  qed
qed

section \<open>Typed identity formulas and the literal LL instance\<close>

lemma paper_R_named_identity_operator_language:
  assumes rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
proof -
  have er: "paper_R_type (paper_logical_type (SEq \<sigma>))" using rt by simp
  have et: "paper_R_has_type G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_R_has_type.Logical[where G=G and l="SEq \<sigma>", OF er] by simp
  show ?thesis unfolding paper_R_in_language_def by (rule conjI[OF et]; simp)
qed

lemma paper_R_named_identity_language:
  assumes left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
  unfolding named_paper_eq_def
  by (rule paper_R_language_App[OF paper_R_language_App[
    OF paper_R_named_identity_operator_language[OF paper_R_language_result_type[OF left]] left] right])

lemma paper_R_named_derivable_LL:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
    and antecedent: "paper_R_named_derivable \<Sigma> G S (NApp F A)"
  shows "paper_R_named_derivable \<Sigma> G S (NApp F B)"
proof -
  have eq: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF left right])
  have fa: "paper_R_in_language \<Sigma> G (NApp F A) Prop" by (rule paper_R_language_App[OF predicate left])
  have fb: "paper_R_in_language \<Sigma> G (NApp F B) Prop" by (rule paper_R_language_App[OF predicate right])
  have conditional_language: "paper_R_in_language \<Sigma> G (named_paper_imp G (NApp F A) (NApp F B)) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich fa fb])
  have ll_language: "paper_R_in_language \<Sigma> G
    (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B))) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich eq conditional_language])
  have ll: "paper_R_named_derivable \<Sigma> G S
    (named_paper_imp G (named_paper_eq \<sigma> A B) (named_paper_imp G (NApp F A) (NApp F B)))"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H.LL[OF ll_language]])
  have conditional: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (NApp F A) (NApp F B))"
    by (rule paper_R_named_derivable.MP[OF equality ll conditional_language])
  show ?thesis by (rule paper_R_named_derivable.MP[OF antecedent conditional fb])
qed

end
