theory Bacon_Source_Relational_Identity_To_Biconditional
  imports Bacon_Source_Relational_Propositional_Identity_Derivations
    Bacon_Source_Relational_Classicism_A3
begin

section \<open>Identity implies the literal biconditional in native local H\<close>

lemma paper_R_named_derivable_identity_imp:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop P Q)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_imp G P Q)"
proof -
  have subset: "S \<subseteq> insert P S" by auto
  have moved: "paper_R_named_derivable \<Sigma> G (insert P S) (named_paper_eq Prop P Q)"
    by (rule paper_R_named_derivable_mono[where \<Sigma>=\<Sigma> and G=G and S=S and T="insert P S", OF equality subset])
  have assumed: "paper_R_named_derivable \<Sigma> G (insert P S) P"
    by (rule paper_R_named_derivable.Assumption; (rule insertI1 | rule pl))
  have conclusion: "paper_R_named_derivable \<Sigma> G (insert P S) Q"
    by (rule paper_R_named_derivable_propositional_identity[OF rich pl ql moved assumed])
  show ?thesis by (rule paper_R_named_derivable_deduction[OF rich pl conclusion])
qed

theorem paper_R_named_derivable_identity_iff:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop P Q)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_iff G P Q)"
proof -
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G P Q)"
    by (rule paper_R_named_derivable_identity_imp[OF rich pl ql equality])
  have reverse: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop Q P)"
    by (rule paper_R_named_identity_sym[OF rich pl ql equality])
  have second: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G Q P)"
    by (rule paper_R_named_derivable_identity_imp[OF rich ql pl reverse])
  have tautology: "sprop_tautology (SPImp (SPImp (SPAtom (0::nat)) (SPAtom 1))
    (SPImp (SPImp (SPAtom 1) (SPAtom 0)) (SPIff (SPAtom 0) (SPAtom 1))))"
    by (auto simp: sprop_tautology_def)
  have schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (named_paper_imp G P Q)
    (named_paper_imp G (named_paper_imp G Q P) (named_paper_iff G P Q)))"
    using paper_R_named_H_binary_PC[OF rich pl ql tautology] by simp
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G P Q) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich pl ql])
  have second_language: "paper_R_in_language \<Sigma> G (named_paper_imp G Q P) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich ql pl])
  have conditional: "paper_R_named_derivable \<Sigma> G S (named_paper_imp G (named_paper_imp G Q P) (named_paper_iff G P Q))"
    by (rule paper_R_named_derivable.MP[OF first paper_R_named_derivable.Theorem[OF schema]
      paper_R_named_paper_imp_language[OF rich second_language il]])
  show ?thesis by (rule paper_R_named_derivable.MP[OF second conditional il])
qed

text \<open>
  This is the identity-to-biconditional direction, derived by LL,
  native local deduction, and PC. It is not Propositional Equivalence
  and does not assume a semantic model. Source: Ref/LL, Figure 2,
  and the saturated formula step used with p.15, footnote 17.
\<close>

corollary paper_R_classicism_identity_iff:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and equality: "paper_R_classicism_proves \<Sigma> G (named_paper_eq Prop P Q)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_iff G P Q)"
proof -
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have member: "named_paper_eq Prop P Q \<in> ?S" using equality by simp
  have premise: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop P Q)"
    by (rule paper_R_named_derivable.Assumption[OF member paper_R_named_identity_language[OF pl ql]])
  have conclusion: "paper_R_named_derivable \<Sigma> G ?S (named_paper_iff G P Q)"
    by (rule paper_R_named_derivable_identity_iff[OF rich pl ql premise])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF conclusion]; simp)
qed

end
