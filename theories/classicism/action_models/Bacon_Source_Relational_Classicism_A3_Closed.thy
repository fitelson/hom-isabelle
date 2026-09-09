theory Bacon_Source_Relational_Classicism_A3_Closed
  imports Bacon_Source_Relational_Classicism_A2 Bacon_Source_Relational_A3_Closed_Context
    Bacon_Source_Relational_Classicism_Identity_Consequences
begin

section \<open>The p.67 selector calculation at a closed covering prefix\<close>

text \<open>
  A.2 identifies K=λv⃗.(A↔B) with T=λv⃗.⊤.
  When v⃗ covers FV(A)∪FV(B), both are closed. The selector
  context transports this identity using only closed-payload LL/β.
  Native H certifies A↔selector(B,A↔B) and selector(B,⊤)↔B;
  the self-β identities connect those endpoints to the context.
  Source: Appendix A.3, p.67.

  The premise is a theorem of the p.12 C judgment, not a derivation
  in the independently specified recursive Equivalence presentation. No general
  abstraction congruence or semantic completeness premise is used.
\<close>

theorem paper_R_classicism_A3_closed:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and covered: "named_fv A \<union> named_fv B \<subseteq> set ns"
    and premise: "paper_R_classicism_proves \<Sigma> G (named_paper_iff G A B)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns A) (named_lam_vec ns B))"
proof -
  let ?I = "named_paper_iff G A B"
  let ?K = "named_lam_vec ns ?I"
  let ?T = "named_lam_vec ns (paper_R_named_top G)"
  let ?E = "paper_R_A3_vector_context ns B"
  let ?Start = "paper_R_A3_selector B ?I"
  let ?End = "paper_R_A3_selector B (paper_R_named_top G)"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have il: "paper_R_in_language \<Sigma> G ?I Prop" by (rule paper_R_named_paper_iff_language[OF rich al bl])
  have top: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have kl: "paper_R_in_language \<Sigma> G ?K ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF il binders])
  have tl: "paper_R_in_language \<Sigma> G ?T ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF top binders])
  have cover_I: "named_fv ?I \<subseteq> set ns" using covered by (simp only: named_paper_defined_fv)
  have cover_B: "named_fv B \<subseteq> set ns" using covered by blast
  have kc: "?K \<in> paper_R_closed_terms \<Sigma> G ?\<tau>"
    by (rule paper_R_closed_termsI[OF kl named_lam_vec_closed[OF cover_I]])
  have tc: "?T \<in> paper_R_closed_terms \<Sigma> G ?\<tau>"
    by (rule paper_R_closed_termsI[OF tl]; simp only: named_lam_vec_fv paper_R_named_top_closed; simp)
  have truth: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> ?K ?T)"
    by (rule paper_R_classicism_A2[OF rich premise binders])
  let ?S = "{P. paper_R_classicism_proves \<Sigma> G P}"
  have truth_member: "named_paper_eq ?\<tau> ?K ?T \<in> ?S" using truth by simp
  have truth_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?K ?T)"
    by (rule paper_R_named_derivable.Assumption[OF truth_member paper_R_named_identity_language[OF kl tl]])
  have replacement_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?K) (?E ?T))"
    by (rule paper_R_A3_closed_context_identity[OF rich bl binders cover_B kc tc truth_local])
  have replacement: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (?E ?K) (?E ?T))"
    by (rule paper_R_local_H_in_classicism[OF replacement_local]; simp)
  have start_tautology: "sprop_tautology (SPIff (SPAtom (0::nat))
    (SPOr (SPAnd (SPAtom 1) (SPIff (SPAtom 0) (SPAtom 1)))
      (SPAnd (SPNot (SPAtom 1)) (SPNot (SPIff (SPAtom 0) (SPAtom 1))))))"
    by (auto simp: sprop_tautology_def)
  have start_H: "paper_R_named_H \<Sigma> G (named_paper_iff G A ?Start)"
    using paper_R_named_H_binary_PC[OF rich al bl start_tautology] by (simp add: paper_R_A3_selector_def)
  have sl: "paper_R_in_language \<Sigma> G ?Start Prop" by (rule paper_R_A3_selector_language[OF bl il])
  have el: "paper_R_in_language \<Sigma> G ?End Prop" by (rule paper_R_A3_selector_language[OF bl top])
  have start: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns A) (named_lam_vec ns ?Start))"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF start_H al sl binders])
  have left_beta: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (?E ?K) (named_lam_vec ns ?Start))"
    by (rule paper_R_classicism_proves.H[OF paper_R_named_H_A3_self_identity[OF rich bl il binders]])
  have right_beta: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (?E ?T) (named_lam_vec ns ?End))"
    by (rule paper_R_classicism_proves.H[OF paper_R_named_H_A3_self_identity[OF rich bl top binders]])
  have end_tautology: "sprop_tautology (SPImp (SPAtom (1::nat))
    (SPIff (SPOr (SPAnd (SPAtom 0) (SPAtom 1)) (SPAnd (SPNot (SPAtom 0)) (SPNot (SPAtom 1)))) (SPAtom 0)))"
    by (auto simp: sprop_tautology_def)
  have end_schema: "paper_R_named_H \<Sigma> G
    (named_paper_imp G (paper_R_named_top G) (named_paper_iff G ?End B))"
    using paper_R_named_H_binary_PC[OF rich bl top end_tautology] by (simp add: paper_R_A3_selector_def)
  have end_H: "paper_R_named_H \<Sigma> G (named_paper_iff G ?End B)"
    by (rule paper_R_named_H.MP[OF paper_R_named_H_top[OF rich] end_schema paper_R_named_paper_iff_language[OF rich el bl]])
  have finish: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns ?End) (named_lam_vec ns B))"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF end_H el bl binders])
  have la: "paper_R_in_language \<Sigma> G (named_lam_vec ns A) ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF al binders])
  have lb: "paper_R_in_language \<Sigma> G (named_lam_vec ns B) ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF bl binders])
  have ls: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?Start) ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF sl binders])
  have le: "paper_R_in_language \<Sigma> G (named_lam_vec ns ?End) ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF el binders])
  have ek: "paper_R_in_language \<Sigma> G (?E ?K) ?\<tau>" by (rule paper_R_A3_vector_language[OF bl kl binders])
  have et: "paper_R_in_language \<Sigma> G (?E ?T) ?\<tau>" by (rule paper_R_A3_vector_language[OF bl tl binders])
  have beta_reverse: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns ?Start) (?E ?K))"
    by (rule paper_R_classicism_identity_sym[OF rich ek ls left_beta])
  have chain1: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns A) (?E ?K))"
    by (rule paper_R_classicism_identity_trans[OF rich la ls ek start beta_reverse])
  have chain2: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns A) (?E ?T))"
    by (rule paper_R_classicism_identity_trans[OF rich la ek et chain1 replacement])
  have chain3: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> (named_lam_vec ns A) (named_lam_vec ns ?End))"
    by (rule paper_R_classicism_identity_trans[OF rich la et le chain2 right_beta])
  show ?thesis by (rule paper_R_classicism_identity_trans[OF rich la le lb chain3 finish])
qed

end
