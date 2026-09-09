theory Bacon_Source_Relational_Classicism_A2_MP_Closed
  imports Bacon_Source_Relational_Classicism_A2_H Bacon_Source_Relational_A2_MP_Environment_Syntax
    Bacon_Source_Relational_A2_MP_Closed_Updates Bacon_Source_Relational_A2_MP_Beta
begin

section \<open>MP preservation when the displayed prefix closes both premises\<close>

text \<open>
  Let K=λv⃗.Q, L=λv⃗.(Q→P), and T=λv⃗.⊤.
  The covering condition makes K,L,T closed. Replace K,L by T,T
  in λv⃗.(P∨(Xv⃗∧Yv⃗)) using two fresh function coordinates.
  Native self-β connects this calculation to P∨(Q∧(Q→P))
  and P∨(⊤∧⊤). The first is H-equivalent to P, and the
  second is an H theorem. Source: Appendix A.2, p.66.

  Every replacement is of CLOSED payloads. No arbitrary open identity
  is abstracted, and neither Equivalence nor general λ-congruence is
  assumed. The later arbitrary-prefix wrapper will supply the cover.
\<close>

theorem paper_R_classicism_A2_MP_closed:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and covered: "named_fv P \<union> named_fv Q \<subseteq> set ns"
    and first: "paper_R_classicism_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns Q) (named_lam_vec ns (paper_R_named_top G)))"
    and second: "paper_R_classicism_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G ns) Prop)
        (named_lam_vec ns (named_paper_imp G Q P)) (named_lam_vec ns (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  let ?K = "named_lam_vec ns Q"
  let ?L = "named_lam_vec ns (named_paper_imp G Q P)"
  let ?T = "named_lam_vec ns (paper_R_named_top G)"
  let ?PP = "named_lam_vec ns P"
  let ?B = "named_lam_vec ns (named_paper_or P (named_paper_and Q (named_paper_imp G Q P)))"
  let ?U = "named_lam_vec ns (named_paper_or P (named_paper_and (paper_R_named_top G) (paper_R_named_top G)))"
  let ?E = "\<lambda>K L. named_lam_vec ns (named_paper_or P
    (named_paper_and (named_app_vec K (map NVar ns)) (named_app_vec L (map NVar ns))))"
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have top: "paper_R_in_language \<Sigma> G (paper_R_named_top G) Prop" by (rule paper_R_named_top_language[OF rich])
  have implication: "paper_R_in_language \<Sigma> G (named_paper_imp G Q P) Prop"
    by (rule paper_R_named_paper_imp_language[OF rich ql pl])
  have kl: "paper_R_in_language \<Sigma> G ?K ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have ll: "paper_R_in_language \<Sigma> G ?L ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF implication binders])
  have tl: "paper_R_in_language \<Sigma> G ?T ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF top binders])
  have ppl: "paper_R_in_language \<Sigma> G ?PP ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have cover_P: "named_fv P \<subseteq> set ns" and cover_Q: "named_fv Q \<subseteq> set ns" using covered by blast+
  have cover_implication: "named_fv (named_paper_imp G Q P) \<subseteq> set ns"
    using covered by (simp only: named_paper_defined_fv; blast)
  have kc: "?K \<in> paper_R_closed_terms \<Sigma> G ?\<tau>"
    by (rule paper_R_closed_termsI[OF kl named_lam_vec_closed[OF cover_Q]])
  have lc: "?L \<in> paper_R_closed_terms \<Sigma> G ?\<tau>"
    by (rule paper_R_closed_termsI[OF ll named_lam_vec_closed[OF cover_implication]])
  have tc: "?T \<in> paper_R_closed_terms \<Sigma> G ?\<tau>"
    by (rule paper_R_closed_termsI[OF tl]; simp only: named_lam_vec_fv paper_R_named_top_closed; simp)
  have first_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?K ?T)"
    by (rule paper_R_named_derivable.Assumption; (use first in simp | rule paper_R_named_identity_language[OF kl tl]))
  have second_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?L ?T)"
    by (rule paper_R_named_derivable.Assumption; (use second in simp | rule paper_R_named_identity_language[OF ll tl]))
  have rt: "paper_R_type ?\<tau>" by (rule paper_R_language_result_type[OF kl])
  obtain x where xt: "G x = ?\<tau>" and xf: "x \<notin> set ns"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="?\<tau>" and S="set ns", OF rich rt finite_set])
  have finite: "finite (insert x (set ns))" by simp
  obtain y where yt: "G y = ?\<tau>" and yf: "y \<notin> insert x (set ns)"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>="?\<tau>", OF rich rt finite])
  have distinct: "x \<noteq> y" and yfresh: "y \<notin> set ns" using yf by auto
  have vx: "paper_R_in_language \<Sigma> G (NVar x) ?\<tau>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF xt rt])
  have vy: "paper_R_in_language \<Sigma> G (NVar y) ?\<tau>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=y, OF yt rt])
  have template: "paper_R_in_language \<Sigma> G (?E (NVar x) (NVar y)) ?\<tau>"
    by (rule paper_R_MP_vector_body_language[OF pl vx vy binders])
  have updates: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau>
    (paper_R_environment_subst ((Map.empty(x := Some ?K))(y := Some ?L)) (?E (NVar x) (NVar y)))
    (paper_R_environment_subst ((Map.empty(x := Some ?T))(y := Some ?T)) (?E (NVar x) (NVar y))))"
    by (rule paper_R_two_closed_updates_identity[OF rich template xt yt distinct kc lc tc first_local second_local])
  have replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?K ?L) (?E ?T ?T))"
    using updates by (simp only: paper_R_A2_MP_environment_evaluation[OF distinct xf yfresh cover_P])
  have start_tautology: "sprop_tautology (SPIff (SPAtom (0::nat))
    (SPOr (SPAtom 0) (SPAnd (SPAtom 1) (SPImp (SPAtom 1) (SPAtom 0)))))"
    by (auto simp: sprop_tautology_def)
  have start_H: "paper_R_named_H \<Sigma> G (named_paper_iff G P (named_paper_or P (named_paper_and Q (named_paper_imp G Q P))))"
    using paper_R_named_H_binary_PC[OF rich pl ql start_tautology] by simp
  have raw_body: "paper_R_in_language \<Sigma> G (named_paper_or P (named_paper_and Q (named_paper_imp G Q P))) Prop"
    by (rule paper_R_named_or_language[OF pl paper_R_named_and_language[OF ql implication]])
  have bl: "paper_R_in_language \<Sigma> G ?B ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF raw_body binders])
  have start_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> ?PP ?B)"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF start_H pl raw_body binders])
  have start_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?PP ?B)"
    by (rule paper_R_named_derivable.Assumption; (use start_C in simp | rule paper_R_named_identity_language[OF ppl bl]))
  have left_beta: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?K ?L) ?B)"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_MP_vector_self_identity[OF rich pl ql implication binders]])
  have right_beta: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> (?E ?T ?T) ?U)"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_MP_vector_self_identity[OF rich pl top top binders]])
  have end_tautology: "sprop_tautology (SPImp (SPAtom (1::nat)) (SPOr (SPAtom 0) (SPAnd (SPAtom 1) (SPAtom 1))))"
    by (auto simp: sprop_tautology_def)
  have end_schema: "paper_R_named_H \<Sigma> G (named_paper_imp G (paper_R_named_top G)
    (named_paper_or P (named_paper_and (paper_R_named_top G) (paper_R_named_top G))))"
    using paper_R_named_H_binary_PC[OF rich pl top end_tautology] by simp
  have top_body: "paper_R_in_language \<Sigma> G
    (named_paper_or P (named_paper_and (paper_R_named_top G) (paper_R_named_top G))) Prop"
    by (rule paper_R_named_or_language[OF pl paper_R_named_and_language[OF top top]])
  have end_H: "paper_R_named_H \<Sigma> G (named_paper_or P (named_paper_and (paper_R_named_top G) (paper_R_named_top G)))"
    by (rule paper_R_named_H.MP[OF paper_R_named_H_top[OF rich] end_schema top_body])
  have end_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> ?U ?T)"
    by (rule paper_R_classicism_A2_H[OF rich end_H binders])
  have ul: "paper_R_in_language \<Sigma> G ?U ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF top_body binders])
  have end_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?U ?T)"
    by (rule paper_R_named_derivable.Assumption; (use end_C in simp | rule paper_R_named_identity_language[OF ul tl]))
  have ekl: "paper_R_in_language \<Sigma> G (?E ?K ?L) ?\<tau>" by (rule paper_R_MP_vector_body_language[OF pl kl ll binders])
  have ett: "paper_R_in_language \<Sigma> G (?E ?T ?T) ?\<tau>" by (rule paper_R_MP_vector_body_language[OF pl tl tl binders])
  have beta_reverse: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?B (?E ?K ?L))"
    by (rule paper_R_named_identity_sym[OF rich ekl bl left_beta])
  have chain1: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?PP (?E ?K ?L))"
    by (rule paper_R_named_identity_trans[OF rich ppl bl ekl start_local beta_reverse])
  have chain2: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?PP (?E ?T ?T))"
    by (rule paper_R_named_identity_trans[OF rich ppl ekl ett chain1 replacement])
  have chain3: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?PP ?U)"
    by (rule paper_R_named_identity_trans[OF rich ppl ett ul chain2 right_beta])
  have final_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?PP ?T)"
    by (rule paper_R_named_identity_trans[OF rich ppl ul tl chain3 end_local])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF final_local]; simp)
qed

end
