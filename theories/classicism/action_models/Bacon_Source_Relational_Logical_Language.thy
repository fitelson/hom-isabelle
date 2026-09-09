theory Bacon_Source_Relational_Logical_Language
  imports Bacon_Source_Relational_Application_Graph
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Logical_Syntax
begin

section \<open>The literal → and ↔ operators belong to R\<close>

text \<open>
  Figure 1 defines →=λpq.¬p∨q and
  ↔=λpq.(¬p∨q)∧(¬q∨p), with distinct p,q:t.
  Source: Bacon–Dorr pp.5–6. We retain the existing literal named
  definitions and prove their typing in the independent R judgment.
  Choosing their proposition names requires only R-richness, not
  infinitely many names of every F type.
\<close>

lemma paper_R_named_chart_fresh_spec:
  assumes rich: "paper_R_rich G" and rt: "paper_R_type \<sigma>"
  shows "G (named_chart_fresh G ns \<sigma>) = \<sigma> \<and> named_chart_fresh G ns \<sigma> \<notin> set ns"
proof -
  obtain n where nt: "G n = \<sigma>" and fresh: "n \<notin> set ns"
    by (rule paper_R_rich_fresh[OF rich rt finite_set])
  have witness: "\<exists>n. G n = \<sigma> \<and> n \<notin> set ns"
    by (rule exI[where x=n], rule conjI[OF nt fresh])
  show ?thesis unfolding named_chart_fresh_def by (rule someI_ex[OF witness])
qed

lemma paper_R_named_paper_p_type:
  assumes rich: "paper_R_rich G"
  shows "G (named_paper_p G) = Prop"
proof -
  have rt: "paper_R_type Prop" by simp
  show ?thesis unfolding named_paper_p_def
    by (rule conjunct1[OF paper_R_named_chart_fresh_spec[OF rich rt]])
qed

lemma paper_R_named_paper_q_type:
  assumes rich: "paper_R_rich G"
  shows "G (named_paper_q G) = Prop"
proof -
  have rt: "paper_R_type Prop" by simp
  show ?thesis unfolding named_paper_q_def
    by (rule conjunct1[OF paper_R_named_chart_fresh_spec[OF rich rt]])
qed

lemma paper_R_named_paper_names_distinct:
  assumes rich: "paper_R_rich G"
  shows "named_paper_p G \<noteq> named_paper_q G"
proof -
  have rt: "paper_R_type Prop" by simp
  have fresh: "named_chart_fresh G [named_paper_p G] Prop \<notin> set [named_paper_p G]"
    by (rule conjunct2[OF paper_R_named_chart_fresh_spec[OF rich rt]])
  show ?thesis using fresh by (auto simp: named_paper_q_def)
qed

lemma paper_R_prop_unary_type:
  assumes symbol: "paper_logical_type l = Arr Prop Prop" and arg: "paper_R_has_type G A Prop"
  shows "paper_R_has_type G (NApp (NLogical l) A) Prop"
proof -
  have rt: "paper_R_type (paper_logical_type l)" by (simp add: symbol)
  have head: "paper_R_has_type G (NLogical l) (Arr Prop Prop)"
    using paper_R_has_type.Logical[where G=G, OF rt] by (simp only: symbol)
  show ?thesis by (rule paper_R_has_type.App[OF head arg])
qed

lemma paper_R_prop_binary_type:
  assumes symbol: "paper_logical_type l = Arr Prop (Arr Prop Prop)"
    and first: "paper_R_has_type G A Prop" and second: "paper_R_has_type G B Prop"
  shows "paper_R_has_type G (NApp (NApp (NLogical l) A) B) Prop"
proof -
  have rt: "paper_R_type (paper_logical_type l)" by (simp add: symbol)
  have head: "paper_R_has_type G (NLogical l) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G, OF rt] by (simp only: symbol)
  show ?thesis by (rule paper_R_has_type.App[OF paper_R_has_type.App[OF head first] second])
qed

lemma paper_R_named_not_type:
  "paper_R_has_type G A Prop \<Longrightarrow> paper_R_has_type G (named_paper_not A) Prop"
  unfolding named_paper_not_def by (rule paper_R_prop_unary_type[OF paper_logical_type.simps(1)]; assumption)

lemma paper_R_named_and_type:
  "paper_R_has_type G A Prop \<Longrightarrow> paper_R_has_type G B Prop \<Longrightarrow>
    paper_R_has_type G (named_paper_and A B) Prop"
  unfolding named_paper_and_def by (rule paper_R_prop_binary_type[OF paper_logical_type.simps(2)]; assumption)

lemma paper_R_named_or_type:
  "paper_R_has_type G A Prop \<Longrightarrow> paper_R_has_type G B Prop \<Longrightarrow>
    paper_R_has_type G (named_paper_or A B) Prop"
  unfolding named_paper_or_def by (rule paper_R_prop_binary_type[OF paper_logical_type.simps(3)]; assumption)

lemma paper_R_double_prop_lambda_type:
  assumes pt: "G p = Prop" and qt: "G q = Prop" and body: "paper_R_has_type G C Prop"
  shows "paper_R_has_type G (NLam p (NLam q C)) (Arr Prop (Arr Prop Prop))"
proof -
  have pr: "paper_R_type (G p)" by (simp only: pt; simp)
  have qr: "paper_R_type (G q)" by (simp only: qt; simp)
  have inner: "paper_R_has_type G (NLam q C) (Arr (G q) Prop)"
    by (rule paper_R_has_type.Lam[OF body qr]; simp)
  have outer: "paper_R_has_type G (NLam p (NLam q C)) (Arr (G p) (Arr (G q) Prop))"
    by (rule paper_R_has_type.Lam[OF inner pr]; simp)
  show ?thesis using outer by (simp only: pt qt)
qed

lemma paper_R_named_prop_variables:
  assumes rich: "paper_R_rich G"
  shows "paper_R_has_type G (NVar (named_paper_p G)) Prop"
    and "paper_R_has_type G (NVar (named_paper_q G)) Prop"
proof -
  have pt: "G (named_paper_p G) = Prop" by (rule paper_R_named_paper_p_type[OF rich])
  have qt: "G (named_paper_q G) = Prop" by (rule paper_R_named_paper_q_type[OF rich])
  have pr: "paper_R_type (G (named_paper_p G))" by (simp only: pt; simp)
  have qr: "paper_R_type (G (named_paper_q G))" by (simp only: qt; simp)
  show "paper_R_has_type G (NVar (named_paper_p G)) Prop"
    using paper_R_has_type.Var[where G=G and n="named_paper_p G", OF pr] by (simp only: pt)
  show "paper_R_has_type G (NVar (named_paper_q G)) Prop"
    using paper_R_has_type.Var[where G=G and n="named_paper_q G", OF qr] by (simp only: qt)
qed

lemma paper_R_named_paper_imp_const_type:
  assumes rich: "paper_R_rich G"
  shows "paper_R_has_type G (named_paper_imp_const G) (Arr Prop (Arr Prop Prop))"
  unfolding named_paper_imp_const_def
  by (rule paper_R_double_prop_lambda_type[OF paper_R_named_paper_p_type[OF rich]
      paper_R_named_paper_q_type[OF rich]],
    rule paper_R_named_or_type[OF paper_R_named_not_type[OF paper_R_named_prop_variables(1)[OF rich]]
      paper_R_named_prop_variables(2)[OF rich]])

lemma paper_R_named_paper_iff_const_type:
  assumes rich: "paper_R_rich G"
  shows "paper_R_has_type G (named_paper_iff_const G) (Arr Prop (Arr Prop Prop))"
  unfolding named_paper_iff_const_def
  by (rule paper_R_double_prop_lambda_type[OF paper_R_named_paper_p_type[OF rich]
      paper_R_named_paper_q_type[OF rich]],
    rule paper_R_named_and_type[
      OF paper_R_named_or_type[OF paper_R_named_not_type[OF paper_R_named_prop_variables(1)[OF rich]]
        paper_R_named_prop_variables(2)[OF rich]]
      paper_R_named_or_type[OF paper_R_named_not_type[OF paper_R_named_prop_variables(2)[OF rich]]
        paper_R_named_prop_variables(1)[OF rich]]])

lemma paper_R_named_paper_imp_const_language:
  "paper_R_rich G \<Longrightarrow> paper_R_in_language \<Sigma> G (named_paper_imp_const G) (Arr Prop (Arr Prop Prop))"
  unfolding paper_R_in_language_def
  by (rule conjI; (rule paper_R_named_paper_imp_const_type | rule named_paper_operator_signatures(1)); assumption?)

lemma paper_R_named_paper_iff_const_language:
  "paper_R_rich G \<Longrightarrow> paper_R_in_language \<Sigma> G (named_paper_iff_const G) (Arr Prop (Arr Prop Prop))"
  unfolding paper_R_in_language_def
  by (rule conjI; (rule paper_R_named_paper_iff_const_type | rule named_paper_operator_signatures(2)); assumption?)

theorem paper_R_named_paper_imp_language:
  assumes rich: "paper_R_rich G" and first: "paper_R_in_language \<Sigma> G A Prop"
    and second: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_in_language \<Sigma> G (named_paper_imp G A B) Prop"
  unfolding named_paper_imp_def
  by (rule paper_R_language_App[OF paper_R_language_App[OF paper_R_named_paper_imp_const_language[OF rich] first] second])

theorem paper_R_named_paper_iff_language:
  assumes rich: "paper_R_rich G" and first: "paper_R_in_language \<Sigma> G A Prop"
    and second: "paper_R_in_language \<Sigma> G B Prop"
  shows "paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop"
  unfolding named_paper_iff_def
  by (rule paper_R_language_App[OF paper_R_language_App[OF paper_R_named_paper_iff_const_language[OF rich] first] second])

lemma paper_R_named_not_language:
  "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow> paper_R_in_language \<Sigma> G (named_paper_not A) Prop"
  unfolding paper_R_in_language_def
  by (auto simp only: named_paper_primitive_signatures intro: paper_R_named_not_type)

lemma paper_R_named_or_language:
  "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow> paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_or A B) Prop"
  unfolding paper_R_in_language_def
  by (auto simp only: named_paper_primitive_signatures intro: paper_R_named_or_type)

lemma paper_R_named_and_language:
  "paper_R_in_language \<Sigma> G A Prop \<Longrightarrow> paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_and A B) Prop"
  unfolding paper_R_in_language_def
  by (auto simp only: named_paper_primitive_signatures intro: paper_R_named_and_type)

end
