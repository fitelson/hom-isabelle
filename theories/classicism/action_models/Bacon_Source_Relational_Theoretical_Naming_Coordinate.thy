theory Bacon_Source_Relational_Theoretical_Naming_Coordinate
  imports Bacon_Source_Relational_H_Theory_Substitution
    Bacon_Source_Relational_Naming_Coordinate_Syntax
begin

section \<open>A one-coordinate change preserves theorem membership\<close>

text \<open>
  Two fresh typed charts differing at one typed new-name key give
  replacements with the same membership in an H-theory T. The
  literal coordinate equation is capture-free variable substitution,
  whose closure in T was derived from Gen, UI, β and MP.

  Source role: the parameter-language extension implicit in p.51
  n.73. This is a syntactic membership statement, not the separately
  proved semantic chart-independence theorem. No model is supplied.
\<close>

lemma paper_R_theoretical_naming_coordinate:
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and first: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
    and key: "k \<in> paper_R_naming_support A"
    and agree: "\<And>j. j \<in> paper_R_naming_support A \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
    and member: "paper_R_naming_replace x A \<in> T"
  shows "paper_R_naming_replace y A \<in> T"
proof -
  have xt: "G (x k) = fst k" by (rule paper_R_naming_chart_type[OF first key])
  have yt: "G (y k) = fst k" by (rule paper_R_naming_chart_type[OF second key])
  have xf: "x k \<notin> named_vars A" by (rule paper_R_naming_chart_fresh[OF first key])
  have yf: "y k \<notin> named_vars A" by (rule paper_R_naming_chart_fresh[OF second key])
  have original_type: "paper_R_has_type G A Prop"
    using language unfolding paper_R_in_language_def by blast
  have rt: "paper_R_type (fst k)"
    using paper_R_naming_support_R_types[OF original_type] key by blast
  have payload_at_key: "paper_R_in_language \<Sigma> G (NVar (y k)) (fst k)"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n="y k", OF yt rt])
  have payload: "paper_R_in_language \<Sigma> G (NVar (y k)) (G (x k))"
    by (simp only: xt; rule payload_at_key)
  have free_for: "named_free_for (NVar (y k)) (x k) (paper_R_naming_replace x A)"
    by (rule paper_R_naming_replace_variable_free_for[OF yf])
  have replacement: "paper_R_naming_replace y A =
      named_subst (x k) (NVar (y k)) (paper_R_naming_replace x A)"
    by (rule paper_R_naming_replace_coordinate[OF subset_refl
      paper_R_naming_chart_injective[OF first] key xf agree])
  show ?thesis by (simp only: replacement;
    rule paper_R_H_theory_substitution[OF rich theory_h member payload free_for])
qed

theorem paper_R_theoretical_naming_coordinate_iff:
  assumes rich: "paper_R_rich G"
    and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A Prop"
    and first: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) x"
    and second: "paper_R_naming_chart G (paper_R_naming_support A) (named_vars A) y"
    and key: "k \<in> paper_R_naming_support A"
    and agree: "\<And>j. j \<in> paper_R_naming_support A \<Longrightarrow> j \<noteq> k \<Longrightarrow> y j = x j"
  shows "(paper_R_naming_replace x A \<in> T) \<longleftrightarrow> (paper_R_naming_replace y A \<in> T)"
proof
  assume member: "paper_R_naming_replace x A \<in> T"
  show "paper_R_naming_replace y A \<in> T"
    by (rule paper_R_theoretical_naming_coordinate[
      OF rich theory_h language first second key agree member])
next
  assume member: "paper_R_naming_replace y A \<in> T"
  have reverse_agree: "x j = y j" if "j \<in> paper_R_naming_support A" "j \<noteq> k" for j
    by (rule sym[OF agree[OF that]])
  show "paper_R_naming_replace x A \<in> T"
    by (rule paper_R_theoretical_naming_coordinate[
      OF rich theory_h language second first key reverse_agree member])
qed

end
