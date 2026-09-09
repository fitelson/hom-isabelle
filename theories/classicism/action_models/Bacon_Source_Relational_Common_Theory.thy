theory Bacon_Source_Relational_Common_Theory
  imports Bacon_Source_Relational_Quasi_Fregean_Denotation
    Bacon_Source_Relational_Application_Graph
begin

section \<open>The common theory of a collection of R models\<close>

text \<open>
  T𝒞 contains exactly the R formulas true at every object M and
  every typed partial assignment g adequate for that formula.
  Source: Bacon–Dorr Theorem 3.12, pp.51–52.

  This definition is semantic and includes its formula-language guard.
  Model validity and the selected arrows are separate certificates.
  Empty object collections are allowed; their common theory contains
  every R formula. No consistency or syntactic closure is stipulated.
\<close>

definition paper_R_common_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data set \<Rightarrow>
    'c paper_named_term set" where
  "paper_R_common_theory \<Sigma> G Obj = {A. paper_R_in_language \<Sigma> G A Prop \<and>
    (\<forall>M\<in>Obj. \<forall>g. named_env_typed (paper_bbk_domain M) G g \<longrightarrow>
      named_adequate g A \<longrightarrow> paper_bbk_valuation M (paper_bbk_denote M g A))}"

lemma paper_R_common_theory_language:
  "A \<in> paper_R_common_theory \<Sigma> G Obj \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  unfolding paper_R_common_theory_def by blast

lemma paper_R_common_theory_truth:
  assumes common: "A \<in> paper_R_common_theory \<Sigma> G Obj"
    and object: "M \<in> Obj"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation M (paper_bbk_denote M g A)"
  using assms unfolding paper_R_common_theory_def by blast

lemma paper_R_common_theoryI:
  assumes language: "paper_R_in_language \<Sigma> G A Prop"
    and truth: "\<And>M g. M \<in> Obj \<Longrightarrow>
      named_env_typed (paper_bbk_domain M) G g \<Longrightarrow>
      named_adequate g A \<Longrightarrow> paper_bbk_valuation M (paper_bbk_denote M g A)"
  shows "A \<in> paper_R_common_theory \<Sigma> G Obj"
  using assms unfolding paper_R_common_theory_def by blast

section \<open>Identity formulas express actual denotation equality\<close>

lemma paper_R_identity_language:
  assumes al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "paper_R_in_language \<Sigma> G (NApp (NApp (NLogical (SEq \<sigma>)) A) B) Prop"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF al])
  have eq_type: "paper_R_type (paper_logical_type (SEq \<sigma>))" using rt by simp
  have eq_typed: "paper_R_has_type G (NLogical (SEq \<sigma>)) (paper_logical_type (SEq \<sigma>))"
    by (rule paper_R_has_type.Logical[where l="SEq \<sigma>", OF eq_type])
  have eq_language: "paper_R_in_language \<Sigma> G (NLogical (SEq \<sigma>)) (Arr \<sigma> (Arr \<sigma> Prop))"
    using eq_typed by (simp add: paper_R_in_language_def)
  show ?thesis by (rule paper_R_language_App[OF paper_R_language_App[OF eq_language al] bl])
qed

lemma paper_R_identity_adequate_iff:
  "named_adequate g (NApp (NApp (NLogical (SEq \<sigma>)) A) B) \<longleftrightarrow>
    named_adequate g A \<and> named_adequate g B"
  by (auto simp: named_adequate_def)

theorem paper_R_common_identity_iff:
  assumes models: "\<And>M. M \<in> Obj \<Longrightarrow> paper_R_bbk_data_valid \<Sigma> G M"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
  shows "(NApp (NApp (NLogical (SEq \<sigma>)) A) B) \<in> paper_R_common_theory \<Sigma> G Obj \<longleftrightarrow>
    (\<forall>M\<in>Obj. \<forall>g. named_env_typed (paper_bbk_domain M) G g \<longrightarrow>
      named_adequate g A \<longrightarrow> named_adequate g B \<longrightarrow>
      paper_bbk_denote M g A = paper_bbk_denote M g B)"
proof -
  have identity_truth: "paper_bbk_valuation M
      (paper_bbk_denote M g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
      (paper_bbk_denote M g A = paper_bbk_denote M g B)"
    if object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
      and aa: "named_adequate g A" and ba: "named_adequate g B" for M g
  proof -
    interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
      "paper_bbk_denote M" "paper_bbk_valuation M"
      by (rule paper_R_bbk_data_model[OF models[OF object]])
    show ?thesis by (rule Model.valuation_identity[OF al bl typed aa ba])
  qed
  show ?thesis
    unfolding paper_R_common_theory_def
    using paper_R_identity_language[OF al bl]
    by (auto simp: paper_R_identity_adequate_iff identity_truth)
qed

end
