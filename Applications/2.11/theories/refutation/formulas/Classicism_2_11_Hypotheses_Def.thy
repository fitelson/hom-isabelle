theory Classicism_2_11_Hypotheses_Def
  imports Classicism_2_11_Syntax
begin

section \<open>The hypotheses and conclusion of Proposition 2.11\<close>

text \<open>
  Proposition 2.11, p.30: □Atomicity, Boolean Completeness, and BF
  jointly imply Rigid Comprehension. The hypotheses are the schema
  instances themselves, unnecessitated except for □Atomicity:
  □Atomicity and Boolean Completeness at every relational type
  (including t), BF at every R type σ (including e), every binder of
  type σ, and every R formula P, open or closed.

  The conclusion refuted is the Rigid Comprehension instance for
  monadic properties of propositions, type t→t.
\<close>

definition c211_hypotheses :: "'c ssignature \<Rightarrow> 'c paper_named_term set" where
  "c211_hypotheses \<Sigma> =
    {c211_box_atomicity \<tau> |\<tau>. paper_R_relational \<tau>} \<union>
    {c211_BC \<tau> |\<tau>. paper_R_relational \<tau>} \<union>
    {c211_BF \<sigma> n P |\<sigma> n P. paper_R_type \<sigma> \<and> c211_G n = \<sigma> \<and>
      paper_R_in_language \<Sigma> c211_G P Prop}"

definition c211_conclusion :: "'c paper_named_term" where
  "c211_conclusion = c211_RC [Prop]"

lemma c211_hypotheses_cases:
  assumes "A \<in> c211_hypotheses \<Sigma>"
  obtains (box_atomicity) \<tau> where "paper_R_relational \<tau>" "A = c211_box_atomicity \<tau>"
  | (completeness) \<tau> where "paper_R_relational \<tau>" "A = c211_BC \<tau>"
  | (barcan) \<sigma> n P where "paper_R_type \<sigma>" "c211_G n = \<sigma>"
      "paper_R_in_language \<Sigma> c211_G P Prop" "A = c211_BF \<sigma> n P"
  using assms unfolding c211_hypotheses_def by blast

lemma c211_hypotheses_language:
  "A \<in> c211_hypotheses \<Sigma> \<Longrightarrow> paper_R_in_language \<Sigma> c211_G A Prop"
  by (erule c211_hypotheses_cases)
    (simp_all add: c211_box_atomicity_language c211_BC_language c211_BF_language)

lemma c211_conclusion_language: "paper_R_in_language \<Sigma> c211_G c211_conclusion Prop"
  unfolding c211_conclusion_def by (rule c211_RC_language) simp

lemma c211_conclusion_closed: "named_fv c211_conclusion = {}"
  unfolding c211_conclusion_def by (rule c211_RC_closed)

ML \<open>
  val _ = ["c211_hypotheses_cases", "c211_hypotheses_language",
      "c211_conclusion_language", "c211_conclusion_closed"]
    |> List.app (fn name =>
      let val th = Proof_Context.get_thm \<^context> name
      in if null (Thm_Deps.all_oracles [th]) andalso null (Thm.hyps_of th)
           andalso null (Thm.tpairs_of th) then () else error name end);
  val _ = writeln "C211-HYPOTHESES-DEF: 4 clean endpoints"
\<close>

end
