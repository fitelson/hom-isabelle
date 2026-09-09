theory Bacon_Source_Relational_H_Theory_Sentence_Fragment
  imports Bacon_Source_Relational_H_Theory_Universal_Closure Bacon_Source_Relational_Closed_Theory
begin

section \<open>The closed fragment of a supplied H-theory\<close>

definition paper_R_sentence_fragment ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term set" where
  "paper_R_sentence_fragment \<Sigma> G T = {P\<in>T. paper_R_sentence \<Sigma> G P}"

lemma paper_R_sentence_fragment_subset:
  "paper_R_sentence_fragment \<Sigma> G T \<subseteq> T"
  by (auto simp: paper_R_sentence_fragment_def)

lemma paper_R_sentence_fragment_closed:
  "paper_R_closed_theory \<Sigma> G (paper_R_sentence_fragment \<Sigma> G T)"
  by (auto simp: paper_R_closed_theory_def paper_R_sentence_fragment_def)

lemma paper_R_sentence_fragment_consistent:
  assumes consistent: "paper_R_named_consistent \<Sigma> G T"
  shows "paper_R_named_consistent \<Sigma> G (paper_R_sentence_fragment \<Sigma> G T)"
  by (rule paper_R_named_consistent_mono[OF consistent paper_R_sentence_fragment_subset])

text \<open>
  The fragment is a set of closed R sentences and inherits local
  H consistency by inclusion. If T is an H-theory, every member P
  has a closed universal closure in this fragment. Thus the sentence-set
  model-existence theorem may be applied to the fragment; recovering
  all of T uses the separate native universal-instantiation implication.
  This is not a maximal or negation-complete open theory.
  Source: Theorem 3.2, pp.44–45, and the theory argument in n.73.
\<close>

theorem paper_R_H_theory_fragment_universal:
  assumes rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T" and member: "P \<in> T"
  obtains ns where "distinct ns" "set ns = named_fv P" "list_all paper_R_type (map G ns)"
    "paper_R_all_vec G ns P \<in> paper_R_sentence_fragment \<Sigma> G T"
proof -
  obtain ns where distinct: "distinct ns" and cover: "set ns = named_fv P"
    and binders: "list_all paper_R_type (map G ns)" and included: "paper_R_all_vec G ns P \<in> T"
    and language: "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    and closed: "named_fv (paper_R_all_vec G ns P) = {}"
    by (rule paper_R_H_theory_closed_universal_instance[OF rich theory_h member])
  have sentence: "paper_R_sentence \<Sigma> G (paper_R_all_vec G ns P)" by (rule paper_R_sentenceI[OF language closed])
  have fragment: "paper_R_all_vec G ns P \<in> paper_R_sentence_fragment \<Sigma> G T"
    using included sentence by (simp add: paper_R_sentence_fragment_def)
  show thesis by (rule that[OF distinct cover binders fragment])
qed

end
