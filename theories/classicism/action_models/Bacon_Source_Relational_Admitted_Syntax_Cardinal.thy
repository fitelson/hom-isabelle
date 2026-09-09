theory Bacon_Source_Relational_Admitted_Syntax_Cardinal
  imports Bacon_Source_Relational_Finite_Syntax_Code
    "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>The cardinal of the admitted finite syntax\<close>

text \<open>
  For infinite U, at most |U| declared constant names give at most |U|
  admitted raw terms. The bound includes every R-typed term but does not
  require typing, richness, consistency, Henkin witnesses, or a model.
  The name carrier 'c and comparison carrier 'u are arbitrary HOL types.
  This is the finite-syntax ingredient, not the entire cardinal-model
  argument of p.51 n.73.
\<close>

lemma paper_R_admitted_syntax_lists_bound:
  "card_of {A :: 'c paper_named_term. named_in_signature \<Sigma> A} \<le>o
    card_of (lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)))"
proof (rule card_of_ordLeqI[where f=paper_R_finite_syntax_code])
  show "inj_on paper_R_finite_syntax_code {A :: 'c paper_named_term. named_in_signature \<Sigma> A}"
    using paper_R_finite_syntax_code_injective by (rule inj_on_subset) simp
next
  fix A :: "'c paper_named_term"
  assume "A \<in> {A. named_in_signature \<Sigma> A}"
  then show "paper_R_finite_syntax_code A \<in>
    lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))"
    by (simp add: paper_R_finite_syntax_code_lists)
qed

theorem paper_R_admitted_syntax_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
  shows "card_of {A :: 'c paper_named_term. named_in_signature \<Sigma> A} \<le>o card_of U"
proof -
  have naturals: "card_of (UNIV :: nat set) \<le>o card_of U"
    using infinite infinite_iff_card_of_nat by blast
  have alphabet: "card_of ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set)) \<le>o card_of U"
    by (rule card_of_Plus_ordLeq_infinite[OF infinite names naturals])
  have lists_bound: "card_of (lists ((\<Union>\<sigma>. \<Sigma> \<sigma>) <+> (UNIV :: nat set))) \<le>o
    card_of (lists U)"
    by (rule card_of_lists_mono[OF alphabet])
  have to_lists: "card_of {A :: 'c paper_named_term. named_in_signature \<Sigma> A} \<le>o card_of (lists U)"
    by (rule ordLeq_transitive[OF paper_R_admitted_syntax_lists_bound lists_bound])
  show ?thesis
    by (rule ordLeq_ordIso_trans[OF to_lists card_of_lists_infinite[OF infinite]])
qed

corollary paper_R_admitted_syntax_embedding:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
  obtains e :: "'c paper_named_term \<Rightarrow> 'u"
    where "inj_on e {A. named_in_signature \<Sigma> A}"
      and "e ` {A. named_in_signature \<Sigma> A} \<subseteq> U"
  using paper_R_admitted_syntax_cardinal_bound[OF infinite names]
  unfolding card_of_ordLeq[symmetric] by blast

end
