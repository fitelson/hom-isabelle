theory Bacon_Source_Relational_Witness_Syntax
  imports Bacon_Source_Relational_Closed_Theory Bacon_Source_Relational_Retraction_Syntax
begin

section \<open>One typed constant and its conditional witness sentence\<close>

text \<open>
  Adjoin c:σ to Ω and put Wc=(∃σF→Fc). Source: Theorem 3.2,
  p.45 n.64. The signature is indexed by type: c may already be a
  name at another type. Freshness here is specifically c∉Ωσ.
  This leaf proves typing, closedness and the exact retraction equation;
  it does not prove consistency or that a fresh name exists in every
  original constant-name carrier. A later name expansion must supply it.
\<close>

definition paper_R_add_constant where
  "paper_R_add_constant \<Omega> \<sigma> c = \<Omega>(\<sigma> := insert c (\<Omega> \<sigma>))"

definition paper_R_witness_axiom where
  "paper_R_witness_axiom G \<sigma> F c =
    named_paper_imp G (named_paper_ex \<sigma> F) (NApp F (NConst c \<sigma>))"

lemma paper_R_add_constant_names:
  assumes names: "named_in_signature \<Omega> A"
  shows "named_in_signature (paper_R_add_constant \<Omega> \<sigma> c) A"
  using names by (induction A) (auto simp: paper_R_add_constant_def)

lemma paper_R_add_constant_language:
  assumes language: "paper_R_in_language \<Omega> G A \<rho>"
  shows "paper_R_in_language (paper_R_add_constant \<Omega> \<sigma> c) G A \<rho>"
proof -
  have typed: "paper_R_has_type G A \<rho>" and names: "named_in_signature \<Omega> A"
    using language unfolding paper_R_in_language_def by blast+
  have expanded: "named_in_signature (paper_R_add_constant \<Omega> \<sigma> c) A"
    by (rule paper_R_add_constant_names[where \<sigma>=\<sigma> and c=c, OF names])
  show ?thesis unfolding paper_R_in_language_def by (rule conjI[OF typed expanded])
qed

lemma paper_R_predicate_exists_language:
  assumes predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
  shows "paper_R_in_language \<Omega> G (named_paper_ex \<sigma> F) Prop"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have qr: "paper_R_type (paper_logical_type (SEx \<sigma>))" using rt by simp
  have qt: "paper_R_has_type G (NLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G and l="SEx \<sigma>", OF qr] by simp
  have ql: "paper_R_in_language \<Omega> G (NLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    unfolding paper_R_in_language_def by (rule conjI[OF qt]; simp)
  show ?thesis unfolding named_paper_ex_def by (rule paper_R_language_App[OF ql predicate])
qed

lemma paper_R_witness_language:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
  shows "paper_R_in_language (paper_R_add_constant \<Omega> \<sigma> c) G (paper_R_witness_axiom G \<sigma> F c) Prop"
proof -
  let ?S = "paper_R_add_constant \<Omega> \<sigma> c"
  have fl: "paper_R_in_language ?S G F (Arr \<sigma> Prop)" by (rule paper_R_add_constant_language[OF predicate])
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have ct: "paper_R_has_type G (NConst c \<sigma>) \<sigma>" by (rule paper_R_has_type.Const[OF rt])
  have cl: "paper_R_in_language ?S G (NConst c \<sigma>) \<sigma>"
    by (simp only: paper_R_in_language_def; use ct in \<open>simp add: paper_R_add_constant_def\<close>)
  show ?thesis unfolding paper_R_witness_axiom_def
    by (rule paper_R_named_paper_imp_language[OF rich paper_R_predicate_exists_language[OF fl]
      paper_R_language_App[OF fl cl]])
qed

lemma paper_R_witness_closed:
  assumes closed: "named_fv F = {}"
  shows "named_fv (paper_R_witness_axiom G \<sigma> F c) = {}"
  by (simp add: paper_R_witness_axiom_def named_paper_defined_fv named_paper_primitive_fv closed)

lemma paper_R_witness_sentence:
  assumes rich: "paper_R_rich G" and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "paper_R_sentence (paper_R_add_constant \<Omega> \<sigma> c) G (paper_R_witness_axiom G \<sigma> F c)"
  by (rule paper_R_sentenceI[OF paper_R_witness_language[OF rich predicate] paper_R_witness_closed[OF closed]])

lemma paper_R_witness_retract:
  assumes names: "named_in_signature \<Omega> F" and fresh: "c \<notin> \<Omega> \<sigma>"
  shows "named_retract \<Omega> v (paper_R_witness_axiom G \<sigma> F c) =
    named_paper_imp G (named_paper_ex \<sigma> F) (NApp F (NVar (v \<sigma>)))"
  by (simp only: paper_R_witness_axiom_def paper_R_retract_imp paper_R_retract_primitive
    named_retract.simps named_retract_fixed[OF names] fresh if_False)

end
