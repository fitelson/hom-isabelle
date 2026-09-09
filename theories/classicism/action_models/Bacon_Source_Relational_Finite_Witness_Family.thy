theory Bacon_Source_Relational_Finite_Witness_Family
  imports Bacon_Source_Relational_Witness_Family_Syntax Bacon_Source_Relational_Witness_Consistency
begin

section \<open>Every finite subfamily preserves consistency sequentially\<close>

text \<open>
  Add one Wᵢ=(∃σᵢFᵢ→Fᵢcᵢ) at a time. At each step,
  the old predicates remain typed by signature inclusion, all accumulated
  premises are closed, and cᵢ is fresh at σᵢ. The latter uses
  injectivity of the TYPED names (σᵢ,cᵢ), not injectivity of c alone.
  The same raw name may therefore be used at distinct types.

  Source: the finite-family Henkin extension underlying Theorem 3.2,
  footnote 64, p.45. S may be infinite. The result assumes supplied
  names with the stated freshness properties; it neither constructs
  them nor imposes an enumeration or countability condition.
\<close>

theorem paper_R_named_consistent_finite_witness_family:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Omega> G S"
    and consistent: "paper_R_named_consistent \<Omega> G S"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow> paper_R_in_language \<Omega> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Omega> (\<tau> i)"
    and distinct: "inj_on (\<lambda>i. (\<tau> i,c i)) I"
    and finite: "finite J" and subset: "J \<subseteq> I"
  shows "paper_R_named_consistent (paper_R_witness_family_signature \<Omega> \<tau> c J) G
    (S \<union> paper_R_witness_family_axioms G \<tau> F c J)"
  using finite subset
proof (induction J rule: finite_induct)
  case empty
  show ?case by (simp only: paper_R_witness_family_signature_empty paper_R_witness_family_axioms_empty Un_empty_right;
    rule consistent)
next
  case (insert i J)
  have index: "i \<in> I" and indices: "J \<subseteq> I" using insert.prems by blast+
  let ?Sig = "paper_R_witness_family_signature \<Omega> \<tau> c J"
  let ?S = "S \<union> paper_R_witness_family_axioms G \<tau> F c J"
  have old_consistent: "paper_R_named_consistent ?Sig G ?S" by (rule insert.IH[OF indices])
  have old_predicates: "paper_R_in_language \<Omega> G (F j) (Arr (\<tau> j) Prop)" if "j \<in> J" for j
    by (rule predicates; use indices that in blast)
  have old_closed: "named_fv (F j) = {}" if "j \<in> J" for j
    by (rule closed; use indices that in blast)
  have old_theory: "paper_R_closed_theory ?Sig G ?S"
    by (rule paper_R_witness_family_closed_theory[OF rich source old_predicates old_closed])
  have predicate: "paper_R_in_language ?Sig G (F i) (Arr (\<tau> i) Prop)"
    by (rule paper_R_language_signature_mono[OF predicates[OF index]];
      rule paper_R_witness_family_signature_inclusion)
  have different: "(\<tau> j,c j) \<noteq> (\<tau> i,c i)" if member: "j \<in> J" for j
  proof
    assume equality: "(\<tau> j,c j) = (\<tau> i,c i)"
    have ji: "j \<in> I" using member indices by blast
    have same: "j = i" by (rule inj_onD[OF distinct equality ji index])
    show False using member insert.hyps(2) same by blast
  qed
  have next_fresh: "c i \<notin> ?Sig (\<tau> i)"
    by (rule paper_R_witness_family_fresh[where \<Omega>=\<Omega> and \<tau>=\<tau> and c=c and i=i and J=J,
      OF fresh[OF index] different])
  have enlarged: "paper_R_named_consistent (paper_R_add_constant ?Sig (\<tau> i) (c i)) G
    (insert (paper_R_witness_axiom G (\<tau> i) (F i) (c i)) ?S)"
    by (rule paper_R_named_consistent_fresh_witness[
      OF rich old_theory old_consistent predicate closed[OF index] next_fresh])
  show ?case by (simp only: paper_R_witness_family_signature_insert paper_R_witness_family_axioms_insert Un_insert_right;
    rule enlarged)
qed

end
