theory Bacon_Source_Relational_Witness_Family_Consistency
  imports Bacon_Source_Relational_Finite_Witness_Family
begin

section \<open>Finite premise sets use a finite part of the witness family\<close>

lemma paper_R_witness_family_finite_cover:
  assumes finite: "finite U" and subset: "U \<subseteq> S \<union> paper_R_witness_family_axioms G \<tau> F c I"
  obtains J where "finite J" "J \<subseteq> I" "U \<subseteq> S \<union> paper_R_witness_family_axioms G \<tau> F c J"
proof -
  let ?W = "\<lambda>i. paper_R_witness_axiom G (\<tau> i) (F i) (c i)"
  have finite_difference: "finite (U - S)" using finite by simp
  have image_subset: "U - S \<subseteq> image ?W I"
    using subset unfolding paper_R_witness_family_axioms_def by blast
  obtain J where indices: "J \<subseteq> I" and finite_J: "finite J" and image: "U - S = image ?W J"
    using finite_subset_image[where B="U - S" and f="?W" and A=I,
      OF finite_difference image_subset] by blast
  have cover: "U \<subseteq> S \<union> paper_R_witness_family_axioms G \<tau> F c J"
    using image unfolding paper_R_witness_family_axioms_def by blast
  show thesis by (rule that[OF finite_J indices cover])
qed

section \<open>An arbitrary supplied witness family preserves consistency\<close>

text \<open>
  Every finite subset of S∪W[I] is covered by S∪W[J] for some
  finite J⊆I. The finite-family theorem gives consistency at Ω[J].
  The proved local signature-transport theorem moves this consistency
  to Ω[I], before restricting it to the actual finite premises.
  Finite character then establishes consistency of the whole family.

  Source: Theorem 3.2, footnote 64, p.45. There is no enumeration
  of I, countability assumption or claim that an arbitrary original
  name carrier has fresh names. Predicates remain closed in the fixed
  old signature. This is not yet a witness-complete maximal theory
  or a semantic model.
\<close>

theorem paper_R_named_consistent_witness_family:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Omega> G S"
    and consistent: "paper_R_named_consistent \<Omega> G S"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow> paper_R_in_language \<Omega> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Omega> (\<tau> i)"
    and distinct: "inj_on (\<lambda>i. (\<tau> i,c i)) I"
  shows "paper_R_named_consistent (paper_R_witness_family_signature \<Omega> \<tau> c I) G
    (S \<union> paper_R_witness_family_axioms G \<tau> F c I)"
proof (rule iffD2[OF paper_R_named_consistent_finite_character], intro allI impI)
  fix U
  assume finite: "finite U" and subset: "U \<subseteq> S \<union> paper_R_witness_family_axioms G \<tau> F c I"
  obtain J where finite_J: "finite J" and indices: "J \<subseteq> I"
    and cover: "U \<subseteq> S \<union> paper_R_witness_family_axioms G \<tau> F c J"
    by (rule paper_R_witness_family_finite_cover[OF finite subset])
  let ?Sig = "paper_R_witness_family_signature \<Omega> \<tau> c J"
  let ?Whole = "paper_R_witness_family_signature \<Omega> \<tau> c I"
  let ?T = "S \<union> paper_R_witness_family_axioms G \<tau> F c J"
  have finite_consistent: "paper_R_named_consistent ?Sig G ?T"
    by (rule paper_R_named_consistent_finite_witness_family[
      OF rich source consistent predicates closed fresh distinct finite_J indices])
  have local_predicates: "paper_R_in_language \<Omega> G (F i) (Arr (\<tau> i) Prop)" if "i \<in> J" for i
    by (rule predicates; use indices that in blast)
  have local_closed: "named_fv (F i) = {}" if "i \<in> J" for i
    by (rule closed; use indices that in blast)
  have closed_family: "paper_R_closed_theory ?Sig G ?T"
    by (rule paper_R_witness_family_closed_theory[OF rich source local_predicates local_closed])
  have source_names: "named_in_signature ?Sig A" if member: "A \<in> ?T" for A
  proof -
    have sentence: "paper_R_sentence ?Sig G A" by (rule paper_R_closed_theory_member[OF closed_family member])
    have language: "paper_R_in_language ?Sig G A Prop" by (rule paper_R_sentence_language[OF sentence])
    show ?thesis using language unfolding paper_R_in_language_def by (rule conjunct2)
  qed
  have enlarged: "paper_R_named_consistent ?Whole G ?T"
    by (rule paper_R_named_consistent_signature_transport[
      where \<Omega>="?Sig" and \<Sigma>="?Whole" and G=G and S="?T",
      OF rich finite_consistent source_names])
  show "paper_R_named_consistent ?Whole G U"
    by (rule paper_R_named_consistent_mono[where \<Sigma>="?Whole" and G=G and S=U and T="?T",
      OF enlarged cover])
qed

end
