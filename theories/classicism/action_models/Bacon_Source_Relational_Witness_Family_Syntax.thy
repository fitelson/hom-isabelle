theory Bacon_Source_Relational_Witness_Family_Syntax
  imports Bacon_Source_Relational_Witness_Syntax
begin

section \<open>Partial signatures and axioms for a typed witness family\<close>

text \<open>
  Ω[J]ρ=Ωρ∪{cᵢ | i∈J, σᵢ=ρ}; W[J]={∃σᵢFᵢ→Fᵢcᵢ | i∈J}.
  The index and name types are arbitrary. These definitions neither
  enumerate the family nor assert that fresh names exist.
  Source role: organizing the Henkin witnesses in Theorem 3.2,
  footnote 64, p.45. Every predicate used later is already closed
  in the FIXED OLD signature Ω, not merely in the final enlargement.
\<close>

definition paper_R_witness_family_signature ::
  "'c ssignature \<Rightarrow> ('i \<Rightarrow> otype) \<Rightarrow> ('i \<Rightarrow> 'c) \<Rightarrow> 'i set \<Rightarrow> 'c ssignature" where
  "paper_R_witness_family_signature \<Omega> \<tau> c J \<rho> = \<Omega> \<rho> \<union> image c {i\<in>J. \<tau> i = \<rho>}"

definition paper_R_witness_family_axioms ::
  "sgcontext \<Rightarrow> ('i \<Rightarrow> otype) \<Rightarrow> ('i \<Rightarrow> 'c paper_named_term) \<Rightarrow>
    ('i \<Rightarrow> 'c) \<Rightarrow> 'i set \<Rightarrow> 'c paper_named_term set" where
  "paper_R_witness_family_axioms G \<tau> F c J = image (\<lambda>i. paper_R_witness_axiom G (\<tau> i) (F i) (c i)) J"

lemma paper_R_language_signature_mono:
  assumes language: "paper_R_in_language \<Omega> G A \<rho>" and inclusion: "\<And>\<sigma>. \<Omega> \<sigma> \<subseteq> \<Sigma> \<sigma>"
  shows "paper_R_in_language \<Sigma> G A \<rho>"
proof -
  have typed: "paper_R_has_type G A \<rho>" and names: "named_in_signature \<Omega> A"
    using language unfolding paper_R_in_language_def by blast+
  have expanded: "named_in_signature \<Sigma> A"
    using names by (induction A) (auto dest: subsetD[OF inclusion])
  show ?thesis unfolding paper_R_in_language_def by (rule conjI[OF typed expanded])
qed

lemma paper_R_sentence_signature_mono:
  assumes sentence: "paper_R_sentence \<Omega> G A" and inclusion: "\<And>\<sigma>. \<Omega> \<sigma> \<subseteq> \<Sigma> \<sigma>"
  shows "paper_R_sentence \<Sigma> G A"
  by (rule paper_R_sentenceI[OF paper_R_language_signature_mono[
    OF paper_R_sentence_language[OF sentence] inclusion] paper_R_sentence_closed[OF sentence]])

lemma paper_R_witness_family_signature_empty:
  "paper_R_witness_family_signature \<Omega> \<tau> c {} = \<Omega>"
  by (rule ext; simp add: paper_R_witness_family_signature_def)

lemma paper_R_witness_family_signature_insert:
  "paper_R_witness_family_signature \<Omega> \<tau> c (insert i J) =
    paper_R_add_constant (paper_R_witness_family_signature \<Omega> \<tau> c J) (\<tau> i) (c i)"
  by (rule ext; auto simp: paper_R_witness_family_signature_def paper_R_add_constant_def)

lemma paper_R_witness_family_signature_inclusion:
  "\<Omega> \<rho> \<subseteq> paper_R_witness_family_signature \<Omega> \<tau> c J \<rho>"
  by (auto simp: paper_R_witness_family_signature_def)

lemma paper_R_witness_family_signature_member:
  assumes index: "i \<in> J"
  shows "c i \<in> paper_R_witness_family_signature \<Omega> \<tau> c J (\<tau> i)"
  using index by (auto simp: paper_R_witness_family_signature_def)

lemma paper_R_witness_family_axioms_empty:
  "paper_R_witness_family_axioms G \<tau> F c {} = {}"
  by (simp add: paper_R_witness_family_axioms_def)

lemma paper_R_witness_family_axioms_insert:
  "paper_R_witness_family_axioms G \<tau> F c (insert i J) =
    insert (paper_R_witness_axiom G (\<tau> i) (F i) (c i)) (paper_R_witness_family_axioms G \<tau> F c J)"
  by (simp add: paper_R_witness_family_axioms_def)

lemma paper_R_witness_family_fresh:
  assumes old: "c i \<notin> \<Omega> (\<tau> i)"
    and different: "\<And>j. j \<in> J \<Longrightarrow> (\<tau> j,c j) \<noteq> (\<tau> i,c i)"
  shows "c i \<notin> paper_R_witness_family_signature \<Omega> \<tau> c J (\<tau> i)"
  using old different by (auto simp: paper_R_witness_family_signature_def; blast)

lemma paper_R_witness_family_axiom_sentence:
  assumes rich: "paper_R_rich G" and index: "i \<in> J"
    and predicate: "paper_R_in_language \<Omega> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "named_fv (F i) = {}"
  shows "paper_R_sentence (paper_R_witness_family_signature \<Omega> \<tau> c J) G
    (paper_R_witness_axiom G (\<tau> i) (F i) (c i))"
proof -
  have one: "paper_R_sentence (paper_R_add_constant \<Omega> (\<tau> i) (c i)) G
    (paper_R_witness_axiom G (\<tau> i) (F i) (c i))"
    by (rule paper_R_witness_sentence[OF rich predicate closed])
  have inclusion: "paper_R_add_constant \<Omega> (\<tau> i) (c i) \<rho> \<subseteq>
    paper_R_witness_family_signature \<Omega> \<tau> c J \<rho>" for \<rho>
    using index by (auto simp: paper_R_add_constant_def paper_R_witness_family_signature_def)
  show ?thesis by (rule paper_R_sentence_signature_mono[OF one inclusion])
qed

theorem paper_R_witness_family_closed_theory:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Omega> G S"
    and predicates: "\<And>i. i \<in> J \<Longrightarrow> paper_R_in_language \<Omega> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> J \<Longrightarrow> named_fv (F i) = {}"
  shows "paper_R_closed_theory (paper_R_witness_family_signature \<Omega> \<tau> c J) G
    (S \<union> paper_R_witness_family_axioms G \<tau> F c J)"
proof (unfold paper_R_closed_theory_def, intro ballI)
  fix A
  assume member: "A \<in> S \<union> paper_R_witness_family_axioms G \<tau> F c J"
  show "paper_R_sentence (paper_R_witness_family_signature \<Omega> \<tau> c J) G A"
  proof (cases "A \<in> S")
    case True
    have sentence: "paper_R_sentence \<Omega> G A" by (rule paper_R_closed_theory_member[OF source True])
    show ?thesis by (rule paper_R_sentence_signature_mono[OF sentence]; rule paper_R_witness_family_signature_inclusion)
  next
    case False
    obtain i where index: "i \<in> J" and shape: "A = paper_R_witness_axiom G (\<tau> i) (F i) (c i)"
      using member False unfolding paper_R_witness_family_axioms_def by blast
    show ?thesis by (simp only: shape; rule paper_R_witness_family_axiom_sentence[
      where \<Omega>=\<Omega> and G=G and F=F and \<tau>=\<tau> and c=c and i=i and J=J,
      OF rich index predicates[OF index] closed[OF index]])
  qed
qed

end
