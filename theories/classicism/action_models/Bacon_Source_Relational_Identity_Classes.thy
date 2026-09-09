theory Bacon_Source_Relational_Identity_Classes
  imports Bacon_Source_Relational_Identity_Class_Relation
begin

section \<open>Classes of closed terms under locally derivable identity\<close>

definition paper_R_identity_class ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> otype \<Rightarrow>
    'c paper_named_term \<Rightarrow> 'c paper_named_term set" where
  "paper_R_identity_class \<Sigma> G S \<sigma> A =
    {B \<in> paper_R_closed_terms \<Sigma> G \<sigma>. paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)}"

definition paper_R_identity_domain ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> otype \<Rightarrow>
    'c paper_named_term set set" where
  "paper_R_identity_domain \<Sigma> G S \<sigma> =
    image (paper_R_identity_class \<Sigma> G S \<sigma>) (paper_R_closed_terms \<Sigma> G \<sigma>)"

lemma paper_R_identity_classI:
  assumes member: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  shows "B \<in> paper_R_identity_class \<Sigma> G S \<sigma> A"
  using assms unfolding paper_R_identity_class_def by blast

lemma paper_R_identity_class_member_closed_terms:
  "B \<in> paper_R_identity_class \<Sigma> G S \<sigma> A \<Longrightarrow> B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  unfolding paper_R_identity_class_def by blast

lemma paper_R_identity_class_member_derivation:
  "B \<in> paper_R_identity_class \<Sigma> G S \<sigma> A \<Longrightarrow>
    paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  unfolding paper_R_identity_class_def by blast

lemma paper_R_identity_class_self:
  assumes member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "A \<in> paper_R_identity_class \<Sigma> G S \<sigma> A"
  by (rule paper_R_identity_classI[OF member
    paper_R_named_identity_refl[OF paper_R_closed_terms_language[OF member]]])

lemma paper_R_identity_class_nonempty:
  assumes member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A \<noteq> {}"
  using paper_R_identity_class_self[OF member] by blast

lemma paper_R_identity_class_as_relation_image:
  assumes member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A = Image (paper_R_identity_relation \<Sigma> G S \<sigma>) {A}"
  using member by (auto simp: paper_R_identity_class_def paper_R_identity_relation_def)

theorem paper_R_identity_class_eq_iff:
  assumes rich: "paper_R_rich G" and first: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and second: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A = paper_R_identity_class \<Sigma> G S \<sigma> B \<longleftrightarrow>
    paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
proof -
  have eq: "Image (paper_R_identity_relation \<Sigma> G S \<sigma>) {A} =
      Image (paper_R_identity_relation \<Sigma> G S \<sigma>) {B} \<longleftrightarrow>
      (A,B) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
    by (rule eq_equiv_class_iff[OF paper_R_identity_relation_equiv[OF rich] first second])
  show ?thesis by (simp only: paper_R_identity_class_as_relation_image[OF first]
    paper_R_identity_class_as_relation_image[OF second] eq paper_R_identity_relation_member first second; simp)
qed

section \<open>Different types have disjoint classes without adding tags\<close>

text \<open>
  A member of a σ-class is itself a closed R term of type σ.
  If the same term belonged to a τ-class, R typing uniqueness would
  give σ=τ. Hence classes at distinct types are disjoint. Represented
  classes are nonempty, so they cannot be equal across distinct types.
  No additional type tags or semantic separation principle is needed.
\<close>

theorem paper_R_identity_classes_disjoint:
  assumes different: "\<sigma> \<noteq> \<tau>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A \<inter> paper_R_identity_class \<Sigma> G S \<tau> B = {}"
proof (rule equals0I)
  fix C
  assume member: "C \<in> paper_R_identity_class \<Sigma> G S \<sigma> A \<inter> paper_R_identity_class \<Sigma> G S \<tau> B"
  have first: "C \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and second: "C \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    using member paper_R_identity_class_member_closed_terms by blast+
  have same: "\<sigma> = \<tau>" by (rule paper_R_closed_terms_type_unique[OF first second])
  show False using different same by contradiction
qed

lemma paper_R_identity_class_equal_types:
  assumes first: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and equality: "paper_R_identity_class \<Sigma> G S \<sigma> A = paper_R_identity_class \<Sigma> G S \<tau> B"
  shows "\<sigma> = \<tau>"
proof -
  have self: "A \<in> paper_R_identity_class \<Sigma> G S \<sigma> A" by (rule paper_R_identity_class_self[OF first])
  have other: "A \<in> paper_R_identity_class \<Sigma> G S \<tau> B" using self by (simp only: equality)
  show ?thesis by (rule paper_R_closed_terms_type_unique[
    OF first paper_R_identity_class_member_closed_terms[OF other]])
qed

section \<open>The image family contains only nonempty represented classes\<close>

text \<open>
  This image family is quotient syntax, not yet a model. Every value
  already in a fiber has a closed representative, and is nonempty.
  The fiber itself may still be empty: no witness-completion or
  all-type domain-inhabitation result is asserted here.
  Source: Theorem 3.2, footnote 64, p.45.
\<close>

lemma paper_R_identity_domainI:
  assumes member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_identity_class \<Sigma> G S \<sigma> A \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  unfolding paper_R_identity_domain_def by (rule imageI[OF member])

lemma paper_R_identity_domainE:
  assumes member: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  obtains A where "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" "X = paper_R_identity_class \<Sigma> G S \<sigma> A"
  using member that unfolding paper_R_identity_domain_def by blast

lemma paper_R_identity_value_nonempty:
  assumes member: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
  shows "X \<noteq> {}"
proof -
  obtain A where am: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" and shape: "X = paper_R_identity_class \<Sigma> G S \<sigma> A"
    by (rule paper_R_identity_domainE[OF member])
  show ?thesis by (simp only: shape; rule paper_R_identity_class_nonempty[OF am])
qed

lemma paper_R_identity_domain_member_closed_terms:
  assumes domain: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>" and member: "A \<in> X"
  shows "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
proof -
  obtain B where bm: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>" and shape: "X = paper_R_identity_class \<Sigma> G S \<sigma> B"
    by (rule paper_R_identity_domainE[OF domain])
  have class_member: "A \<in> paper_R_identity_class \<Sigma> G S \<sigma> B" using member by (simp only: shape)
  show ?thesis by (rule paper_R_identity_class_member_closed_terms[OF class_member])
qed

theorem paper_R_identity_domains_disjoint:
  assumes different: "\<sigma> \<noteq> \<tau>"
  shows "paper_R_identity_domain \<Sigma> G S \<sigma> \<inter> paper_R_identity_domain \<Sigma> G S \<tau> = {}"
proof (rule equals0I)
  fix X
  assume member: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma> \<inter> paper_R_identity_domain \<Sigma> G S \<tau>"
  have first: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
    and second: "X \<in> paper_R_identity_domain \<Sigma> G S \<tau>" using member by blast+
  obtain A where am: "A \<in> X" using paper_R_identity_value_nonempty[OF first] by blast
  have same: "\<sigma> = \<tau>" by (rule paper_R_closed_terms_type_unique[
    OF paper_R_identity_domain_member_closed_terms[OF first am] paper_R_identity_domain_member_closed_terms[OF second am]])
  show False using different same by contradiction
qed

lemma paper_R_identity_domain_nonR:
  assumes outside: "\<not> paper_R_type \<sigma>"
  shows "paper_R_identity_domain \<Sigma> G S \<sigma> = {}"
  by (simp only: paper_R_identity_domain_def paper_R_closed_terms_nonR[OF outside] image_empty)

end
