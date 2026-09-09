theory Bacon_Source_Relational_Identity_Class_Relation
  imports Bacon_Source_Relational_Identity_Derivations
begin

section \<open>The theorem-identity relation on closed R terms\<close>

text \<open>
  Cσ is the set of closed terms of type σ in ℒᴿ(Σ).
  For A,B∈Cσ, put A≈S,σB iff S⊢HᴿA=σB.
  Source: the canonical model blueprint in Theorem 3.2, footnote 64,
  p.45. The relation is DERIVABLE IDENTITY, not βη conversion.

  Ref, the derived symmetry theorem and the derived transitivity
  theorem make it an equivalence relation. No consistency, maximality,
  witness completeness or semantic equality law is needed for this
  algebraic fact. No closed term at a given type is assumed to exist.
\<close>

definition paper_R_closed_terms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> 'c paper_named_term set" where
  "paper_R_closed_terms \<Sigma> G \<sigma> =
    {A. paper_R_in_language \<Sigma> G A \<sigma> \<and> named_fv A = {}}"

definition paper_R_identity_relation ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> otype \<Rightarrow>
    ('c paper_named_term \<times> 'c paper_named_term) set" where
  "paper_R_identity_relation \<Sigma> G S \<sigma> =
    {(A,B). A \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<and> B \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<and>
      paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)}"

lemma paper_R_closed_termsI:
  assumes language: "paper_R_in_language \<Sigma> G A \<sigma>" and closed: "named_fv A = {}"
  shows "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  using assms unfolding paper_R_closed_terms_def by blast

lemma paper_R_closed_terms_language:
  "A \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<Longrightarrow> paper_R_in_language \<Sigma> G A \<sigma>"
  unfolding paper_R_closed_terms_def by blast

lemma paper_R_closed_terms_type:
  assumes member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  shows "paper_R_has_type G A \<sigma>"
  using paper_R_closed_terms_language[OF member] unfolding paper_R_in_language_def by (rule conjunct1)

lemma paper_R_closed_terms_closed:
  "A \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<Longrightarrow> named_fv A = {}"
  unfolding paper_R_closed_terms_def by blast

lemma paper_R_closed_terms_type_unique:
  assumes first: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    and second: "A \<in> paper_R_closed_terms \<Sigma> G \<tau>"
  shows "\<sigma> = \<tau>"
  by (rule paper_R_type_unique[OF paper_R_closed_terms_type[OF first] paper_R_closed_terms_type[OF second]])

lemma paper_R_closed_terms_nonR:
  assumes outside: "\<not> paper_R_type \<sigma>"
  shows "paper_R_closed_terms \<Sigma> G \<sigma> = {}"
proof (rule equals0I)
  fix A
  assume member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_result_type[OF paper_R_closed_terms_type[OF member]])
  show False using outside rt by contradiction
qed

lemma paper_R_identity_relation_member:
  "(A,B) \<in> paper_R_identity_relation \<Sigma> G S \<sigma> \<longleftrightarrow>
    A \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<and> B \<in> paper_R_closed_terms \<Sigma> G \<sigma> \<and>
      paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
  by (simp add: paper_R_identity_relation_def)

theorem paper_R_identity_relation_equiv:
  assumes rich: "paper_R_rich G"
  shows "equiv (paper_R_closed_terms \<Sigma> G \<sigma>) (paper_R_identity_relation \<Sigma> G S \<sigma>)"
proof (rule equivI)
  show "paper_R_identity_relation \<Sigma> G S \<sigma> \<subseteq>
    paper_R_closed_terms \<Sigma> G \<sigma> \<times> paper_R_closed_terms \<Sigma> G \<sigma>"
    by (auto simp: paper_R_identity_relation_def)
next
  show "refl_on (paper_R_closed_terms \<Sigma> G \<sigma>) (paper_R_identity_relation \<Sigma> G S \<sigma>)"
  proof (rule refl_onI)
    fix A
    assume member: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    have equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A A)"
      by (rule paper_R_named_identity_refl[OF paper_R_closed_terms_language[OF member]])
    show "(A,A) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
      using member equality by (simp only: paper_R_identity_relation_member)
  qed
next
  show "sym (paper_R_identity_relation \<Sigma> G S \<sigma>)"
  proof (rule symI)
    fix A B
    assume pair: "(A,B) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
    have am: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
      and ab: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
      using pair by (simp only: paper_R_identity_relation_member; blast)+
    have ba: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> B A)"
      by (rule paper_R_named_identity_sym[OF rich paper_R_closed_terms_language[OF am]
        paper_R_closed_terms_language[OF bm] ab])
    show "(B,A) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
      using am bm ba by (simp only: paper_R_identity_relation_member)
  qed
next
  show "trans (paper_R_identity_relation \<Sigma> G S \<sigma>)"
  proof (rule transI)
    fix A B C
    assume first: "(A,B) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
      and second: "(B,C) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
    have am: "A \<in> paper_R_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
      and cm: "C \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
      and ab: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A B)"
      and bc: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> B C)"
      using first second by (simp only: paper_R_identity_relation_member; blast)+
    have ac: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<sigma> A C)"
      by (rule paper_R_named_identity_trans[OF rich paper_R_closed_terms_language[OF am]
        paper_R_closed_terms_language[OF bm] paper_R_closed_terms_language[OF cm] ab bc])
    show "(A,C) \<in> paper_R_identity_relation \<Sigma> G S \<sigma>"
      using am cm ac by (simp only: paper_R_identity_relation_member)
  qed
qed

end
