theory Bacon_Source_Relational_Identity_Interpretation
  imports Bacon_Source_Relational_Environment_Substitution_Typing
    Bacon_Source_Relational_Identity_Application Bacon_Source_Relational_Term_Type
begin

section \<open>The candidate closed-term-class interpretation\<close>

text \<open>
  JΣ,G,S(g,A) is the identity class of A after simultaneous substitution
  of the chosen closed representatives of g's assigned values. The type
  index is the unique R type of A, supplied by paper_R_term_type.
  Source: the canonical interpretation in Theorem 3.2, p.45 n.64.

  Type selection on ill-typed syntax and representative choice outside
  actual class fibers have no asserted source meaning. The meaningful
  denotation theorem requires an R-language term and a typed adequate
  partial class assignment. These structural facts need no consistency
  or Henkin property. Arbitrary representative independence, conversion,
  valuation and the thirteen BBK fields are not assumed or concluded.
\<close>

definition paper_R_identity_denote ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    ('c paper_named_term set) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'c paper_named_term set" where
  "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_class \<Sigma> G S (paper_R_term_type G A)
    (paper_R_environment_subst (paper_R_representative_assignment g) A)"

lemma paper_R_identity_denote_eq:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
  shows "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_class \<Sigma> G S \<tau>
    (paper_R_environment_subst (paper_R_representative_assignment g) A)"
  by (simp only: paper_R_identity_denote_def paper_R_term_type_language[OF language])

theorem paper_R_identity_denote_type:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g" and adequate: "named_adequate g A"
  shows "paper_R_identity_denote \<Sigma> G S g A \<in> paper_R_identity_domain \<Sigma> G S \<tau>"
  by (simp only: paper_R_identity_denote_eq[OF language];
    rule paper_R_identity_domainI[OF paper_R_representative_substitution_closed_terms[OF language typed adequate]])

lemma paper_R_identity_denote_closed:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>" and closed: "named_fv A = {}"
  shows "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_class \<Sigma> G S \<tau> A"
  by (simp only: paper_R_identity_denote_eq[OF language] paper_R_environment_subst_closed_fixed[OF closed])

section \<open>Variables and the two kinds of constants\<close>

theorem paper_R_identity_denote_var:
  assumes rich: "paper_R_rich G" and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
    and assigned: "g n = Some X"
  shows "paper_R_identity_denote \<Sigma> G S g (NVar n) = X"
proof -
  have domain: "X \<in> paper_R_identity_domain \<Sigma> G S (G n)" by (rule named_env_value[OF typed assigned])
  have representative: "paper_R_identity_rep X \<in> paper_R_closed_terms \<Sigma> G (G n)"
    by (rule paper_R_identity_rep_closed_terms[OF domain])
  have rt: "paper_R_type (G n)" by (rule paper_R_result_type[OF paper_R_closed_terms_type[OF representative]])
  have variable: "paper_R_has_type G (NVar n) (G n)" by (rule paper_R_has_type.Var[where G=G and n=n, OF rt])
  have replacement: "paper_R_environment_subst (paper_R_representative_assignment g) (NVar n) = paper_R_identity_rep X"
    by (simp only: paper_R_environment_subst.simps paper_R_representative_assignment_apply assigned option.map option.case)
  show ?thesis by (simp only: paper_R_identity_denote_def paper_R_term_type_eq[OF variable] replacement;
    rule paper_R_identity_class_rep[OF rich domain])
qed

lemma paper_R_identity_denote_const:
  assumes rt: "paper_R_type \<sigma>" and declared: "c \<in> \<Sigma> \<sigma>"
  shows "paper_R_identity_denote \<Sigma> G S g (NConst c \<sigma>) = paper_R_identity_class \<Sigma> G S \<sigma> (NConst c \<sigma>)"
proof -
  have language: "paper_R_in_language \<Sigma> G (NConst c \<sigma>) \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF paper_R_has_type.Const[OF rt]];
      simp only: named_in_signature.simps; rule declared)
  have closed: "named_fv (NConst c \<sigma>) = {}" by simp
  show ?thesis by (rule paper_R_identity_denote_closed[OF language closed])
qed

lemma paper_R_identity_denote_logical:
  assumes rt: "paper_R_type (paper_logical_type l)"
  shows "paper_R_identity_denote \<Sigma> G S g (NLogical l) =
    paper_R_identity_class \<Sigma> G S (paper_logical_type l) (NLogical l)"
proof -
  have language: "paper_R_in_language \<Sigma> G (NLogical l) (paper_logical_type l)"
    unfolding paper_R_in_language_def by (rule conjI[OF paper_R_has_type.Logical[OF rt]]; simp)
  have closed: "named_fv (NLogical l :: 'c paper_named_term) = {}" by simp
  show ?thesis by (rule paper_R_identity_denote_closed[OF language closed])
qed

section \<open>Free-variable locality and application\<close>

lemma paper_R_identity_denote_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
  shows "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_denote \<Sigma> G S k A"
proof -
  have representatives: "paper_R_representative_assignment g n = paper_R_representative_assignment k n"
    if "n \<in> named_fv A" for n
    by (simp only: paper_R_representative_assignment_apply agree[OF that])
  have equal: "paper_R_environment_subst (paper_R_representative_assignment g) A =
      paper_R_environment_subst (paper_R_representative_assignment k) A"
    by (rule paper_R_environment_subst_locality[OF representatives])
  show ?thesis by (simp only: paper_R_identity_denote_def equal)
qed

theorem paper_R_identity_denote_App:
  assumes rich: "paper_R_rich G" and head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
    and adequate: "named_adequate g (NApp F A)"
  shows "paper_R_identity_denote \<Sigma> G S g (NApp F A) =
    paper_R_identity_application \<Sigma> G S \<sigma> \<tau>
      (paper_R_identity_denote \<Sigma> G S g F) (paper_R_identity_denote \<Sigma> G S g A)"
proof -
  let ?r = "paper_R_representative_assignment g"
  have fa: "named_adequate g F" and aa: "named_adequate g A" using adequate by (auto simp: named_adequate_def)
  have fc: "paper_R_environment_subst ?r F \<in> paper_R_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    by (rule paper_R_representative_substitution_closed_terms[OF head typed fa])
  have ac: "paper_R_environment_subst ?r A \<in> paper_R_closed_terms \<Sigma> G \<sigma>"
    by (rule paper_R_representative_substitution_closed_terms[OF argument typed aa])
  have whole: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>" by (rule paper_R_language_App[OF head argument])
  show ?thesis by (simp only: paper_R_identity_denote_eq[OF whole] paper_R_identity_denote_eq[OF head]
    paper_R_identity_denote_eq[OF argument] paper_R_environment_subst.simps;
    rule sym[OF paper_R_identity_application_classes[where S=S, OF rich fc ac]])
qed

end
