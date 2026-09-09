theory Bacon_Source_Relational_Recoding_Denotation
  imports Bacon_Source_Relational_Recoding_Assignments
begin

section \<open>Change the carrier using an injection on the actual domain union\<close>

text \<open>
  Put U=⋃σDσ and let f be injective on U. Define D′σ=f[Dσ],
  J′(g,A)=f(J(f⁻¹∘g,A)), and V′(b)=V(f⁻¹(b)), where the inverse
  is justified on f[U]. Source: Definition 3.1 and the countable-model
  refinement of Theorem 3.2, pp.43–45.

  No injection of the entire ambient value type is required. In
  particular, a countable collection of class values can be recoded
  even when the surrounding powerset-valued HOL type is uncountable.
  Typing and adequacy supply every inverse law used for denotations.
\<close>

context paper_R_bbk_model
begin

definition paper_R_recode_denote ::
  "('v \<Rightarrow> 'w) \<Rightarrow> 'w named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'w" where
  "paper_R_recode_denote f g A =
    f (denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A)"

definition paper_R_recode_valuation :: "('v \<Rightarrow> 'w) \<Rightarrow> 'w \<Rightarrow> bool" where
  "paper_R_recode_valuation f b = valuation (paper_R_recode_inverse domain f b)"

lemma paper_R_recode_denote_inverse:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and language: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and adequate: "named_adequate g A"
  shows "paper_R_recode_inverse domain f (paper_R_recode_denote f g A) =
    denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A"
proof -
  have dt: "named_env_typed domain stock (paper_R_recode_assignment (paper_R_recode_inverse domain f) g)"
    by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A"
    by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
  have member: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A \<in> domain \<sigma>"
    by (rule denote_type[OF language dt da])
  show ?thesis unfolding paper_R_recode_denote_def
    by (rule paper_R_recode_inverse_on[OF injective member])
qed

lemma paper_R_recode_truth:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and language: "paper_R_in_language signature stock A Prop"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and adequate: "named_adequate g A"
  shows "paper_R_recode_valuation f (paper_R_recode_denote f g A) =
    valuation (denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A)"
  by (simp only: paper_R_recode_valuation_def
    paper_R_recode_denote_inverse[OF injective language typed adequate])

theorem paper_R_recode_denote_type:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and language: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and adequate: "named_adequate g A"
  shows "paper_R_recode_denote f g A \<in> paper_R_recode_domain f domain \<sigma>"
proof -
  have dt: "named_env_typed domain stock (paper_R_recode_assignment (paper_R_recode_inverse domain f) g)"
    by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have da: "named_adequate (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A"
    by (rule iffD2[OF paper_R_recode_assignment_adequate_iff adequate])
  have member: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A \<in> domain \<sigma>"
    by (rule denote_type[OF language dt da])
  show ?thesis unfolding paper_R_recode_denote_def paper_R_recode_domain_def
    by (rule imageI[OF member])
qed

theorem paper_R_recode_denote_var:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and assigned: "g n = Some b"
  shows "paper_R_recode_denote f g (NVar n) = b"
proof -
  have dt: "named_env_typed domain stock (paper_R_recode_assignment (paper_R_recode_inverse domain f) g)"
    by (rule paper_R_recode_inverse_assignment_typed[OF injective typed])
  have dn: "paper_R_recode_assignment (paper_R_recode_inverse domain f) g n = Some (paper_R_recode_inverse domain f b)"
    by (simp only: paper_R_recode_assignment_def assigned option.simps)
  have value_eq: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) (NVar n) =
      paper_R_recode_inverse domain f b" by (rule denote_var[OF dt dn])
  have member: "b \<in> paper_R_recode_domain f domain (stock n)"
    by (rule named_env_value[OF typed assigned])
  show ?thesis by (simp only: paper_R_recode_denote_def value_eq;
    rule paper_R_recode_inverse_right[OF member])
qed

end

end
