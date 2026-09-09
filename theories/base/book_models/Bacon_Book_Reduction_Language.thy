theory Bacon_Book_Reduction_Language
  imports Bacon_Book_Variable_Substitution_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Literal contraction preserves the full declared language\<close>

text \<open>
  A single β or η contraction of a typed term preserves its type,
  nonlogical signature and permitted logical symbols. The β rule itself
  carries the source free-for proviso. Source role: directional reduction
  closure in Definition 9.1, p.190; this is not closure under expansion.
\<close>

lemma book_beta_contract_language:
  assumes step: "named_beta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
proof -
  obtain N n M where source: "A = NApp (NLam n M) N" and target: "B = named_subst n N M"
    using step by (cases rule: named_beta_contract.cases) blast
  have redex: "book_in_language L \<Lambda> \<Sigma> G (NApp (NLam n M) N) \<tau>"
    using language by (simp only: source)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G (NLam n M) (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G N \<sigma>"
    by (rule book_language_App_obtain[OF redex]; rule that; assumption)
  obtain \<rho> where arrow: "Arr \<sigma> \<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<rho>"
    by (rule book_language_Lam_obtain[OF head]; rule that; assumption)
  have body_type: "book_in_language L \<Lambda> \<Sigma> G M \<tau>" using body arrow by simp
  have argument_type: "book_in_language L \<Lambda> \<Sigma> G N (G n)" using argument arrow by simp
  show ?thesis by (simp only: target; rule book_variable_subst_language[OF body_type argument_type])
qed

lemma book_eta_contract_language:
  assumes step: "named_eta_contract A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
proof -
  obtain n F where source: "A = NLam n (NApp F (NVar n))" and target: "B = F"
    using step by (cases rule: named_eta_contract.cases) blast
  have redex: "book_in_language L \<Lambda> \<Sigma> G (NLam n (NApp F (NVar n))) \<tau>"
    using language by (simp only: source)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G (NApp F (NVar n)) \<rho>"
    by (rule book_language_Lam_obtain[OF redex]; rule that; assumption)
  obtain \<sigma> where head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<rho>)"
    and variable: "book_in_language L \<Lambda> \<Sigma> G (NVar n) \<sigma>"
    by (rule book_language_App_obtain[OF body]; rule that; assumption)
  have same: "\<sigma> = G n" using variable by (simp only: book_language_var_iff)
  show ?thesis using head same arrow target by simp
qed

end
