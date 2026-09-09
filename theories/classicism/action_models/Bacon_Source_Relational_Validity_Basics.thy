theory Bacon_Source_Relational_Validity_Basics
  imports Bacon_Source_Relational_Logical_Truth Bacon_Source_Relational_Binder_Truth
    Bacon_Source_Relational_Assignment_Denotation
begin

section \<open>Validity and guarded assignment updates in R\<close>

text \<open>
  A holds in M when valM(⟦A⟧ᵍ) holds for every typed assignment
  adequate for A (Definition 3.1, p.44). An update at n leaves
  ⟦A⟧ unchanged if n∉FV(A), and remains typed when its value
  belongs to D(G n). These are semantic facts, not H inference rules.
  The independent R model and partial-assignment conventions are retained.
\<close>

lemma paper_R_imp_adequate_iff:
  "named_adequate g (named_paper_imp G A B) \<longleftrightarrow> named_adequate g A \<and> named_adequate g B"
  by (simp add: named_adequate_def named_paper_defined_fv)

context paper_R_bbk_model
begin

lemma paper_R_validI:
  assumes language: "paper_R_in_language signature stock A Prop"
    and truth: "\<And>g. named_env_typed domain stock g \<Longrightarrow> named_adequate g A \<Longrightarrow>
      valuation (denote g A)"
  shows "paper_R_valid A"
  unfolding paper_R_valid_def paper_R_satisfies_def
  by (rule conjI[OF language], intro allI impI, rule truth; assumption)

lemma paper_R_validE:
  assumes valid: "paper_R_valid A" and typed: "named_env_typed domain stock g"
    and adequate: "named_adequate g A"
  shows "valuation (denote g A)"
  using valid typed adequate unfolding paper_R_valid_def paper_R_satisfies_def by blast

lemma paper_R_valid_language:
  "paper_R_valid A \<Longrightarrow> paper_R_in_language signature stock A Prop"
  unfolding paper_R_valid_def by (rule conjunct1)

lemma paper_R_fresh_update_denote:
  assumes language: "paper_R_in_language signature stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and member: "a \<in> domain (stock n)" and fresh: "n \<notin> named_fv A"
  shows "denote (g(n := Some a)) A = denote g A"
proof -
  have updated: "named_env_typed domain stock (g(n := Some a))"
    by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed member])
  have updated_adequate: "named_adequate (g(n := Some a)) A"
    by (rule named_adequate_update[OF adequate])
  show ?thesis
  proof (rule denote_locality[OF language updated typed updated_adequate adequate])
    fix m
    assume free: "m \<in> named_fv A"
    show "(g(n := Some a)) m = g m" by (rule named_update_fresh_agreement[OF fresh free])
  qed
qed

lemma paper_R_binder_quantifier_language:
  assumes body: "paper_R_in_language signature stock A Prop"
    and nt: "stock n = \<sigma>" and rt: "paper_R_type \<sigma>"
    and symbol: "paper_logical_type l = Arr (Arr \<sigma> Prop) Prop"
  shows "paper_R_in_language signature stock (NApp (NLogical l) (NLam n A)) Prop"
proof -
  have nr: "paper_R_type (stock n)" by (simp only: nt; rule rt)
  have predicate: "paper_R_in_language signature stock (NLam n A) (Arr \<sigma> Prop)"
    using paper_R_binder_formula_language[OF body nr] by (simp only: nt)
  have operator_R: "paper_R_type (paper_logical_type l)" by (simp add: symbol rt)
  have operator_type: "paper_R_has_type stock (NLogical l) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=stock, OF operator_R] by (simp only: symbol)
  have operator_language: "paper_R_in_language signature stock (NLogical l) (Arr (Arr \<sigma> Prop) Prop)"
    unfolding paper_R_in_language_def by (rule conjI[OF operator_type]; simp)
  show ?thesis by (rule paper_R_language_App[OF operator_language predicate])
qed

end

end
