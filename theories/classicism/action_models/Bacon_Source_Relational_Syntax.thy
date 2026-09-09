theory Bacon_Source_Relational_Syntax
  imports Bacon_Source_Relational_Types
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Syntax
begin

section \<open>Named terms over the relational type system\<close>

text \<open>
  In the paper's default language, A:σ requires R types throughout the
  expression. For λn.A:σ→τ, both σ and τ belong to R and τ≠e.
  Source: Bacon–Dorr §1.1, p.5. The logical constants remain first-class
  terms; their entire declared type, including quantifier indices, must
  belong to R.

  Representation: paper_R_has_type is an independent judgment on the
  existing named AST. paper_R_in_language adds the declared nonlogical
  signature. Embedding into F is proved below, not used as the definition.
  Status: grammar and typing only, with no R proof system, model interface,
  completeness, or conservativity assertion.
\<close>

inductive paper_R_has_type ::
  "sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> otype \<Rightarrow> bool"
  for G :: sgcontext where
  Var: "paper_R_type (G n) \<Longrightarrow> paper_R_has_type G (NVar n) (G n)"
| Const: "paper_R_type \<sigma> \<Longrightarrow> paper_R_has_type G (NConst c \<sigma>) \<sigma>"
| Logical: "paper_R_type (paper_logical_type l) \<Longrightarrow>
    paper_R_has_type G (NLogical l) (paper_logical_type l)"
| App: "paper_R_has_type G F (Arr \<sigma> \<tau>) \<Longrightarrow> paper_R_has_type G A \<sigma> \<Longrightarrow>
    paper_R_has_type G (NApp F A) \<tau>"
| Lam: "paper_R_has_type G A \<tau> \<Longrightarrow> paper_R_type (G n) \<Longrightarrow> \<tau> \<noteq> Ind \<Longrightarrow>
    paper_R_has_type G (NLam n A) (Arr (G n) \<tau>)"

definition paper_R_in_language ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> otype \<Rightarrow> bool" where
  "paper_R_in_language \<Sigma> G A \<sigma> \<longleftrightarrow>
    paper_R_has_type G A \<sigma> \<and> named_in_signature \<Sigma> A"

definition paper_R_rich :: "sgcontext \<Rightarrow> bool" where
  "paper_R_rich G \<longleftrightarrow> (\<forall>\<sigma>. paper_R_type \<sigma> \<longrightarrow> infinite {n. G n = \<sigma>})"

lemma paper_R_rich_from_F:
  assumes "sg_rich G"
  shows "paper_R_rich G"
  using assms unfolding sg_rich_def paper_R_rich_def by blast

lemma paper_R_rich_type:
  assumes "paper_R_rich G" and "paper_R_type \<sigma>"
  shows "infinite {n. G n = \<sigma>}"
  using assms unfolding paper_R_rich_def by blast

theorem paper_R_result_type:
  assumes "paper_R_has_type G A \<sigma>"
  shows "paper_R_type \<sigma>"
  using assms by (induction rule: paper_R_has_type.induct) simp_all

theorem paper_R_has_type_embedding:
  assumes "paper_R_has_type G A \<sigma>"
  shows "has_ntype paper_logical_type G A \<sigma>"
  using assms
  by (induction rule: paper_R_has_type.induct) (auto intro: has_ntype.intros)

theorem paper_R_language_embedding:
  assumes "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
  using assms unfolding paper_R_in_language_def named_in_language_def
  by (auto intro: paper_R_has_type_embedding)

lemma paper_R_language_result_type:
  assumes "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "paper_R_type \<sigma>"
  using assms unfolding paper_R_in_language_def by (auto intro: paper_R_result_type)

lemma paper_R_type_unique:
  assumes first: "paper_R_has_type G A \<sigma>" and second: "paper_R_has_type G A \<tau>"
  shows "\<sigma> = \<tau>"
  by (rule named_type_unique[OF paper_R_has_type_embedding[OF first]
    paper_R_has_type_embedding[OF second]])

lemma paper_R_logical_type_iff:
  "paper_R_has_type G (NLogical l) \<sigma> \<longleftrightarrow>
    \<sigma> = paper_logical_type l \<and> paper_R_type (paper_logical_type l)"
  by (auto elim: paper_R_has_type.cases intro: paper_R_has_type.Logical)

lemma paper_R_app_type_obtain:
  assumes typed: "paper_R_has_type G (NApp F A) \<tau>"
  obtains \<sigma> where "paper_R_has_type G F (Arr \<sigma> \<tau>)" and "paper_R_has_type G A \<sigma>"
  using typed by (cases rule: paper_R_has_type.cases) auto

lemma paper_R_lam_type_obtain:
  assumes typed: "paper_R_has_type G (NLam n A) \<sigma>"
  obtains \<tau> where "\<sigma> = Arr (G n) \<tau>" and "paper_R_has_type G A \<tau>"
    and "paper_R_type (G n)" and "\<tau> \<noteq> Ind"
  using typed by (cases rule: paper_R_has_type.cases) auto

section \<open>A proposition-valued F sentence outside R\<close>

text \<open>
  The sentence ∀f:e→e.(f=f) has result type t but is not an R term.
  Its quantifier already has a non-R declared type. Thus an F typing
  derivation together with σ∈R does not certify the R grammar.
\<close>

definition paper_F_function_reflexivity :: "nat \<Rightarrow> 'c paper_named_term" where
  "paper_F_function_reflexivity n =
    NApp (NLogical (SAll (Arr Ind Ind)))
      (NLam n (NApp (NApp (NLogical (SEq (Arr Ind Ind))) (NVar n)) (NVar n)))"

lemma paper_F_function_reflexivity_language:
  assumes nt: "G n = Arr Ind Ind"
  shows "named_in_language paper_logical_type \<Sigma> G (paper_F_function_reflexivity n) Prop"
proof -
  have variable_type: "has_ntype paper_logical_type G (NVar n) (Arr Ind Ind)"
    using has_ntype.Var[where L=paper_logical_type and G=G and n=n] by (simp only: nt)
  have equality_type: "has_ntype paper_logical_type G (NLogical (SEq (Arr Ind Ind)))
      (Arr (Arr Ind Ind) (Arr (Arr Ind Ind) Prop))"
    using has_ntype.Logical[where L=paper_logical_type and G=G and l="SEq (Arr Ind Ind)"] by simp
  have body_type: "has_ntype paper_logical_type G
      (NApp (NApp (NLogical (SEq (Arr Ind Ind))) (NVar n)) (NVar n)) Prop"
    by (rule has_ntype.App[OF has_ntype.App[OF equality_type variable_type] variable_type])
  have predicate_type: "has_ntype paper_logical_type G
      (NLam n (NApp (NApp (NLogical (SEq (Arr Ind Ind))) (NVar n)) (NVar n)))
      (Arr (Arr Ind Ind) Prop)"
    using has_ntype.Lam[OF body_type, where n=n] by (simp only: nt)
  have quantifier_type: "has_ntype paper_logical_type G (NLogical (SAll (Arr Ind Ind)))
      (Arr (Arr (Arr Ind Ind) Prop) Prop)"
    using has_ntype.Logical[where L=paper_logical_type and G=G and l="SAll (Arr Ind Ind)"] by simp
  have typed: "has_ntype paper_logical_type G (paper_F_function_reflexivity n) Prop"
    unfolding paper_F_function_reflexivity_def
    by (rule has_ntype.App[OF quantifier_type predicate_type])
  show ?thesis using typed
    by (simp add: named_in_language_def paper_F_function_reflexivity_def)
qed

lemma paper_F_function_reflexivity_closed:
  "named_fv (paper_F_function_reflexivity n) = {}"
  by (simp add: paper_F_function_reflexivity_def)

lemma paper_F_function_reflexivity_not_R:
  "\<not> paper_R_has_type G (paper_F_function_reflexivity n) Prop"
proof
  assume typed: "paper_R_has_type G (paper_F_function_reflexivity n) Prop"
  from typed show False unfolding paper_F_function_reflexivity_def
    by (cases rule: paper_R_has_type.cases) (auto simp: paper_R_logical_type_iff)
qed

end
