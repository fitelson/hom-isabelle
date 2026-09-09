theory Bacon_Book_Classicism_Syntax
  imports Bacon_Book_Environment_Development.Bacon_Book_Minimal_Leibniz_Syntax
    Bacon_Book_Environment_Development.Bacon_Book_Logic
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Intersections
begin

section \<open>The Rule-of-Equivalence base over full-F book syntax\<close>

text \<open>
  Source-scope boundary: Chapter 6 develops the Rule of Equivalence
  under the relational-type restriction. Section 8.1, p.160, extends
  Classicism to full F by including Modalized Functionality at all
  types; endnote 5 (p.178) gives the MF plus Propositional Equivalence
  presentation. The definitions below implement the Equivalence-rule
  base over full-F syntax, not that completed full-type extension.
  Existing theorem names are retained. An explicit extension and
  proof/consistency/Henkin transfer are required before invoking the
  functional-type step of Chapter 18 for full Classicism.
\<close>

definition book_vector_application :: "'c book_named_term \<Rightarrow> nat list \<Rightarrow> 'c book_named_term" where
  "book_vector_application R ns = foldl NApp R (map NVar ns)"

definition book_equivalence_rule_instance ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat list \<Rightarrow> 'c book_named_term \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_equivalence_rule_instance \<Sigma> G ns R S \<longleftrightarrow>
    distinct ns \<and> set ns \<inter> (named_fv R \<union> named_fv S) = {} \<and>
    book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G ns) Prop) \<and>
    book_in_language book_minimal_logical_type UNIV \<Sigma> G S (foldr Arr (map G ns) Prop)"

definition book_equivalence_closed ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_equivalence_closed \<Sigma> G T \<longleftrightarrow>
    (\<forall>ns R S. book_equivalence_rule_instance \<Sigma> G ns R S \<longrightarrow>
      book_iff G (book_vector_application R ns) (book_vector_application S ns) \<in> T \<longrightarrow>
      book_leibniz G (foldr Arr (map G ns) Prop) R S \<in> T)"

definition book_classicist_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_classicist_theory \<Sigma> G T \<longleftrightarrow>
    book_higher_order_theory \<Sigma> G T \<and> book_equivalence_closed \<Sigma> G T"

definition book_C :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_C \<Sigma> G A \<longleftrightarrow> book_theory_formula \<Sigma> G A \<and>
    (\<forall>T. book_classicist_theory \<Sigma> G T \<longrightarrow> A \<in> T)"

lemma book_equivalence_conclusion_language:
  assumes rich: "sg_rich G" and instance_ok: "book_equivalence_rule_instance \<Sigma> G ns R S"
  shows "book_theory_formula \<Sigma> G (book_leibniz G (foldr Arr (map G ns) Prop) R S)"
  using instance_ok unfolding book_equivalence_rule_instance_def
  by (intro book_leibniz_language[OF rich]; blast)

text \<open>
  Definition 6.1, p.126: C is the least higher-order theory closed
  under the Rule of Equivalence. The premise is R x₁…xₙ ↔ S x₁…xₙ,
  with distinct argument variables absent from FV(R)∪FV(S); the
  conclusion is their Leibniz identity at σ₁→…→σₙ→t.

  This is the book's named full-F language and minimal →/∀ basis.
  ↔ and identity are the literal closed operators of Table 4.1.
  The argument types may be arbitrary F types; no R restriction or
  primitive paper identity is inserted. The empty vector is the
  propositional case. The formula guard prevents raw nonformulas
  from belonging to an empty-family intersection.
  No soundness, completeness, substitution or modal rule is assumed.
\<close>

end
