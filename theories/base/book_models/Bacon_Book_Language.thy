theory Bacon_Book_Language
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Syntax
begin

section \<open>Typed named terms with a partial logical signature\<close>

text \<open>
  A:τ belongs to the ambient language when it is well typed in G,
  its nonlogical constants belong to Σ, and each logical symbol occurring
  in A belongs to the permitted set Λ. Source: Bacon's Definition 15.1,
  pp.314–315, where a logical truth clause is required only when its
  symbol is present; Definition 14.13, p.302, guards interpreted endpoints
  by membership in the chosen λ-language.

  Representation: L assigns types to the generic logical-symbol carrier;
  Λ records the available logical symbols, while Σ retains the repository's
  typed nonlogical stock. We reuse named_term, has_ntype and named_fv.
  No paper_logical or BBK model predicate is fixed or imported.

  Status: this is the full typed named grammar over the permitted symbols,
  not yet an arbitrary general λ-sublanguage. A separate restriction on
  admitted terms may be added later. No truth clause, interpretation,
  proof rule or existence of a logical symbol is assumed. Definition
  14.13's semantic agreement condition uses FV(M) ∩ FV(N); it is not
  replaced by a union or defined in this language-only leaf.
\<close>

fun named_logical_occurrences :: "('c,'l) named_term \<Rightarrow> 'l set" where
  "named_logical_occurrences (NVar n) = {}"
| "named_logical_occurrences (NConst c \<sigma>) = {}"
| "named_logical_occurrences (NLogical l) = {l}"
| "named_logical_occurrences (NApp F A) =
    named_logical_occurrences F \<union> named_logical_occurrences A"
| "named_logical_occurrences (NLam n A) = named_logical_occurrences A"

lemma named_logical_occurrences_finite:
  "finite (named_logical_occurrences A)"
  by (induction A) simp_all

definition book_in_language ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'l set \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    ('c,'l) named_term \<Rightarrow> otype \<Rightarrow> bool"
where
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<longleftrightarrow>
    named_in_language L \<Sigma> G A \<tau> \<and> named_logical_occurrences A \<subseteq> \<Lambda>"

lemma book_language_named:
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> named_in_language L \<Sigma> G A \<tau>"
  unfolding book_in_language_def by (rule conjunct1)

lemma book_language_type:
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> has_ntype L G A \<tau>"
  unfolding book_in_language_def named_in_language_def by blast

lemma book_language_signature:
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> named_in_signature \<Sigma> A"
  unfolding book_in_language_def named_in_language_def by blast

lemma book_language_logical_occurrences:
  "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> named_logical_occurrences A \<subseteq> \<Lambda>"
  unfolding book_in_language_def by (rule conjunct2)

lemma book_language_logical_member:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and occurs: "l \<in> named_logical_occurrences A"
  shows "l \<in> \<Lambda>"
  by (rule subsetD[OF book_language_logical_occurrences[OF language] occurs])

lemma book_language_UNIV:
  "book_in_language L UNIV \<Sigma> G A \<tau> \<longleftrightarrow> named_in_language L \<Sigma> G A \<tau>"
  by (simp add: book_in_language_def)

lemma book_language_logical_mono:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>" and inclusion: "\<Lambda> \<subseteq> \<Lambda>'"
  shows "book_in_language L \<Lambda>' \<Sigma> G A \<tau>"
  unfolding book_in_language_def
  by (rule conjI[OF book_language_named[OF language]
    subset_trans[OF book_language_logical_occurrences[OF language] inclusion]])

section \<open>Membership and formation rules\<close>

lemma book_language_var_iff:
  "book_in_language L \<Lambda> \<Sigma> G (NVar n) \<tau> \<longleftrightarrow> \<tau> = G n"
  by (simp add: book_in_language_def named_in_language_def named_var_type_iff)

lemma book_language_const_iff:
  "book_in_language L \<Lambda> \<Sigma> G (NConst c \<sigma>) \<tau> \<longleftrightarrow> \<tau> = \<sigma> \<and> c \<in> \<Sigma> \<sigma>"
  by (simp add: book_in_language_def named_in_language_def named_const_type_iff)

lemma book_language_logical_iff:
  "book_in_language L \<Lambda> \<Sigma> G (NLogical l) \<tau> \<longleftrightarrow> \<tau> = L l \<and> l \<in> \<Lambda>"
  by (simp add: book_in_language_def named_in_language_def named_logical_type_iff)

lemma book_language_Var:
  "book_in_language L \<Lambda> \<Sigma> G (NVar n) (G n)"
  by (simp only: book_language_var_iff)

lemma book_language_Logical:
  assumes present: "l \<in> \<Lambda>"
  shows "book_in_language L \<Lambda> \<Sigma> G (NLogical l) (L l)"
  by (simp only: book_language_logical_iff; rule conjI[OF refl present])

lemma book_language_App:
  assumes head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
  shows "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>"
proof -
  have typed: "has_ntype L G (NApp F A) \<tau>"
    by (rule has_ntype.App[OF book_language_type[OF head] book_language_type[OF argument]])
  have names: "named_in_signature \<Sigma> (NApp F A)"
    using book_language_signature[OF head] book_language_signature[OF argument] by simp
  have logicals: "named_logical_occurrences (NApp F A) \<subseteq> \<Lambda>"
    using book_language_logical_occurrences[OF head] book_language_logical_occurrences[OF argument]
    by simp
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

lemma book_language_App_obtain:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G (NApp F A) \<tau>"
  obtains \<sigma> where "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
proof -
  obtain \<sigma> where ft: "has_ntype L G F (Arr \<sigma> \<tau>)" and at: "has_ntype L G A \<sigma>"
    by (rule named_app_type_obtain[OF book_language_type[OF language]]; rule that; assumption)
  have fn: "named_in_signature \<Sigma> F" and an: "named_in_signature \<Sigma> A"
    using book_language_signature[OF language] by simp_all
  have fl: "named_logical_occurrences F \<subseteq> \<Lambda>"
    and al: "named_logical_occurrences A \<subseteq> \<Lambda>"
    using book_language_logical_occurrences[OF language] by simp_all
  have head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    unfolding book_in_language_def named_in_language_def by (rule conjI[OF conjI[OF ft fn] fl])
  have argument: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    unfolding book_in_language_def named_in_language_def by (rule conjI[OF conjI[OF at an] al])
  show thesis by (rule that[OF head argument])
qed

lemma book_language_Lam:
  assumes body: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
proof -
  have typed: "has_ntype L G (NLam n A) (Arr (G n) \<tau>)"
    by (rule has_ntype.Lam[OF book_language_type[OF body]])
  show ?thesis using typed book_language_signature[OF body] book_language_logical_occurrences[OF body]
    unfolding book_in_language_def named_in_language_def
    by (simp only: named_in_signature.simps named_logical_occurrences.simps; intro conjI; assumption)
qed

lemma book_language_Lam_obtain:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G (NLam n A) \<tau>"
  obtains \<rho> where "\<tau> = Arr (G n) \<rho>" and "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
proof -
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>" and typed: "has_ntype L G A \<rho>"
    by (rule named_lam_type_obtain[OF book_language_type[OF language]]; rule that; assumption)
  have names: "named_in_signature \<Sigma> A" using book_language_signature[OF language] by simp
  have logicals: "named_logical_occurrences A \<subseteq> \<Lambda>"
    using book_language_logical_occurrences[OF language] by simp
  have body: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    unfolding book_in_language_def named_in_language_def by (rule conjI[OF conjI[OF typed names] logicals])
  show thesis by (rule that[OF arrow body])
qed

lemma book_language_type_unique:
  assumes first: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    and second: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "\<sigma> = \<tau>"
  by (rule named_type_unique[OF book_language_type[OF first] book_language_type[OF second]])

text \<open>
  The free-variable operation is unchanged: named_fv(NApp F A) is
  FV(F) ∪ FV(A), and named_fv(NLam n A) is FV(A) − {n}.
  We reuse named_fv.simps and named_fv_finite directly rather than
  introduce a second notion of free occurrence. No additional predicate
  selecting a general λ-sublanguage is imposed here.
\<close>

end
