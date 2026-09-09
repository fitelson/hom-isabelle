theory Bacon_Book_Henkin_Full_Signature
  imports Bacon_Book_Henkin_Name_Stages
begin

section \<open>The union of the successive witness signatures\<close>

text \<open>
  Σ∞σ is the union of Σₙσ over the natural-number stages n. Each
  stage may contain arbitrarily many constants. Every individual term
  over Σ∞ already lies in one stage: variables and logical symbols
  need no constants, a constant belongs to one stage, application takes
  the maximum of the two stages, and abstraction preserves the stage.

  The syntax treats the predicate payload of BookWitness as part of an
  atomic constant name. It does not recursively inspect that payload.
  Source role: closure of the staged fresh-name construction supporting
  Bacon's Proposition 15.4. No richness, countability of the signature,
  enumeration of terms, proof judgment, or model premise is assumed.
\<close>

definition book_henkin_full_signature ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c book_henkin_name) ssignature" where
  "book_henkin_full_signature \<Sigma> G \<tau> = (\<Union>n. book_henkin_signature \<Sigma> G n \<tau>)"

lemma book_henkin_stage_in_full:
  "book_henkin_signature \<Sigma> G n \<tau> \<subseteq> book_henkin_full_signature \<Sigma> G \<tau>"
  by (auto simp: book_henkin_full_signature_def)

lemma book_henkin_full_original_iff:
  "BookOriginal c \<in> book_henkin_full_signature \<Sigma> G \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
  by (auto simp: book_henkin_full_signature_def book_henkin_signature_original_iff)

lemma book_henkin_stage_names_mono:
  assumes names: "named_in_signature (book_henkin_signature \<Sigma> G m) A"
    and order: "m \<le> n"
  shows "named_in_signature (book_henkin_signature \<Sigma> G n) A"
  using names
proof (induction A)
  case (NVar x)
  show ?case by simp
next
  case (NConst c \<tau>)
  have member: "c \<in> book_henkin_signature \<Sigma> G m \<tau>" using NConst.prems by simp
  have enlarged: "c \<in> book_henkin_signature \<Sigma> G n \<tau>"
    by (rule subsetD[OF book_henkin_signature_mono[OF order] member])
  show ?case using enlarged by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case using NApp.prems NApp.IH by simp
next
  case (NLam x A)
  show ?case using NLam.prems NLam.IH by simp
qed

theorem book_henkin_full_names_eventual:
  assumes names: "named_in_signature (book_henkin_full_signature \<Sigma> G) A"
  shows "\<exists>n. named_in_signature (book_henkin_signature \<Sigma> G n) A"
  using names
proof (induction A)
  case (NVar x)
  show ?case by (rule exI[where x=0], simp)
next
  case (NConst c \<tau>)
  have member: "c \<in> book_henkin_full_signature \<Sigma> G \<tau>" using NConst.prems by simp
  obtain n where stage: "c \<in> book_henkin_signature \<Sigma> G n \<tau>"
    using member unfolding book_henkin_full_signature_def by blast
  show ?case by (rule exI[where x=n], simp add: stage)
next
  case (NLogical l)
  show ?case by (rule exI[where x=0], simp)
next
  case (NApp F A)
  have fn: "named_in_signature (book_henkin_full_signature \<Sigma> G) F"
    and an: "named_in_signature (book_henkin_full_signature \<Sigma> G) A"
    using NApp.prems by simp_all
  obtain m where fm: "named_in_signature (book_henkin_signature \<Sigma> G m) F"
    using NApp.IH(1)[OF fn] by blast
  obtain n where an_stage: "named_in_signature (book_henkin_signature \<Sigma> G n) A"
    using NApp.IH(2)[OF an] by blast
  have fmax: "named_in_signature (book_henkin_signature \<Sigma> G (max m n)) F"
    by (rule book_henkin_stage_names_mono[OF fm max.cobounded1])
  have amax: "named_in_signature (book_henkin_signature \<Sigma> G (max m n)) A"
    by (rule book_henkin_stage_names_mono[OF an_stage max.cobounded2])
  show ?case by (rule exI[where x="max m n"], simp add: fmax amax)
next
  case (NLam x A)
  have body: "named_in_signature (book_henkin_full_signature \<Sigma> G) A"
    using NLam.prems by simp
  obtain n where stage: "named_in_signature (book_henkin_signature \<Sigma> G n) A"
    using NLam.IH[OF body] by blast
  show ?case by (rule exI[where x=n], simp add: stage)
qed

section \<open>Language membership and eventual witness availability\<close>

lemma book_henkin_stage_language_mono:
  assumes language: "book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G m) G A \<tau>"
    and order: "m \<le> n"
  shows "book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G n) G A \<tau>"
proof -
  have names: "named_in_signature (book_henkin_signature \<Sigma> G m) A"
    by (rule book_language_signature[OF language])
  have enlarged: "named_in_signature (book_henkin_signature \<Sigma> G n) A"
    by (rule book_henkin_stage_names_mono[OF names order])
  show ?thesis using language enlarged
    unfolding book_in_language_def named_in_language_def by blast
qed

theorem book_henkin_full_language_eventual:
  assumes language: "book_in_language L \<Lambda> (book_henkin_full_signature \<Sigma> G) G A \<tau>"
  shows "\<exists>n. book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G n) G A \<tau>"
proof -
  have names: "named_in_signature (book_henkin_full_signature \<Sigma> G) A"
    by (rule book_language_signature[OF language])
  obtain n where stage_names: "named_in_signature (book_henkin_signature \<Sigma> G n) A"
    using book_henkin_full_names_eventual[OF names] by blast
  have stage_language: "book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G n) G A \<tau>"
    using language stage_names unfolding book_in_language_def named_in_language_def by blast
  show ?thesis by (rule exI[where x=n], rule stage_language)
qed

theorem book_henkin_full_language_eventually:
  assumes language: "book_in_language L \<Lambda> (book_henkin_full_signature \<Sigma> G) G A \<tau>"
  shows "\<exists>n. \<forall>m\<ge>n. book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G m) G A \<tau>"
proof -
  obtain n where stage: "book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G n) G A \<tau>"
    using book_henkin_full_language_eventual[OF language] by blast
  have later: "\<forall>m\<ge>n. book_in_language L \<Lambda> (book_henkin_signature \<Sigma> G m) G A \<tau>"
    by (intro allI impI, rule book_henkin_stage_language_mono[OF stage], assumption)
  show ?thesis by (rule exI[where x=n], rule later)
qed

corollary book_henkin_full_closed_predicate_witness:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "\<exists>n. book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G n) G F (Arr \<sigma> Prop) \<and>
    BookWitness n \<sigma> F \<in> book_henkin_full_signature \<Sigma> G \<sigma>"
proof -
  obtain n where stage: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G n) G F (Arr \<sigma> Prop)"
    using book_henkin_full_language_eventual[OF predicate] by blast
  have witness: "BookWitness n \<sigma> F \<in> book_henkin_signature \<Sigma> G (Suc n) \<sigma>"
    by (rule book_henkin_signature_witness[OF closed stage])
  have full: "BookWitness n \<sigma> F \<in> book_henkin_full_signature \<Sigma> G \<sigma>"
    by (rule subsetD[OF book_henkin_stage_in_full witness])
  show ?thesis by (rule exI[where x=n], rule conjI[OF stage full])
qed

end
