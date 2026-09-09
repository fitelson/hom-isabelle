theory Bacon_Source_Relational_Henkin_Full_Signature
  imports Bacon_Source_Relational_Henkin_Stage_Signature
begin

section \<open>Every full-signature term already belongs to a finite stage\<close>

text \<open>
  Σ∞ρ is the union of the successive witness signatures. A term has
  finitely many object-language constant occurrences: a constant picks
  one stage, application takes the maximum of two bounds, and λ keeps
  its body's bound. The predicate payload inside an RWitness NAME is
  not traversed as an object-language subterm.

  Source role: closure of the expanded language in Theorem 3.2,
  p.45 n.64. Each stage may be uncountable. This argument neither
  enumerates formulas nor assumes richness, consistency, witness-axiom
  membership, a maximal theory, or a model.
\<close>

definition paper_R_henkin_full_signature ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c paper_R_henkin_name) ssignature" where
  "paper_R_henkin_full_signature \<Sigma> G \<rho> = (\<Union>n. paper_R_henkin_signature \<Sigma> G n \<rho>)"

lemma paper_R_henkin_stage_in_full:
  "paper_R_henkin_signature \<Sigma> G n \<rho> \<subseteq> paper_R_henkin_full_signature \<Sigma> G \<rho>"
  by (auto simp: paper_R_henkin_full_signature_def)

lemma paper_R_henkin_full_original_iff:
  "ROriginal c \<in> paper_R_henkin_full_signature \<Sigma> G \<rho> \<longleftrightarrow> c \<in> \<Sigma> \<rho>"
  by (auto simp: paper_R_henkin_full_signature_def paper_R_henkin_signature_original_iff)

lemma paper_R_henkin_stage_names_mono:
  assumes names: "named_in_signature (paper_R_henkin_signature \<Sigma> G m) A" and order: "m \<le> n"
  shows "named_in_signature (paper_R_henkin_signature \<Sigma> G n) A"
  using names
proof (induction A)
  case (NVar x)
  show ?case by simp
next
  case (NConst c \<rho>)
  have member: "c \<in> paper_R_henkin_signature \<Sigma> G m \<rho>" using NConst.prems by simp
  have expanded: "c \<in> paper_R_henkin_signature \<Sigma> G n \<rho>"
    by (rule subsetD[OF paper_R_henkin_signature_mono[OF order] member])
  show ?case using expanded by simp
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

theorem paper_R_henkin_full_names_eventual:
  assumes names: "named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A"
  shows "\<exists>n. named_in_signature (paper_R_henkin_signature \<Sigma> G n) A"
  using names
proof (induction A)
  case (NVar x)
  show ?case by (rule exI[where x=0]; simp)
next
  case (NConst c \<rho>)
  have member: "c \<in> paper_R_henkin_full_signature \<Sigma> G \<rho>" using NConst.prems by simp
  obtain n where stage: "c \<in> paper_R_henkin_signature \<Sigma> G n \<rho>"
    using member unfolding paper_R_henkin_full_signature_def by blast
  show ?case by (rule exI[where x=n]; simp add: stage)
next
  case (NLogical l)
  show ?case by (rule exI[where x=0]; simp)
next
  case (NApp F A)
  have fn: "named_in_signature (paper_R_henkin_full_signature \<Sigma> G) F"
    and an: "named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A" using NApp.prems by simp_all
  obtain m where fm: "named_in_signature (paper_R_henkin_signature \<Sigma> G m) F" using NApp.IH(1)[OF fn] by blast
  obtain n where am: "named_in_signature (paper_R_henkin_signature \<Sigma> G n) A" using NApp.IH(2)[OF an] by blast
  have fmax: "named_in_signature (paper_R_henkin_signature \<Sigma> G (max m n)) F"
    by (rule paper_R_henkin_stage_names_mono[OF fm max.cobounded1])
  have amax: "named_in_signature (paper_R_henkin_signature \<Sigma> G (max m n)) A"
    by (rule paper_R_henkin_stage_names_mono[OF am max.cobounded2])
  show ?case by (rule exI[where x="max m n"]; simp add: fmax amax)
next
  case (NLam x A)
  have body: "named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A" using NLam.prems by simp
  obtain n where stage: "named_in_signature (paper_R_henkin_signature \<Sigma> G n) A" using NLam.IH[OF body] by blast
  show ?case by (rule exI[where x=n]; simp add: stage)
qed

lemma paper_R_henkin_stage_language_mono:
  assumes language: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G m) G A \<rho>" and order: "m \<le> n"
  shows "paper_R_in_language (paper_R_henkin_signature \<Sigma> G n) G A \<rho>"
  by (rule paper_R_language_signature_mono[OF language]; rule paper_R_henkin_signature_mono[OF order])

theorem paper_R_henkin_full_language_eventual:
  assumes language: "paper_R_in_language (paper_R_henkin_full_signature \<Sigma> G) G A \<rho>"
  shows "\<exists>n. paper_R_in_language (paper_R_henkin_signature \<Sigma> G n) G A \<rho>"
proof -
  have typed: "paper_R_has_type G A \<rho>" and names: "named_in_signature (paper_R_henkin_full_signature \<Sigma> G) A"
    using language unfolding paper_R_in_language_def by blast+
  obtain n where stage: "named_in_signature (paper_R_henkin_signature \<Sigma> G n) A"
    using paper_R_henkin_full_names_eventual[OF names] by blast
  have in_stage: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G n) G A \<rho>"
    unfolding paper_R_in_language_def by (rule conjI[OF typed stage])
  show ?thesis by (rule exI[where x=n]; rule in_stage)
qed

theorem paper_R_henkin_full_language_eventually:
  assumes language: "paper_R_in_language (paper_R_henkin_full_signature \<Sigma> G) G A \<rho>"
  shows "\<exists>n. \<forall>m\<ge>n. paper_R_in_language (paper_R_henkin_signature \<Sigma> G m) G A \<rho>"
proof -
  obtain n where stage: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G n) G A \<rho>"
    using paper_R_henkin_full_language_eventual[OF language] by blast
  show ?thesis by (rule exI[where x=n], intro allI impI; rule paper_R_henkin_stage_language_mono[OF stage]; assumption)
qed

section \<open>Every closed full-signature predicate receives an actual witness name\<close>

theorem paper_R_henkin_full_closed_predicate_witness:
  assumes predicate: "paper_R_in_language (paper_R_henkin_full_signature \<Sigma> G) G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}"
  shows "\<exists>n. (\<sigma>,F) \<in> paper_R_henkin_stage_indices \<Sigma> G n \<and>
    RWitness n \<sigma> F \<in> paper_R_henkin_full_signature \<Sigma> G \<sigma>"
proof -
  obtain n where stage: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G n) G F (Arr \<sigma> Prop)"
    using paper_R_henkin_full_language_eventual[OF predicate] by blast
  have index: "(\<sigma>,F) \<in> paper_R_henkin_stage_indices \<Sigma> G n"
    by (rule paper_R_henkin_stage_indexI[OF closed stage])
  have witness: "RWitness n \<sigma> F \<in> paper_R_henkin_signature \<Sigma> G (Suc n) \<sigma>"
    by (rule paper_R_henkin_signature_witness[OF closed stage])
  have full: "RWitness n \<sigma> F \<in> paper_R_henkin_full_signature \<Sigma> G \<sigma>"
    by (rule subsetD[OF paper_R_henkin_stage_in_full witness])
  show ?thesis by (rule exI[where x=n], rule conjI[OF index full])
qed

end
