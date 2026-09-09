theory Bacon_Parametric_Canonical_Truth
  imports Bacon_Parametric_Canonical_Domain
begin

section \<open>Canonical valuation and propositional truth\<close>

text \<open>
  val([P]ₜ) = 1 iff P ∈ T.  Identity substitution makes this independent
  of the chosen representative.  Consistency and negation completeness
  give the Boolean truth clauses, while object identity is true exactly
  when denotations are the same tagged class.  Source: Bacon–Dorr,
  Definition 3.1 and p.45 n.64; Bacon, Theorem 15.3, pp.320–321.

  Status: conditional on pH_closed_Henkin only.  This constructs a
  valuation and its clauses, not a Henkin-theory existence theorem.
  Propositions are not identified merely because their truth values agree.
\<close>

context pH_closed_Henkin
begin

lemma pHc_language_Neg:
  "pterm_in_language signature [] A Prop \<Longrightarrow> pterm_in_language signature [] (PNeg A) Prop"
  unfolding pterm_in_language_def by auto

lemma pHc_language_Imp:
  "pterm_in_language signature [] A Prop \<Longrightarrow> pterm_in_language signature [] B Prop \<Longrightarrow>
    pterm_in_language signature [] (PImp A B) Prop"
  unfolding pterm_in_language_def by auto

lemma pHc_language_Conj:
  "pterm_in_language signature [] A Prop \<Longrightarrow> pterm_in_language signature [] B Prop \<Longrightarrow>
    pterm_in_language signature [] (PConj A B) Prop"
  unfolding pterm_in_language_def by auto

lemma pHc_language_Disj:
  "pterm_in_language signature [] A Prop \<Longrightarrow> pterm_in_language signature [] B Prop \<Longrightarrow>
    pterm_in_language signature [] (PDisj A B) Prop"
  unfolding pterm_in_language_def by auto

lemma pHc_PC_one:
  assumes a: "A \<in> T" and lang: "pterm_in_language signature [] B Prop"
    and entails: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v B"
  shows "B \<in> T"
proof -
  have al: "pterm_in_language signature [] A Prop" by (rule pH_member_language[OF a])
  have il: "pterm_in_language signature [] (PImp A B) Prop" by (rule pHc_language_Imp[OF al lang])
  have it: "has_ptype [] (PImp A B) Prop" using il unfolding pterm_in_language_def by (rule conjunct1)
  have isig: "pterm_in_signature signature (PImp A B)" using il unfolding pterm_in_language_def by (rule conjunct2)
  have valid: "\<forall>v. pprop_eval v (PImp A B)" using entails by (simp add: pprop_eval.simps)
  have implication: "PImp A B \<in> T" by (rule pH_PC_member[OF it isig valid])
  show ?thesis by (rule pH_member_MP[OF a implication])
qed

lemma pHc_PC_two:
  assumes a: "A \<in> T" and b: "B \<in> T" and lang: "pterm_in_language signature [] C Prop"
    and entails: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v B \<longrightarrow> pprop_eval v C"
  shows "C \<in> T"
proof -
  have bl: "pterm_in_language signature [] B Prop" by (rule pH_member_language[OF b])
  have il: "pterm_in_language signature [] (PImp B C) Prop" by (rule pHc_language_Imp[OF bl lang])
  have valid: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v (PImp B C)" using entails by simp
  have implication: "PImp B C \<in> T" by (rule pHc_PC_one[OF a il valid])
  show ?thesis by (rule pH_member_MP[OF b implication])
qed

lemma pHc_false_language: "pterm_in_language signature [] (PObjFalse :: 'c pterm) Prop"
proof -
  have tt: "has_ptype [] (PObjTrue :: 'c pterm) Prop" unfolding PObjTrue_def
    by (intro has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all
  have ft: "has_ptype [] (PObjFalse :: 'c pterm) Prop" unfolding PObjFalse_def by (rule has_ptype.PNeg[OF tt])
  have fs: "pterm_in_signature signature (PObjFalse :: 'c pterm)" by (simp add: PObjFalse_def PObjTrue_def)
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF ft fs])
qed

lemma pHc_false_not_member: "(PObjFalse :: 'c pterm) \<notin> T"
proof
  assume member: "(PObjFalse :: 'c pterm) \<in> T"
  have false_language:
      "has_ptype [] (PObjFalse :: 'c pterm) Prop \<and>
       pterm_in_signature signature (PObjFalse :: 'c pterm)"
    using pHc_false_language unfolding pterm_in_language_def .
  have typed: "has_ptype [] (PObjFalse :: 'c pterm) Prop"
    and sig: "pterm_in_signature signature (PObjFalse :: 'c pterm)"
  proof -
    show "has_ptype [] (PObjFalse :: 'c pterm) Prop" by (rule conjunct1[OF false_language])
    show "pterm_in_signature signature (PObjFalse :: 'c pterm)" by (rule conjunct2[OF false_language])
  qed
  have bad: "pH_set_derivable signature [] T (PObjFalse :: 'c pterm)"
    by (rule pH_set_Assumption[OF member typed sig])
  show False using henkin bad unfolding pH_Henkin_theory_def pH_maximal_consistent_def pH_consistent_def by blast
qed

lemma pHc_not_both:
  assumes a: "A \<in> T" and na: "PNeg A \<in> T"
  shows False
proof -
  have valid: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v (PNeg A) \<longrightarrow>
      pprop_eval v (PObjFalse :: 'c pterm)"
    by (intro allI) (simp only: pprop_eval.simps; blast)
  have bad: "(PObjFalse :: 'c pterm) \<in> T"
    by (rule pHc_PC_two[OF a na pHc_false_language valid])
  show False by (rule notE[OF pHc_false_not_member bad])
qed

lemma pHc_decides:
  assumes "pterm_in_language signature [] A Prop"
  shows "A \<in> T \<or> PNeg A \<in> T"
  using henkin assms unfolding pH_Henkin_theory_def pH_maximal_consistent_def pH_negation_complete_def by blast

lemma pHc_member_Neg:
  assumes lang: "pterm_in_language signature [] A Prop"
  shows "PNeg A \<in> T \<longleftrightarrow> A \<notin> T"
  using pHc_not_both pHc_decides[OF lang] by blast

lemma pHc_member_Conj:
  assumes a: "pterm_in_language signature [] A Prop" and b: "pterm_in_language signature [] B Prop"
  shows "PConj A B \<in> T \<longleftrightarrow> A \<in> T \<and> B \<in> T"
proof
  assume member: "PConj A B \<in> T"
  have av: "\<forall>v. pprop_eval v (PConj A B) \<longrightarrow> pprop_eval v A" by simp
  have bv: "\<forall>v. pprop_eval v (PConj A B) \<longrightarrow> pprop_eval v B" by simp
  show "A \<in> T \<and> B \<in> T" by (rule conjI[OF pHc_PC_one[OF member a av] pHc_PC_one[OF member b bv]])
next
  assume members: "A \<in> T \<and> B \<in> T"
  have valid: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v B \<longrightarrow> pprop_eval v (PConj A B)" by simp
  show "PConj A B \<in> T" by (rule pHc_PC_two[OF conjunct1[OF members] conjunct2[OF members] pHc_language_Conj[OF a b] valid])
qed

lemma pHc_member_Imp:
  assumes a: "pterm_in_language signature [] A Prop" and b: "pterm_in_language signature [] B Prop"
  shows "PImp A B \<in> T \<longleftrightarrow> (A \<in> T \<longrightarrow> B \<in> T)"
proof
  assume member: "PImp A B \<in> T"
  show "A \<in> T \<longrightarrow> B \<in> T" using pH_member_MP[OF _ member] by blast
next
  assume condition: "A \<in> T \<longrightarrow> B \<in> T"
  show "PImp A B \<in> T"
  proof (cases "A \<in> T")
    case True
    have member: "B \<in> T" by (rule mp[OF condition True])
    have valid: "\<forall>v. pprop_eval v B \<longrightarrow> pprop_eval v (PImp A B)" by simp
    show ?thesis by (rule pHc_PC_one[OF member pHc_language_Imp[OF a b] valid])
  next
    case False
    have member: "PNeg A \<in> T" by (rule iffD2[OF pHc_member_Neg[OF a] False])
    have valid: "\<forall>v. pprop_eval v (PNeg A) \<longrightarrow> pprop_eval v (PImp A B)" by simp
    show ?thesis by (rule pHc_PC_one[OF member pHc_language_Imp[OF a b] valid])
  qed
qed

lemma pHc_member_Disj:
  assumes a: "pterm_in_language signature [] A Prop" and b: "pterm_in_language signature [] B Prop"
  shows "PDisj A B \<in> T \<longleftrightarrow> A \<in> T \<or> B \<in> T"
proof
  assume member: "PDisj A B \<in> T"
  show "A \<in> T \<or> B \<in> T"
  proof (cases "A \<in> T")
    case True
    show ?thesis by (rule disjI1[OF True])
  next
    case False
    have neg: "PNeg A \<in> T" by (rule iffD2[OF pHc_member_Neg[OF a] False])
    have valid: "\<forall>v. pprop_eval v (PDisj A B) \<longrightarrow> pprop_eval v (PNeg A) \<longrightarrow> pprop_eval v B" by simp
    show ?thesis by (rule disjI2[OF pHc_PC_two[OF member neg b valid]])
  qed
next
  assume members: "A \<in> T \<or> B \<in> T"
  have av: "\<forall>v. pprop_eval v A \<longrightarrow> pprop_eval v (PDisj A B)" by simp
  have bv: "\<forall>v. pprop_eval v B \<longrightarrow> pprop_eval v (PDisj A B)" by simp
  show "PDisj A B \<in> T" using members
  proof
    assume member: "A \<in> T"
    show ?thesis by (rule pHc_PC_one[OF member pHc_language_Disj[OF a b] av])
  next
    assume member: "B \<in> T"
    show ?thesis by (rule pHc_PC_one[OF member pHc_language_Disj[OF a b] bv])
  qed
qed

subsection \<open>Valuation is independent of representatives\<close>

lemma pHc_identity_truth_forward:
  assumes eq: "pH_term_eq Prop A B" and member: "A \<in> T"
  shows "B \<in> T"
proof -
  have body: "has_ptype [Prop] (PVar 0) Prop" by (rule has_ptype.PVar) simp
  have sig: "pterm_in_signature signature (PVar 0)" by simp
  have source: "psubst0 A (PVar 0) \<in> T" using member by (simp only: pH_inst_zero)
  have target: "psubst0 B (PVar 0) \<in> T" by (rule pH_identity_body_transport[OF eq body sig source])
  show ?thesis using target by (simp only: pH_inst_zero)
qed

lemma pHc_identity_truth:
  "pH_term_eq Prop A B \<Longrightarrow> (A \<in> T \<longleftrightarrow> B \<in> T)"
  using pHc_identity_truth_forward pH_term_eq_sym by blast

definition pHc_holds :: "'c pHc_value \<Rightarrow> bool" where
  "pHc_holds v \<longleftrightarrow> fst v = Prop \<and> pHc_rep v \<in> T"

lemma pHc_holds_class:
  assumes lang: "pterm_in_language signature [] A Prop"
  shows "pHc_holds (pHc_class Prop A) \<longleftrightarrow> A \<in> T"
proof -
  have same: "pHc_rep (pHc_class Prop A) \<in> T \<longleftrightarrow> A \<in> T"
    by (rule pHc_identity_truth[OF pHc_rep_class_eq[OF lang]])
  have tag: "fst (pHc_class Prop A) = Prop" by (simp only: pHc_class_def fst_conv)
  show ?thesis by (simp only: pHc_holds_def tag same simp_thms)
qed

lemma pHc_truth_lemma:
  assumes typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g A) \<longleftrightarrow> psubst (\<lambda>n. pHc_rep (g n)) A \<in> T"
  by (simp only: pHc_denote_typed_form[OF typed sig env]
    pHc_holds_class[OF pHc_closed_instance_language[OF typed sig env]])

lemma pHc_truth_representatives:
  assumes typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
    and sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pterm_in_language signature [] (s n) \<rho>"
    and reps: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pHc_class \<rho> (s n) = g n"
  shows "pHc_holds (pHc_denote g A) \<longleftrightarrow> psubst s A \<in> T"
  by (simp only: pHc_denote_representatives[OF typed sig env sub reps]
    pHc_holds_class[OF pHcs_subst_language[OF typed sig sub]])

subsection \<open>Boolean and actual-identity clauses\<close>

lemma pHc_truth_Neg:
  assumes a: "has_ptype \<Gamma> A Prop" and sa: "pterm_in_signature signature A" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PNeg A)) = (\<not> pHc_holds (pHc_denote g A))"
proof -
  have sig: "pterm_in_signature signature (PNeg A)" using sa by simp
  show ?thesis by (simp only: pHc_truth_lemma[OF has_ptype.PNeg[OF a] sig env] pHc_truth_lemma[OF a sa env]
    psubst.simps pHc_member_Neg[OF pHc_closed_instance_language[OF a sa env]])
qed

lemma pHc_truth_Conj:
  assumes a: "has_ptype \<Gamma> A Prop" and b: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PConj A B)) = (pHc_holds (pHc_denote g A) \<and> pHc_holds (pHc_denote g B))"
proof -
  have sig: "pterm_in_signature signature (PConj A B)" using sa sb by simp
  show ?thesis by (simp only: pHc_truth_lemma[OF has_ptype.PConj[OF a b] sig env]
    pHc_truth_lemma[OF a sa env] pHc_truth_lemma[OF b sb env] psubst.simps
    pHc_member_Conj[OF pHc_closed_instance_language[OF a sa env] pHc_closed_instance_language[OF b sb env]])
qed

lemma pHc_truth_Disj:
  assumes a: "has_ptype \<Gamma> A Prop" and b: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PDisj A B)) = (pHc_holds (pHc_denote g A) \<or> pHc_holds (pHc_denote g B))"
proof -
  have sig: "pterm_in_signature signature (PDisj A B)" using sa sb by simp
  show ?thesis by (simp only: pHc_truth_lemma[OF has_ptype.PDisj[OF a b] sig env]
    pHc_truth_lemma[OF a sa env] pHc_truth_lemma[OF b sb env] psubst.simps
    pHc_member_Disj[OF pHc_closed_instance_language[OF a sa env] pHc_closed_instance_language[OF b sb env]])
qed

lemma pHc_truth_Imp:
  assumes a: "has_ptype \<Gamma> A Prop" and b: "has_ptype \<Gamma> B Prop"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PImp A B)) = (pHc_holds (pHc_denote g A) \<longrightarrow> pHc_holds (pHc_denote g B))"
proof -
  have sig: "pterm_in_signature signature (PImp A B)" using sa sb by simp
  show ?thesis by (simp only: pHc_truth_lemma[OF has_ptype.PImp[OF a b] sig env]
    pHc_truth_lemma[OF a sa env] pHc_truth_lemma[OF b sb env] psubst.simps
    pHc_member_Imp[OF pHc_closed_instance_language[OF a sa env] pHc_closed_instance_language[OF b sb env]])
qed

lemma pHc_identity_membership:
  assumes a: "pterm_in_language signature [] A \<sigma>" and b: "pterm_in_language signature [] B \<sigma>"
  shows "PEq \<sigma> A B \<in> T \<longleftrightarrow> pHc_class \<sigma> A = pHc_class \<sigma> B"
  using pHc_class_eq_iff[OF a b] a b unfolding pH_term_eq_def by blast

lemma pHc_truth_Eq:
  assumes a: "has_ptype \<Gamma> A \<sigma>" and b: "has_ptype \<Gamma> B \<sigma>"
    and sa: "pterm_in_signature signature A" and sb: "pterm_in_signature signature B" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PEq \<sigma> A B)) = (pHc_denote g A = pHc_denote g B)"
proof -
  have sig: "pterm_in_signature signature (PEq \<sigma> A B)" using sa sb by simp
  show ?thesis by (simp only: pHc_truth_lemma[OF has_ptype.PEq[OF a b] sig env] psubst.simps
    pHc_denote_typed_form[OF a sa env] pHc_denote_typed_form[OF b sb env]
    pHc_identity_membership[OF pHc_closed_instance_language[OF a sa env] pHc_closed_instance_language[OF b sb env]])
qed

end
end
