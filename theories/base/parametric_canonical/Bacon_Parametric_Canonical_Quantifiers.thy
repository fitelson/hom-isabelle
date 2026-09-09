theory Bacon_Parametric_Canonical_Quantifiers
  imports Bacon_Parametric_Canonical_Truth
begin

section \<open>Quantifiers range over the actual canonical domains\<close>

text \<open>
  M,g ⊨ ∀x:σ.A iff M,g[x↦a] ⊨ A for every a ∈ Dσ, with the
  existential analogue for some a.  Since a is a class [W]ₜ, Henkin
  witnesses turn the syntactic instance condition into quantification over
  actual domain elements.  Source: Bacon–Dorr Definition 3.1(iii.d–e)
  and p.45 n.64; Bacon, Theorem 15.3, pp.320–321.

  The universal converse needs ¬∀x.A → ∃x.¬A.  We derive that H
  theorem first from EG, Gen, and PC.  The later canonical results are
  conditional on pH_closed_Henkin and do not assert model existence.
\<close>

lemma pH_not_forall_exists_neg:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sigA: "pterm_in_signature \<Sigma> A"
  shows "pH_proves \<Sigma> \<Gamma> (PImp (PNeg (PForall \<sigma> A)) (PExists \<sigma> (PNeg A)))"
proof -
  let ?E = "PExists \<sigma> (PNeg A)"
  let ?F = "PForall \<sigma> A"
  let ?B = "prename (lift_ren Suc) (PNeg A)"
  have na: "has_ptype (\<sigma> # \<Gamma>) (PNeg A) Prop" by (rule has_ptype.PNeg[OF body])
  have et: "has_ptype \<Gamma> ?E Prop" by (rule has_ptype.PExists[OF na])
  have ft: "has_ptype \<Gamma> ?F Prop" by (rule has_ptype.PForall[OF body])
  have ne: "has_ptype \<Gamma> (PNeg ?E) Prop" by (rule has_ptype.PNeg[OF et])
  have se: "has_ptype (\<sigma> # \<Gamma>) (pshift ?E) Prop" by (rule pshift_preserves_typing[OF et])
  have shifted_exists: "pshift ?E = PExists \<sigma> ?B" by (simp only: pshift_def prename.simps)
  have bt: "has_ptype (\<sigma> # \<sigma> # \<Gamma>) ?B Prop"
    using se by (auto simp only: shifted_exists elim: has_ptype.cases)
  have zero: "has_ptype (\<sigma> # \<Gamma>) (PVar 0) \<sigma>" by (rule has_ptype.PVar) simp
  have bs: "pterm_in_signature \<Sigma> ?B" using sigA by (simp add: prename_signature)
  have zs: "pterm_in_signature \<Sigma> (PVar 0)" by simp
  have eg: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (psubst0 (PVar 0) ?B) (PExists \<sigma> ?B))"
    by (rule pH_proves.EG[OF bt zero bs zs])
  have eg': "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (PNeg A) (pshift ?E))"
    using eg by (simp only: pH_witness_slot_restore shifted_exists)
  have st: "has_ptype (\<sigma> # \<Gamma>) (pshift (PNeg ?E)) Prop" by (rule pshift_preserves_typing[OF ne])
  have ct: "has_ptype (\<sigma> # \<Gamma>) (PImp (pshift (PNeg ?E)) A) Prop" by (rule has_ptype.PImp[OF st body])
  have cs: "pterm_in_signature \<Sigma> (PImp (pshift (PNeg ?E)) A)" using sigA by (simp add: pshift_def)
  have shift_neg: "pshift (PNeg ?E) = PNeg (pshift ?E)" by (simp only: pshift_def prename.simps)
  have cv: "\<forall>v. pprop_eval v (PImp (PNeg A) (pshift ?E)) \<longrightarrow>
    pprop_eval v (PImp (PNeg A) (pshift ?E)) \<longrightarrow> pprop_eval v (PImp (pshift (PNeg ?E)) A)"
    by (intro allI) (simp only: shift_neg pprop_eval.simps; blast)
  have contraposed: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (pshift (PNeg ?E)) A)"
    by (rule pH_witness_PC_two[OF eg' eg' ct cs cv])
  have nes: "pterm_in_signature \<Sigma> (PNeg ?E)" using sigA by simp
  have generalized: "pH_proves \<Sigma> \<Gamma> (PImp (PNeg ?E) ?F)"
    by (rule pH_proves.Gen[OF ne body nes sigA contraposed])
  have result_type: "has_ptype \<Gamma> (PImp (PNeg ?F) ?E) Prop"
    by (rule has_ptype.PImp[OF has_ptype.PNeg[OF ft] et])
  have result_sig: "pterm_in_signature \<Sigma> (PImp (PNeg ?F) ?E)" using sigA by simp
  have result_valid: "\<forall>v. pprop_eval v (PImp (PNeg ?E) ?F) \<longrightarrow>
    pprop_eval v (PImp (PNeg ?E) ?F) \<longrightarrow> pprop_eval v (PImp (PNeg ?F) ?E)"
    by (intro allI) (simp only: pprop_eval.simps; blast)
  show ?thesis by (rule pH_witness_PC_two[OF generalized generalized result_type result_sig result_valid])
qed

context pH_closed_Henkin
begin

lemma pHc_member_Exists:
  assumes body: "pterm_in_language signature [\<sigma>] A Prop"
  shows "PExists \<sigma> A \<in> T \<longleftrightarrow>
    (\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst0 W A \<in> T)"
proof
  assume member: "PExists \<sigma> A \<in> T"
  have witnessed: "pH_Henkin_witnessed signature [] T"
    using henkin unfolding pH_Henkin_theory_def by (rule conjunct2)
  show "\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst0 W A \<in> T"
    using witnessed body member unfolding pH_Henkin_witnessed_def by blast
next
  assume witnesses: "\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst0 W A \<in> T"
  obtain W where wl: "pterm_in_language signature [] W \<sigma>" and inst: "psubst0 W A \<in> T"
    using witnesses by blast
  have at: "has_ptype [\<sigma>] A Prop" and sa: "pterm_in_signature signature A"
    using body unfolding pterm_in_language_def by simp_all
  have wt: "has_ptype [] W \<sigma>" and sw: "pterm_in_signature signature W"
    using wl unfolding pterm_in_language_def by simp_all
  have eg: "PImp (psubst0 W A) (PExists \<sigma> A) \<in> T"
    by (rule pH_theorem_member[OF pH_proves.EG[OF at wt sa sw]])
  show "PExists \<sigma> A \<in> T" by (rule pH_member_MP[OF inst eg])
qed

lemma pHc_member_Forall:
  assumes body: "pterm_in_language signature [\<sigma>] A Prop"
  shows "PForall \<sigma> A \<in> T \<longleftrightarrow>
    (\<forall>W. pterm_in_language signature [] W \<sigma> \<longrightarrow> psubst0 W A \<in> T)"
proof
  assume member: "PForall \<sigma> A \<in> T"
  show "\<forall>W. pterm_in_language signature [] W \<sigma> \<longrightarrow> psubst0 W A \<in> T"
  proof (intro allI impI)
    fix W
    assume wl: "pterm_in_language signature [] W \<sigma>"
    have at: "has_ptype [\<sigma>] A Prop" and sa: "pterm_in_signature signature A"
      using body unfolding pterm_in_language_def by simp_all
    have wt: "has_ptype [] W \<sigma>" and sw: "pterm_in_signature signature W"
      using wl unfolding pterm_in_language_def by simp_all
    have ui: "PImp (PForall \<sigma> A) (psubst0 W A) \<in> T"
      by (rule pH_theorem_member[OF pH_proves.UI[OF at wt sa sw]])
    show "psubst0 W A \<in> T" by (rule pH_member_MP[OF member ui])
  qed
next
  assume all_instances: "\<forall>W. pterm_in_language signature [] W \<sigma> \<longrightarrow> psubst0 W A \<in> T"
  show "PForall \<sigma> A \<in> T"
  proof (rule ccontr)
    assume absent: "PForall \<sigma> A \<notin> T"
    have at: "has_ptype [\<sigma>] A Prop" and sa: "pterm_in_signature signature A"
      using body unfolding pterm_in_language_def by simp_all
    have ft: "has_ptype [] (PForall \<sigma> A) Prop" by (rule has_ptype.PForall[OF at])
    have fs: "pterm_in_signature signature (PForall \<sigma> A)" using sa by simp
    have fl: "pterm_in_language signature [] (PForall \<sigma> A) Prop"
      unfolding pterm_in_language_def by (rule conjI[OF ft fs])
    have neg: "PNeg (PForall \<sigma> A) \<in> T" by (rule iffD2[OF pHc_member_Neg[OF fl] absent])
    have dual: "PImp (PNeg (PForall \<sigma> A)) (PExists \<sigma> (PNeg A)) \<in> T"
      by (rule pH_theorem_member[OF pH_not_forall_exists_neg[OF at sa]])
    have exists_neg: "PExists \<sigma> (PNeg A) \<in> T" by (rule pH_member_MP[OF neg dual])
    have nt: "has_ptype [\<sigma>] (PNeg A) Prop" by (rule has_ptype.PNeg[OF at])
    have ns: "pterm_in_signature signature (PNeg A)" using sa by simp
    have nl: "pterm_in_language signature [\<sigma>] (PNeg A) Prop"
      unfolding pterm_in_language_def by (rule conjI[OF nt ns])
    obtain W where wl: "pterm_in_language signature [] W \<sigma>" and neg_inst: "psubst0 W (PNeg A) \<in> T"
      using iffD1[OF pHc_member_Exists[OF nl] exists_neg] by blast
    have inst: "psubst0 W A \<in> T" using all_instances wl by blast
    have neg_inst': "PNeg (psubst0 W A) \<in> T" using neg_inst by (simp only: psubst0_def psubst.simps)
    show False by (rule pHc_not_both[OF inst neg_inst'])
  qed
qed

subsection \<open>Representatives for an extended assignment\<close>

lemma pHc_subst0_lift:
  "psubst0 W (psubst (plift_subst s) A) = psubst (case_nat W s) A"
  using pHcs_head_tail[where s="case_nat W s" and M=A] by simp

lemma pHc_binder_data:
  assumes env: "pbbk_env_typed pHc_domain \<Gamma> g" and wl: "pterm_in_language signature [] W \<sigma>"
    and lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
  shows "pterm_in_language signature [] (case_nat W (\<lambda>n. pHc_rep (g n)) n) \<rho> \<and>
    pHc_class \<rho> (case_nat W (\<lambda>n. pHc_rep (g n)) n) = pbbk_extend (pHc_class \<sigma> W) g n"
proof (cases n)
  case 0
  have same: "\<rho> = \<sigma>" using lookup by (simp add: 0)
  show ?thesis using wl by (simp add: 0 same)
next
  case (Suc m)
  have old: "lookup \<Gamma> m = Some \<rho>" using lookup by (simp only: Suc lookup_Cons_Suc)
  have domain: "g m \<in> pHc_domain \<rho>" by (rule pbbk_env_lookup[OF env old])
  have lang: "pterm_in_language signature [] (pHc_rep (g m)) \<rho>" by (rule pHc_rep_language[OF domain])
  have reconstruction: "pHc_class \<rho> (pHc_rep (g m)) = g m" by (rule pHc_rep_reconstruct[OF domain])
  show ?thesis using lang reconstruction by (simp add: Suc)
qed

lemma pHc_binder_truth_class:
  assumes typed: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g" and wl: "pterm_in_language signature [] W \<sigma>"
  shows "pHc_holds (pHc_denote (pbbk_extend (pHc_class \<sigma> W) g) A) \<longleftrightarrow>
    psubst (case_nat W (\<lambda>n. pHc_rep (g n))) A \<in> T"
proof -
  let ?s = "case_nat W (\<lambda>n. pHc_rep (g n))"
  have extended: "pbbk_env_typed pHc_domain (\<sigma> # \<Gamma>) (pbbk_extend (pHc_class \<sigma> W) g)"
    by (rule pbbk_env_extend[OF env pHc_class_in_domain[OF wl]])
  have sub: "pterm_in_language signature [] (?s n) \<rho>"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule conjunct1[OF pHc_binder_data[OF env wl look]])
  have reps: "pHc_class \<rho> (?s n) = pbbk_extend (pHc_class \<sigma> W) g n"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule conjunct2[OF pHc_binder_data[OF env wl look]])
  show ?thesis by (rule pHc_truth_representatives[OF typed sig extended sub reps])
qed

lemma pHc_lifted_body_language:
  assumes typed: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pterm_in_language signature [\<sigma>] (psubst (plift_subst (\<lambda>n. pHc_rep (g n))) A) Prop"
proof -
  let ?s = "\<lambda>n. pHc_rep (g n)"
  have types: "has_ptype [] (?s n) \<rho>" if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    using pHc_env_rep[OF env look] unfolding pterm_in_language_def by (rule conjunct1)
  have sigs: "pterm_in_signature signature (?s n)" if look: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    using pHc_env_rep[OF env look] unfolding pterm_in_language_def by (rule conjunct2)
  have lifted_types: "has_ptype [\<sigma>] (plift_subst ?s n) \<rho>"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule plift_subst_preserves_typing[OF types look])
  have lifted_sigs: "pterm_in_signature signature (plift_subst ?s n)"
    if look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>" for n \<rho>
    by (rule pHcs_lift_signature[OF sigs look])
  have result_type: "has_ptype [\<sigma>] (psubst (plift_subst ?s) A) Prop"
    by (rule psubst_preserves_typing[OF typed lifted_types])
  have result_sig: "pterm_in_signature signature (psubst (plift_subst ?s) A)"
    by (rule pHcs_subst_signature[OF typed sig lifted_sigs])
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF result_type result_sig])
qed

lemma pHc_domain_all:
  "(\<forall>v \<in> pHc_domain \<sigma>. P v) \<longleftrightarrow>
    (\<forall>W. pterm_in_language signature [] W \<sigma> \<longrightarrow> P (pHc_class \<sigma> W))"
  unfolding pHc_domain_def by blast

lemma pHc_domain_some:
  "(\<exists>v \<in> pHc_domain \<sigma>. P v) \<longleftrightarrow>
    (\<exists>W. pterm_in_language signature [] W \<sigma> \<and> P (pHc_class \<sigma> W))"
  unfolding pHc_domain_def by blast

subsection \<open>Canonical truth clauses over Dσ\<close>

lemma pHc_truth_Forall:
  assumes typed: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PForall \<sigma> A)) =
    (\<forall>v \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend v g) A))"
proof -
  let ?s = "\<lambda>n. pHc_rep (g n)"
  have qt: "has_ptype \<Gamma> (PForall \<sigma> A) Prop" by (rule has_ptype.PForall[OF typed])
  have qs: "pterm_in_signature signature (PForall \<sigma> A)" using sig by simp
  have body: "pterm_in_language signature [\<sigma>] (psubst (plift_subst ?s) A) Prop"
    by (rule pHc_lifted_body_language[OF typed sig env])
  have terms: "pHc_holds (pHc_denote g (PForall \<sigma> A)) \<longleftrightarrow>
      (\<forall>W. pterm_in_language signature [] W \<sigma> \<longrightarrow> psubst (case_nat W ?s) A \<in> T)"
    by (simp only: pHc_truth_lemma[OF qt qs env] psubst.simps pHc_member_Forall[OF body] pHc_subst0_lift)
  have instances: "pHc_holds (pHc_denote (pbbk_extend (pHc_class \<sigma> W) g) A) \<longleftrightarrow>
      psubst (case_nat W ?s) A \<in> T" if wl: "pterm_in_language signature [] W \<sigma>" for W
    by (rule pHc_binder_truth_class[OF typed sig env wl])
  show ?thesis using terms instances pHc_domain_all[where \<sigma>=\<sigma>
    and P="\<lambda>v. pHc_holds (pHc_denote (pbbk_extend v g) A)"] by blast
qed

lemma pHc_truth_Exists:
  assumes typed: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_holds (pHc_denote g (PExists \<sigma> A)) =
    (\<exists>v \<in> pHc_domain \<sigma>. pHc_holds (pHc_denote (pbbk_extend v g) A))"
proof -
  let ?s = "\<lambda>n. pHc_rep (g n)"
  have qt: "has_ptype \<Gamma> (PExists \<sigma> A) Prop" by (rule has_ptype.PExists[OF typed])
  have qs: "pterm_in_signature signature (PExists \<sigma> A)" using sig by simp
  have body: "pterm_in_language signature [\<sigma>] (psubst (plift_subst ?s) A) Prop"
    by (rule pHc_lifted_body_language[OF typed sig env])
  have terms: "pHc_holds (pHc_denote g (PExists \<sigma> A)) \<longleftrightarrow>
      (\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst (case_nat W ?s) A \<in> T)"
    by (simp only: pHc_truth_lemma[OF qt qs env] psubst.simps pHc_member_Exists[OF body] pHc_subst0_lift)
  have instances: "pHc_holds (pHc_denote (pbbk_extend (pHc_class \<sigma> W) g) A) \<longleftrightarrow>
      psubst (case_nat W ?s) A \<in> T" if wl: "pterm_in_language signature [] W \<sigma>" for W
    by (rule pHc_binder_truth_class[OF typed sig env wl])
  show ?thesis using terms instances pHc_domain_some[where \<sigma>=\<sigma>
    and P="\<lambda>v. pHc_holds (pHc_denote (pbbk_extend v g) A)"] by blast
qed

end
end
