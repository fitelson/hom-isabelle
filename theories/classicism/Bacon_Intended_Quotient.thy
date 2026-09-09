theory Bacon_Intended_Quotient
  imports Bacon_Clean_Completeness
begin

section \<open>The local term quotient at a clean CEV Henkin world\<close>

text \<open>
  Bacon--Dorr completeness uses a category of models rather than a single
  extensional model.  At each object of the canonical category, terms are
  quotiented by the identities true at that object's Henkin world.  Arrows
  between these local quotients are a separate construction.

  Conventionally, write M \<open>\<sim>\<close> N at type \<open>\<sigma>\<close> and world \<open>T\<close>
  when the identity M = N belongs to \<open>T\<close>.  The class [M] is represented
  here by a set of equivalent typed terms, rather than by an Isabelle
  quotient type.  Application sends ([F], [A]) to [FA], and propositional
  truth of [A] means membership of A in T.  A typed substitution s induces
  the map [M] to [M[s]] only when it preserves the source identity diagram.

  Source: Bacon--Dorr, footnote 64 (p. 45) and Section 3.3 (pp. 49--52);
  compare Bacon's modal term structure, Definition 18.9 (p. 399).
  The present quotient and map lemmas are ingredients, not the complete
  interpretation or profile representation required for an action model.
  The unrestricted fresh-reserve endpoints at the end are historical:
  their hypotheses are shown to be impossible in \<open>Bacon_Supported_Canonical\<close>,
  which supplies the supported-language repair.
\<close>

definition CEV_local_term_equiv ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_local_term_equiv \<Gamma> T \<sigma> M N \<longleftrightarrow>
    \<Gamma> \<turnstile> M : \<sigma> \<and> \<Gamma> \<turnstile> N : \<sigma> \<and> Eq \<sigma> M N \<in> T"

definition CEV_local_term_class ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm set" where
  "CEV_local_term_class \<Gamma> T \<sigma> M =
    {N. CEV_local_term_equiv \<Gamma> T \<sigma> M N}"

definition CEV_local_domain ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> oterm set set" where
  "CEV_local_domain \<Gamma> T \<sigma> =
    {CEV_local_term_class \<Gamma> T \<sigma> M | M. \<Gamma> \<turnstile> M : \<sigma>}"

lemma CEV_clean_Henkin_local:
  assumes "CEV_clean_Henkin_theory \<Gamma> T"
  shows "CEV_locally_maximal_consistent \<Gamma> T"
  using assms unfolding CEV_clean_Henkin_theory_def by blast

lemma CEV_clean_Henkin_contains_theorems:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and proves: "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "A \<in> T"
  using CEV_clean_Henkin_local[OF henkin] proves
  by (rule CEV_locally_maximal_consistent_contains_theorems)

lemma CEV_clean_Henkin_closed_under_set_derivable:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and derivable: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "A \<in> T"
  using CEV_clean_Henkin_local[OF henkin] derivable
  by (rule CEV_locally_maximal_consistent_deductively_closed)

lemma CEV_local_term_equiv_refl:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "CEV_local_term_equiv \<Gamma> T \<sigma> M M"
proof -
  have ref: "\<Gamma> \<turnstile>\<^sub>CEV Eq \<sigma> M M"
    using M_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
  have "Eq \<sigma> M M \<in> T"
    using henkin ref by (rule CEV_clean_Henkin_contains_theorems)
  then show ?thesis
    unfolding CEV_local_term_equiv_def using M_type by blast
qed

lemma CEV_local_term_equiv_sym:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and MN: "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
  shows "CEV_local_term_equiv \<Gamma> T \<sigma> N M"
proof -
  have M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and eq_in: "Eq \<sigma> M N \<in> T"
    using MN unfolding CEV_local_term_equiv_def by auto
  have d_eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> M N"
    using eq_in M_type N_type by (intro CEV_set_derivable.Assumption) auto
  have sym_imp: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
    using M_type N_type by (rule CEV_eq_sym)
  have d_sym_imp:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
    using sym_imp by (rule CEV_set_derivable.Theorem)
  have d_sym: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> N M"
    using d_eq d_sym_imp by (rule CEV_set_derivable.Derive_MP)
  have "Eq \<sigma> N M \<in> T"
    using henkin d_sym by (rule CEV_clean_Henkin_closed_under_set_derivable)
  then show ?thesis
    unfolding CEV_local_term_equiv_def using M_type N_type by blast
qed

lemma CEV_local_term_equiv_trans:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and MN: "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
    and NP: "CEV_local_term_equiv \<Gamma> T \<sigma> N P"
  shows "CEV_local_term_equiv \<Gamma> T \<sigma> M P"
proof -
  have M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and P_type: "\<Gamma> \<turnstile> P : \<sigma>"
    and MN_in: "Eq \<sigma> M N \<in> T"
    and NP_in: "Eq \<sigma> N P \<in> T"
    using MN NP unfolding CEV_local_term_equiv_def by auto
  have d_MN: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> M N"
    using MN_in M_type N_type by (intro CEV_set_derivable.Assumption) auto
  have d_NP: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> N P"
    using NP_in N_type P_type by (intro CEV_set_derivable.Assumption) auto
  have trans_imp:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
    using M_type N_type P_type by (rule CEV_eq_trans)
  have d_trans_imp:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
    using trans_imp by (rule CEV_set_derivable.Theorem)
  have d_step:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Eq \<sigma> N P) (Eq \<sigma> M P)"
    using d_MN d_trans_imp by (rule CEV_set_derivable.Derive_MP)
  have d_MP: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> M P"
    using d_NP d_step by (rule CEV_set_derivable.Derive_MP)
  have "Eq \<sigma> M P \<in> T"
    using henkin d_MP by (rule CEV_clean_Henkin_closed_under_set_derivable)
  then show ?thesis
    unfolding CEV_local_term_equiv_def using M_type P_type by blast
qed

lemma CEV_clean_Henkin_identity_subst_in:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and eq_in: "Eq \<sigma> M N \<in> T"
    and app_in: "App F M \<in> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "App F N \<in> T"
proof -
  have eq_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using M_type N_type by auto
  have app_M_type: "\<Gamma> \<turnstile> App F M : Prop"
    using F_type M_type by auto
  have d_eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> M N"
    using eq_in eq_type by (rule CEV_set_derivable.Assumption)
  have d_app: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s App F M"
    using app_in app_M_type by (rule CEV_set_derivable.Assumption)
  have ll:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using M_type N_type F_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have d_ll:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Eq \<sigma> M N) (Imp (App F M) (App F N))"
    using ll by (rule CEV_set_derivable.Theorem)
  have d_step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (App F M) (App F N)"
    using d_eq d_ll by (rule CEV_set_derivable.Derive_MP)
  have d_result: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s App F N"
    using d_app d_step by (rule CEV_set_derivable.Derive_MP)
  show "App F N \<in> T"
    using henkin d_result by (rule CEV_clean_Henkin_closed_under_set_derivable)
qed

lemma CEV_clean_Henkin_beta_step_mem_iff:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step beta_contract A B"
  shows "A \<in> T \<longleftrightarrow> B \<in> T"
proof -
  have bicond: "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
    using A_type B_type step by (rule CEV_beta_step)
  have d_bicond: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s (A \<longleftrightarrow>\<^sub>o B)"
    using bicond by (rule CEV_set_derivable.Theorem)
  have AB_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using A_type B_type by auto
  have BA_type: "\<Gamma> \<turnstile> Imp B A : Prop"
    using A_type B_type by auto
  have left:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B)"
    using AB_type BA_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_left)
  have right:
      "\<Gamma> \<turnstile>\<^sub>CEV Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A)"
    using AB_type BA_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_right)
  have d_left:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B)"
    using left by (rule CEV_set_derivable.Theorem)
  have d_right:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A)"
    using right by (rule CEV_set_derivable.Theorem)
  have d_AB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A B"
    using d_bicond d_left by (rule CEV_set_derivable.Derive_MP)
  have d_BA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp B A"
    using d_bicond d_right by (rule CEV_set_derivable.Derive_MP)
  show ?thesis
  proof
    assume A_in: "A \<in> T"
    have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
      using A_in A_type by (rule CEV_set_derivable.Assumption)
    have d_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"
      using d_A d_AB by (rule CEV_set_derivable.Derive_MP)
    show "B \<in> T"
      using henkin d_B by (rule CEV_clean_Henkin_closed_under_set_derivable)
  next
    assume B_in: "B \<in> T"
    have d_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"
      using B_in B_type by (rule CEV_set_derivable.Assumption)
    have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
      using d_B d_BA by (rule CEV_set_derivable.Derive_MP)
    show "A \<in> T"
      using henkin d_A by (rule CEV_clean_Henkin_closed_under_set_derivable)
  qed
qed

lemma CEV_local_term_equiv_app_right:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and AB: "CEV_local_term_equiv \<Gamma> T \<sigma> A B"
  shows "CEV_local_term_equiv \<Gamma> T \<tau> (App F A) (App F B)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and AB_in: "Eq \<sigma> A B \<in> T"
    using AB unfolding CEV_local_term_equiv_def by auto
  let ?FA = "App F A"
  let ?FB = "App F B"
  let ?EAA = "Eq \<tau> ?FA ?FA"
  let ?EAB = "Eq \<tau> ?FA ?FB"
  let ?P =
    "Lam \<sigma> (Eq \<tau> (shift ?FA) (App (shift F) (Var 0)))"
  have FA_type: "\<Gamma> \<turnstile> ?FA : \<tau>"
    using F_type A_type by auto
  have FB_type: "\<Gamma> \<turnstile> ?FB : \<tau>"
    using F_type B_type by auto
  have EAA_type: "\<Gamma> \<turnstile> ?EAA : Prop"
    using FA_type by auto
  have EAB_type: "\<Gamma> \<turnstile> ?EAB : Prop"
    using FA_type FB_type by auto
  have shift_FA_type: "\<sigma> # \<Gamma> \<turnstile> shift ?FA : \<tau>"
    using FA_type by (rule weakening_front)
  have shift_F_type: "\<sigma> # \<Gamma> \<turnstile> shift F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F_type by (rule weakening_front)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have app_shift_type:
      "\<sigma> # \<Gamma> \<turnstile> App (shift F) (Var 0) : \<tau>"
    using shift_F_type var_type by (rule has_type.App)
  have body_type:
      "\<sigma> # \<Gamma> \<turnstile>
        Eq \<tau> (shift ?FA) (App (shift F) (Var 0)) : Prop"
    using shift_FA_type app_shift_type by (rule has_type.Eq)
  have P_type: "\<Gamma> \<turnstile> ?P : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_P_A_type: "\<Gamma> \<turnstile> App ?P A : Prop"
    using P_type A_type by auto
  have app_P_B_type: "\<Gamma> \<turnstile> App ?P B : Prop"
    using P_type B_type by auto
  have EAA_in: "?EAA \<in> T"
  proof -
    have ref: "\<Gamma> \<turnstile>\<^sub>CEV ?EAA"
      using FA_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
    show ?thesis
      using CEV_clean_Henkin_contains_theorems[OF henkin ref] .
  qed
  have beta_A: "compatible_step beta_contract (App ?P A) ?EAA"
  proof -
    have "compatible_step beta_contract (App ?P A)
        (subst0 A (Eq \<tau> (shift ?FA) (App (shift F) (Var 0))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have app_P_A_in: "App ?P A \<in> T"
    using CEV_clean_Henkin_beta_step_mem_iff[
      OF henkin app_P_A_type EAA_type beta_A] EAA_in by blast
  have app_P_B_in: "App ?P B \<in> T"
    using henkin AB_in app_P_A_in A_type B_type P_type
    by (rule CEV_clean_Henkin_identity_subst_in)
  have beta_B: "compatible_step beta_contract (App ?P B) ?EAB"
  proof -
    have "compatible_step beta_contract (App ?P B)
        (subst0 B (Eq \<tau> (shift ?FA) (App (shift F) (Var 0))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have EAB_in: "?EAB \<in> T"
    using CEV_clean_Henkin_beta_step_mem_iff[
      OF henkin app_P_B_type EAB_type beta_B] app_P_B_in by blast
  show ?thesis
    unfolding CEV_local_term_equiv_def using FA_type FB_type EAB_in by blast
qed

lemma CEV_local_term_equiv_app_left:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and FG: "CEV_local_term_equiv \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
  shows "CEV_local_term_equiv \<Gamma> T \<tau> (App F A) (App G A)"
proof -
  have F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and G_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and FG_in: "Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G \<in> T"
    using FG unfolding CEV_local_term_equiv_def by auto
  let ?FA = "App F A"
  let ?GA = "App G A"
  let ?EAA = "Eq \<tau> ?FA ?FA"
  let ?EAG = "Eq \<tau> ?FA ?GA"
  let ?P =
    "Lam (\<sigma> \<rightarrow>\<^sub>o \<tau>)
      (Eq \<tau> (shift ?FA) (App (Var 0) (shift A)))"
  have FA_type: "\<Gamma> \<turnstile> ?FA : \<tau>"
    using F_type A_type by auto
  have GA_type: "\<Gamma> \<turnstile> ?GA : \<tau>"
    using G_type A_type by auto
  have EAA_type: "\<Gamma> \<turnstile> ?EAA : Prop"
    using FA_type by auto
  have EAG_type: "\<Gamma> \<turnstile> ?EAG : Prop"
    using FA_type GA_type by auto
  have shift_FA_type:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> shift ?FA : \<tau>"
    using FA_type by (rule weakening_front)
  have shift_A_type:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> shift A : \<sigma>"
    using A_type by (rule weakening_front)
  have var_type:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Var 0 : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    by simp
  have app_var_type:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile>
        App (Var 0) (shift A) : \<tau>"
    using var_type shift_A_type by (rule has_type.App)
  have body_type:
      "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile>
        Eq \<tau> (shift ?FA) (App (Var 0) (shift A)) : Prop"
    using shift_FA_type app_var_type by (rule has_type.Eq)
  have P_type: "\<Gamma> \<turnstile> ?P : (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_P_F_type: "\<Gamma> \<turnstile> App ?P F : Prop"
    using P_type F_type by auto
  have app_P_G_type: "\<Gamma> \<turnstile> App ?P G : Prop"
    using P_type G_type by auto
  have EAA_in: "?EAA \<in> T"
  proof -
    have ref: "\<Gamma> \<turnstile>\<^sub>CEV ?EAA"
      using FA_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
    show ?thesis
      using CEV_clean_Henkin_contains_theorems[OF henkin ref] .
  qed
  have beta_F: "compatible_step beta_contract (App ?P F) ?EAA"
  proof -
    have "compatible_step beta_contract (App ?P F)
        (subst0 F (Eq \<tau> (shift ?FA) (App (Var 0) (shift A))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have app_P_F_in: "App ?P F \<in> T"
    using CEV_clean_Henkin_beta_step_mem_iff[
      OF henkin app_P_F_type EAA_type beta_F] EAA_in by blast
  have app_P_G_in: "App ?P G \<in> T"
    using henkin FG_in app_P_F_in F_type G_type P_type
    by (rule CEV_clean_Henkin_identity_subst_in)
  have beta_G: "compatible_step beta_contract (App ?P G) ?EAG"
  proof -
    have "compatible_step beta_contract (App ?P G)
        (subst0 G (Eq \<tau> (shift ?FA) (App (Var 0) (shift A))))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: subst0_def)
  qed
  have EAG_in: "?EAG \<in> T"
    using CEV_clean_Henkin_beta_step_mem_iff[
      OF henkin app_P_G_type EAG_type beta_G] app_P_G_in by blast
  show ?thesis
    unfolding CEV_local_term_equiv_def using FA_type GA_type EAG_in by blast
qed

lemma CEV_local_term_equiv_app:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and FG: "CEV_local_term_equiv \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
    and AB: "CEV_local_term_equiv \<Gamma> T \<sigma> A B"
  shows "CEV_local_term_equiv \<Gamma> T \<tau> (App F A) (App G B)"
proof -
  have F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    using FG AB unfolding CEV_local_term_equiv_def by auto
  have right:
      "CEV_local_term_equiv \<Gamma> T \<tau> (App F A) (App F B)"
    using henkin F_type AB by (rule CEV_local_term_equiv_app_right)
  have left:
      "CEV_local_term_equiv \<Gamma> T \<tau> (App F B) (App G B)"
    using henkin FG B_type by (rule CEV_local_term_equiv_app_left)
  show ?thesis
    using henkin right left by (rule CEV_local_term_equiv_trans)
qed

lemma CEV_local_term_class_self:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "M \<in> CEV_local_term_class \<Gamma> T \<sigma> M"
  using CEV_local_term_equiv_refl[OF assms]
  unfolding CEV_local_term_class_def by blast

lemma CEV_local_term_class_eq:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
  shows "CEV_local_term_class \<Gamma> T \<sigma> M =
      CEV_local_term_class \<Gamma> T \<sigma> N
    \<longleftrightarrow> CEV_local_term_equiv \<Gamma> T \<sigma> M N"
proof
  assume classes:
      "CEV_local_term_class \<Gamma> T \<sigma> M =
        CEV_local_term_class \<Gamma> T \<sigma> N"
  have "M \<in> CEV_local_term_class \<Gamma> T \<sigma> N"
    using CEV_local_term_class_self[OF henkin M_type] classes by simp
  then have NM: "CEV_local_term_equiv \<Gamma> T \<sigma> N M"
    unfolding CEV_local_term_class_def by blast
  show "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
    using henkin NM by (rule CEV_local_term_equiv_sym)
next
  assume MN: "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
  show "CEV_local_term_class \<Gamma> T \<sigma> M =
      CEV_local_term_class \<Gamma> T \<sigma> N"
  proof (rule set_eqI)
    fix P
    show "P \<in> CEV_local_term_class \<Gamma> T \<sigma> M \<longleftrightarrow>
        P \<in> CEV_local_term_class \<Gamma> T \<sigma> N"
    proof
      assume P_in: "P \<in> CEV_local_term_class \<Gamma> T \<sigma> M"
      have MP: "CEV_local_term_equiv \<Gamma> T \<sigma> M P"
        using P_in unfolding CEV_local_term_class_def by blast
      have NM: "CEV_local_term_equiv \<Gamma> T \<sigma> N M"
        using henkin MN by (rule CEV_local_term_equiv_sym)
      have NP: "CEV_local_term_equiv \<Gamma> T \<sigma> N P"
        using henkin NM MP by (rule CEV_local_term_equiv_trans)
      then show "P \<in> CEV_local_term_class \<Gamma> T \<sigma> N"
        unfolding CEV_local_term_class_def by blast
    next
      assume P_in: "P \<in> CEV_local_term_class \<Gamma> T \<sigma> N"
      have NP: "CEV_local_term_equiv \<Gamma> T \<sigma> N P"
        using P_in unfolding CEV_local_term_class_def by blast
      have MP: "CEV_local_term_equiv \<Gamma> T \<sigma> M P"
        using henkin MN NP by (rule CEV_local_term_equiv_trans)
      then show "P \<in> CEV_local_term_class \<Gamma> T \<sigma> M"
        unfolding CEV_local_term_class_def by blast
    qed
  qed
qed

lemma CEV_local_domainI:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "CEV_local_term_class \<Gamma> T \<sigma> M \<in> CEV_local_domain \<Gamma> T \<sigma>"
  using assms unfolding CEV_local_domain_def by blast

section \<open>Application on quotient classes\<close>

definition CEV_local_app_rel ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow>
      oterm set \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_local_app_rel \<Gamma> T \<sigma> \<tau> X Y Z \<longleftrightarrow>
    (\<exists>F A. \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<and>
      \<Gamma> \<turnstile> A : \<sigma> \<and>
      X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F \<and>
      Y = CEV_local_term_class \<Gamma> T \<sigma> A \<and>
      Z = CEV_local_term_class \<Gamma> T \<tau> (App F A))"

lemma CEV_local_app_rel_exists:
  assumes X_dom: "X \<in> CEV_local_domain \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and Y_dom: "Y \<in> CEV_local_domain \<Gamma> T \<sigma>"
  shows "\<exists>Z. CEV_local_app_rel \<Gamma> T \<sigma> \<tau> X Y Z"
proof -
  obtain F where F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_def:
      "X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    using X_dom unfolding CEV_local_domain_def by blast
  obtain A where A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and Y_def: "Y = CEV_local_term_class \<Gamma> T \<sigma> A"
    using Y_dom unfolding CEV_local_domain_def by blast
  show ?thesis
    unfolding CEV_local_app_rel_def
    using F_type A_type X_def Y_def by blast
qed

lemma CEV_local_app_rel_unique:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and rel_Z: "CEV_local_app_rel \<Gamma> T \<sigma> \<tau> X Y Z"
    and rel_W: "CEV_local_app_rel \<Gamma> T \<sigma> \<tau> X Y W"
  shows "Z = W"
proof -
  obtain F A where F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and X_F:
      "X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    and Y_A: "Y = CEV_local_term_class \<Gamma> T \<sigma> A"
    and Z_def: "Z = CEV_local_term_class \<Gamma> T \<tau> (App F A)"
    using rel_Z unfolding CEV_local_app_rel_def by blast
  obtain G B where G_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and X_G:
      "X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) G"
    and Y_B: "Y = CEV_local_term_class \<Gamma> T \<sigma> B"
    and W_def: "W = CEV_local_term_class \<Gamma> T \<tau> (App G B)"
    using rel_W unfolding CEV_local_app_rel_def by blast
  have classes_FG:
      "CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F =
        CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) G"
    using X_F X_G by simp
  have FG:
      "CEV_local_term_equiv \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
    using CEV_local_term_class_eq[
      OF henkin F_type G_type] classes_FG by blast
  have classes_AB:
      "CEV_local_term_class \<Gamma> T \<sigma> A =
        CEV_local_term_class \<Gamma> T \<sigma> B"
    using Y_A Y_B by simp
  have AB: "CEV_local_term_equiv \<Gamma> T \<sigma> A B"
    using CEV_local_term_class_eq[
      OF henkin A_type B_type] classes_AB by blast
  have app_equiv:
      "CEV_local_term_equiv \<Gamma> T \<tau> (App F A) (App G B)"
    using henkin FG AB by (rule CEV_local_term_equiv_app)
  have app_F_type: "\<Gamma> \<turnstile> App F A : \<tau>"
    using F_type A_type by auto
  have app_G_type: "\<Gamma> \<turnstile> App G B : \<tau>"
    using G_type B_type by auto
  have classes_app:
      "CEV_local_term_class \<Gamma> T \<tau> (App F A) =
        CEV_local_term_class \<Gamma> T \<tau> (App G B)"
    using CEV_local_term_class_eq[
      OF henkin app_F_type app_G_type] app_equiv by blast
  show "Z = W"
    using Z_def W_def classes_app by simp
qed

definition CEV_local_app ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow>
      oterm set \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_local_app \<Gamma> T \<sigma> \<tau> X Y =
    (THE Z. CEV_local_app_rel \<Gamma> T \<sigma> \<tau> X Y Z)"

lemma CEV_local_app_class:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
  shows "CEV_local_app \<Gamma> T \<sigma> \<tau>
      (CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
      (CEV_local_term_class \<Gamma> T \<sigma> A) =
    CEV_local_term_class \<Gamma> T \<tau> (App F A)"
proof -
  let ?X = "CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
  let ?Y = "CEV_local_term_class \<Gamma> T \<sigma> A"
  let ?Z = "CEV_local_term_class \<Gamma> T \<tau> (App F A)"
  have rel: "CEV_local_app_rel \<Gamma> T \<sigma> \<tau> ?X ?Y ?Z"
    unfolding CEV_local_app_rel_def using F_type A_type by blast
  have unique: "\<And>W. CEV_local_app_rel \<Gamma> T \<sigma> \<tau> ?X ?Y W
      \<Longrightarrow> W = ?Z"
  proof -
    fix W
    assume rel_W: "CEV_local_app_rel \<Gamma> T \<sigma> \<tau> ?X ?Y W"
    have "?Z = W"
      using henkin rel rel_W by (rule CEV_local_app_rel_unique)
    then show "W = ?Z"
      by simp
  qed
  show ?thesis
    unfolding CEV_local_app_def
    using rel unique by (rule the_equality)
qed

lemma CEV_local_app_closed:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and X_dom: "X \<in> CEV_local_domain \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and Y_dom: "Y \<in> CEV_local_domain \<Gamma> T \<sigma>"
  shows "CEV_local_app \<Gamma> T \<sigma> \<tau> X Y
    \<in> CEV_local_domain \<Gamma> T \<tau>"
proof -
  obtain F where F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and X_def:
      "X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    using X_dom unfolding CEV_local_domain_def by blast
  obtain A where A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and Y_def: "Y = CEV_local_term_class \<Gamma> T \<sigma> A"
    using Y_dom unfolding CEV_local_domain_def by blast
  have app_type: "\<Gamma> \<turnstile> App F A : \<tau>"
    using F_type A_type by auto
  have app_eq:
      "CEV_local_app \<Gamma> T \<sigma> \<tau> X Y =
        CEV_local_term_class \<Gamma> T \<tau> (App F A)"
    unfolding X_def Y_def
    using henkin F_type A_type by (rule CEV_local_app_class)
  show ?thesis
    unfolding app_eq using app_type by (rule CEV_local_domainI)
qed

section \<open>Diagram-preserving substitution arrows\<close>

definition CEV_quotient_arrow ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow>
      oterm env \<Rightarrow> bool" where
  "CEV_quotient_arrow \<Delta> S \<Gamma> T s \<longleftrightarrow>
    CEV_clean_Henkin_theory \<Delta> S \<and>
    CEV_clean_Henkin_theory \<Gamma> T \<and>
    term_subst_typed \<Delta> \<Gamma> s \<and>
    (\<forall>\<sigma> M N. \<Delta> \<turnstile> M : \<sigma> \<longrightarrow> \<Delta> \<turnstile> N : \<sigma> \<longrightarrow>
      Eq \<sigma> M N \<in> S \<longrightarrow>
      Eq \<sigma> (subst s M) (subst s N) \<in> T)"

lemma CEV_quotient_arrow_source:
  assumes "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
  shows "CEV_clean_Henkin_theory \<Delta> S"
  using assms unfolding CEV_quotient_arrow_def by blast

lemma CEV_quotient_arrow_target:
  assumes "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
  shows "CEV_clean_Henkin_theory \<Gamma> T"
  using assms unfolding CEV_quotient_arrow_def by blast

lemma CEV_quotient_arrow_typed:
  assumes "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
  shows "term_subst_typed \<Delta> \<Gamma> s"
  using assms unfolding CEV_quotient_arrow_def by blast

lemma CEV_quotient_arrow_preserves_equiv:
  assumes arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and MN: "CEV_local_term_equiv \<Delta> S \<sigma> M N"
  shows "CEV_local_term_equiv \<Gamma> T \<sigma> (subst s M) (subst s N)"
proof -
  have M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and eq_in: "Eq \<sigma> M N \<in> S"
    using MN unfolding CEV_local_term_equiv_def by auto
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_quotient_arrow_typed)
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have eq_sub_in: "Eq \<sigma> (subst s M) (subst s N) \<in> T"
    using arrow M_type N_type eq_in
    unfolding CEV_quotient_arrow_def by blast
  show ?thesis
    unfolding CEV_local_term_equiv_def
    using sub_M_type sub_N_type eq_sub_in by blast
qed

lemma CEV_quotient_arrow_id:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
  shows "CEV_quotient_arrow \<Gamma> T \<Gamma> T Var"
  unfolding CEV_quotient_arrow_def
  using henkin term_subst_typed_Var by simp

lemma term_subst_typed_comp:
  assumes s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    and t_typed: "term_subst_typed \<Gamma> \<Lambda> t"
  shows "term_subst_typed \<Delta> \<Lambda> (\<lambda>n. subst t (s n))"
proof (unfold term_subst_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Delta> n = Some \<sigma>"
  have "\<Gamma> \<turnstile> s n : \<sigma>"
    using s_typed lookup by (rule term_subst_typedD)
  then show "\<Lambda> \<turnstile> subst t (s n) : \<sigma>"
    using t_typed by (rule term_subst_preserves_typing)
qed

lemma CEV_quotient_arrow_comp:
  assumes s_arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and t_arrow: "CEV_quotient_arrow \<Gamma> T \<Lambda> U t"
  shows "CEV_quotient_arrow \<Delta> S \<Lambda> U (\<lambda>n. subst t (s n))"
proof -
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using s_arrow by (rule CEV_quotient_arrow_source)
  have middle_s: "CEV_clean_Henkin_theory \<Gamma> T"
    using s_arrow by (rule CEV_quotient_arrow_target)
  have middle_t: "CEV_clean_Henkin_theory \<Gamma> T"
    using t_arrow by (rule CEV_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Lambda> U"
    using t_arrow by (rule CEV_quotient_arrow_target)
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using s_arrow by (rule CEV_quotient_arrow_typed)
  have t_typed: "term_subst_typed \<Gamma> \<Lambda> t"
    using t_arrow by (rule CEV_quotient_arrow_typed)
  have comp_typed: "term_subst_typed \<Delta> \<Lambda> (\<lambda>n. subst t (s n))"
    using s_typed t_typed by (rule term_subst_typed_comp)
  have preserves:
      "\<And>\<sigma> M N. \<Delta> \<turnstile> M : \<sigma> \<Longrightarrow> \<Delta> \<turnstile> N : \<sigma> \<Longrightarrow>
        Eq \<sigma> M N \<in> S \<Longrightarrow>
        Eq \<sigma> (subst (\<lambda>n. subst t (s n)) M)
          (subst (\<lambda>n. subst t (s n)) N) \<in> U"
  proof -
    fix \<sigma> M N
    assume M_type: "\<Delta> \<turnstile> M : \<sigma>"
      and N_type: "\<Delta> \<turnstile> N : \<sigma>"
      and eq_in: "Eq \<sigma> M N \<in> S"
    have eq_s_in: "Eq \<sigma> (subst s M) (subst s N) \<in> T"
      using s_arrow M_type N_type eq_in
      unfolding CEV_quotient_arrow_def by blast
    have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
      using M_type s_typed by (rule term_subst_preserves_typing)
    have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
      using N_type s_typed by (rule term_subst_preserves_typing)
    have eq_t_in:
        "Eq \<sigma> (subst t (subst s M)) (subst t (subst s N)) \<in> U"
      using t_arrow sub_M_type sub_N_type eq_s_in
      unfolding CEV_quotient_arrow_def by blast
    show "Eq \<sigma> (subst (\<lambda>n. subst t (s n)) M)
        (subst (\<lambda>n. subst t (s n)) N) \<in> U"
      using eq_t_in by (simp add: subst_comp)
  qed
  show ?thesis
    unfolding CEV_quotient_arrow_def
    using source target comp_typed preserves by blast
qed

definition CEV_quotient_map_rel ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow>
      oterm env \<Rightarrow> otype \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> X Y \<longleftrightarrow>
    (\<exists>M. \<Delta> \<turnstile> M : \<sigma> \<and>
      X = CEV_local_term_class \<Delta> S \<sigma> M \<and>
      Y = CEV_local_term_class \<Gamma> T \<sigma> (subst s M))"

lemma CEV_quotient_map_rel_exists:
  assumes X_dom: "X \<in> CEV_local_domain \<Delta> S \<sigma>"
  shows "\<exists>Y. CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> X Y"
  using X_dom
  unfolding CEV_local_domain_def CEV_quotient_map_rel_def by blast

lemma CEV_quotient_map_rel_unique:
  assumes arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and rel_Y: "CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> X Y"
    and rel_Z: "CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> X Z"
  shows "Y = Z"
proof -
  obtain M where M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and X_M: "X = CEV_local_term_class \<Delta> S \<sigma> M"
    and Y_def: "Y = CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
    using rel_Y unfolding CEV_quotient_map_rel_def by blast
  obtain N where N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and X_N: "X = CEV_local_term_class \<Delta> S \<sigma> N"
    and Z_def: "Z = CEV_local_term_class \<Gamma> T \<sigma> (subst s N)"
    using rel_Z unfolding CEV_quotient_map_rel_def by blast
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using arrow by (rule CEV_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Gamma> T"
    using arrow by (rule CEV_quotient_arrow_target)
  have classes_MN:
      "CEV_local_term_class \<Delta> S \<sigma> M =
        CEV_local_term_class \<Delta> S \<sigma> N"
    using X_M X_N by simp
  have MN: "CEV_local_term_equiv \<Delta> S \<sigma> M N"
    using CEV_local_term_class_eq[
      OF source M_type N_type] classes_MN by blast
  have sub_equiv:
      "CEV_local_term_equiv \<Gamma> T \<sigma> (subst s M) (subst s N)"
    using arrow MN by (rule CEV_quotient_arrow_preserves_equiv)
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_quotient_arrow_typed)
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have classes_sub:
      "CEV_local_term_class \<Gamma> T \<sigma> (subst s M) =
        CEV_local_term_class \<Gamma> T \<sigma> (subst s N)"
    using CEV_local_term_class_eq[
      OF target sub_M_type sub_N_type] sub_equiv by blast
  show "Y = Z"
    using Y_def Z_def classes_sub by simp
qed

definition CEV_quotient_map ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow>
      oterm env \<Rightarrow> otype \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma> X =
    (THE Y. CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> X Y)"

lemma CEV_quotient_map_class:
  assumes arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
  shows "CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma>
      (CEV_local_term_class \<Delta> S \<sigma> M) =
    CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
proof -
  let ?X = "CEV_local_term_class \<Delta> S \<sigma> M"
  let ?Y = "CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
  have rel: "CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> ?X ?Y"
    unfolding CEV_quotient_map_rel_def using M_type by blast
  have unique:
      "\<And>Z. CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> ?X Z
        \<Longrightarrow> Z = ?Y"
  proof -
    fix Z
    assume rel_Z: "CEV_quotient_map_rel \<Delta> S \<Gamma> T s \<sigma> ?X Z"
    have "?Y = Z"
      using arrow rel rel_Z by (rule CEV_quotient_map_rel_unique)
    then show "Z = ?Y"
      by simp
  qed
  show ?thesis
    unfolding CEV_quotient_map_def
    using rel unique by (rule the_equality)
qed

lemma CEV_quotient_map_closed:
  assumes arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and X_dom: "X \<in> CEV_local_domain \<Delta> S \<sigma>"
  shows "CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma> X
    \<in> CEV_local_domain \<Gamma> T \<sigma>"
proof -
  obtain M where M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and X_def: "X = CEV_local_term_class \<Delta> S \<sigma> M"
    using X_dom unfolding CEV_local_domain_def by blast
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_quotient_arrow_typed)
  have sub_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have map_eq:
      "CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma> X =
        CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
    unfolding X_def using arrow M_type by (rule CEV_quotient_map_class)
  show ?thesis
    unfolding map_eq using sub_type by (rule CEV_local_domainI)
qed

lemma CEV_quotient_map_preserves_app:
  assumes arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and F_type: "\<Delta> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Delta> \<turnstile> A : \<sigma>"
  shows "CEV_quotient_map \<Delta> S \<Gamma> T s \<tau>
      (CEV_local_app \<Delta> S \<sigma> \<tau>
        (CEV_local_term_class \<Delta> S (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (CEV_local_term_class \<Delta> S \<sigma> A)) =
    CEV_local_app \<Gamma> T \<sigma> \<tau>
      (CEV_quotient_map \<Delta> S \<Gamma> T s (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (CEV_local_term_class \<Delta> S (\<sigma> \<rightarrow>\<^sub>o \<tau>) F))
      (CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma>
        (CEV_local_term_class \<Delta> S \<sigma> A))"
proof -
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using arrow by (rule CEV_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Gamma> T"
    using arrow by (rule CEV_quotient_arrow_target)
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_quotient_arrow_typed)
  have sub_F_type: "\<Gamma> \<turnstile> subst s F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F_type s_typed by (rule term_subst_preserves_typing)
  have sub_A_type: "\<Gamma> \<turnstile> subst s A : \<sigma>"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have app_type: "\<Delta> \<turnstile> App F A : \<tau>"
    using F_type A_type by auto
  show ?thesis
    using CEV_local_app_class[OF source F_type A_type]
      CEV_quotient_map_class[OF arrow app_type]
      CEV_quotient_map_class[OF arrow F_type]
      CEV_quotient_map_class[OF arrow A_type]
      CEV_local_app_class[OF target sub_F_type sub_A_type]
    by simp
qed

lemma CEV_quotient_map_id_class:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "CEV_quotient_map \<Gamma> T \<Gamma> T Var \<sigma>
      (CEV_local_term_class \<Gamma> T \<sigma> M) =
    CEV_local_term_class \<Gamma> T \<sigma> M"
  using CEV_quotient_map_class[
    OF CEV_quotient_arrow_id[OF henkin] M_type] by simp

lemma CEV_quotient_map_comp_class:
  assumes s_arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    and t_arrow: "CEV_quotient_arrow \<Gamma> T \<Lambda> U t"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
  shows "CEV_quotient_map \<Gamma> T \<Lambda> U t \<sigma>
      (CEV_quotient_map \<Delta> S \<Gamma> T s \<sigma>
        (CEV_local_term_class \<Delta> S \<sigma> M)) =
    CEV_quotient_map \<Delta> S \<Lambda> U (\<lambda>n. subst t (s n)) \<sigma>
      (CEV_local_term_class \<Delta> S \<sigma> M)"
proof -
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using s_arrow by (rule CEV_quotient_arrow_typed)
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have comp_arrow:
      "CEV_quotient_arrow \<Delta> S \<Lambda> U (\<lambda>n. subst t (s n))"
    using s_arrow t_arrow by (rule CEV_quotient_arrow_comp)
  show ?thesis
    using CEV_quotient_map_class[OF s_arrow M_type]
      CEV_quotient_map_class[OF t_arrow sub_M_type]
      CEV_quotient_map_class[OF comp_arrow M_type]
    by (simp add: subst_comp)
qed

definition CEV_subst_identity_diagram ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm env \<Rightarrow> oterm set" where
  "CEV_subst_identity_diagram \<Delta> S \<Gamma> s =
    {Eq \<sigma> (subst s M) (subst s N) | \<sigma> M N.
      \<Delta> \<turnstile> M : \<sigma> \<and> \<Delta> \<turnstile> N : \<sigma> \<and> Eq \<sigma> M N \<in> S}"

lemma CEV_subst_identity_diagram_typed:
  assumes s_typed: "term_subst_typed \<Delta> \<Gamma> s"
  shows "typed_theory \<Gamma> (CEV_subst_identity_diagram \<Delta> S \<Gamma> s)"
  unfolding typed_theory_def
proof (intro ballI)
  fix A
  assume "A \<in> CEV_subst_identity_diagram \<Delta> S \<Gamma> s"
  then obtain \<sigma> M N where
      A_def: "A = Eq \<sigma> (subst s M) (subst s N)"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and N_type: "\<Delta> \<turnstile> N : \<sigma>"
    unfolding CEV_subst_identity_diagram_def by blast
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  show "\<Gamma> \<turnstile> A : Prop"
    unfolding A_def using sub_M_type sub_N_type by auto
qed

theorem CEV_quotient_arrow_iff_diagram_subset:
  assumes source: "CEV_clean_Henkin_theory \<Delta> S"
    and target: "CEV_clean_Henkin_theory \<Gamma> T"
    and s_typed: "term_subst_typed \<Delta> \<Gamma> s"
  shows "CEV_quotient_arrow \<Delta> S \<Gamma> T s \<longleftrightarrow>
    CEV_subst_identity_diagram \<Delta> S \<Gamma> s \<subseteq> T"
proof
  assume arrow: "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
  show "CEV_subst_identity_diagram \<Delta> S \<Gamma> s \<subseteq> T"
  proof
    fix A
    assume "A \<in> CEV_subst_identity_diagram \<Delta> S \<Gamma> s"
    then obtain \<sigma> M N where
      A_def: "A = Eq \<sigma> (subst s M) (subst s N)"
      and M_type: "\<Delta> \<turnstile> M : \<sigma>"
      and N_type: "\<Delta> \<turnstile> N : \<sigma>"
      and eq_in: "Eq \<sigma> M N \<in> S"
      unfolding CEV_subst_identity_diagram_def by blast
    have "Eq \<sigma> (subst s M) (subst s N) \<in> T"
      using arrow M_type N_type eq_in
      unfolding CEV_quotient_arrow_def by blast
    then show "A \<in> T"
      unfolding A_def .
  qed
next
  assume subset: "CEV_subst_identity_diagram \<Delta> S \<Gamma> s \<subseteq> T"
  have preserves:
      "\<And>\<sigma> M N. \<Delta> \<turnstile> M : \<sigma> \<Longrightarrow> \<Delta> \<turnstile> N : \<sigma> \<Longrightarrow>
        Eq \<sigma> M N \<in> S \<Longrightarrow>
        Eq \<sigma> (subst s M) (subst s N) \<in> T"
  proof -
    fix \<sigma> M N
    assume M_type: "\<Delta> \<turnstile> M : \<sigma>"
      and N_type: "\<Delta> \<turnstile> N : \<sigma>"
      and eq_in: "Eq \<sigma> M N \<in> S"
    have "Eq \<sigma> (subst s M) (subst s N)
        \<in> CEV_subst_identity_diagram \<Delta> S \<Gamma> s"
      unfolding CEV_subst_identity_diagram_def
      using M_type N_type eq_in by blast
    then show "Eq \<sigma> (subst s M) (subst s N) \<in> T"
      using subset by blast
  qed
  show "CEV_quotient_arrow \<Delta> S \<Gamma> T s"
    unfolding CEV_quotient_arrow_def
    using source target s_typed preserves by blast
qed

definition CEV_subst_diagram_consistent ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm env \<Rightarrow> bool" where
  "CEV_subst_diagram_consistent \<Delta> S \<Gamma> s \<longleftrightarrow>
    CEV_consistent \<Gamma> (CEV_subst_identity_diagram \<Delta> S \<Gamma> s)"

text \<open>
  The remaining existence problem for arrows is now explicit: for each typed
  substitution needed by the Bacon--Dorr separation argument, extend its
  transported identity diagram to a clean CEV Henkin theory.  The hard step is
  consistency of that diagram together with a chosen separating formula; it is
  not supplied by ordinary one-world Lindenbaum completion.
\<close>

section \<open>Propositional truth is well-defined on the quotient\<close>

lemma CEV_clean_Henkin_prop_identity_forward:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq_in: "Eq Prop A B \<in> T"
    and A_in: "A \<in> T"
  shows "B \<in> T"
proof -
  have id_type: "\<Gamma> \<turnstile> prop_id : Prop \<rightarrow>\<^sub>o Prop"
    by (rule typed_prop_id)
  have app_A_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using id_type A_type by auto
  have app_B_type: "\<Gamma> \<turnstile> App prop_id B : Prop"
    using id_type B_type by auto
  have d_eq: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Eq Prop A B"
    using eq_in A_type B_type by (intro CEV_set_derivable.Assumption) auto
  have ll:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq Prop A B) (Imp (App prop_id A) (App prop_id B))"
    using A_type B_type id_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have d_ll:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Eq Prop A B) (Imp (App prop_id A) (App prop_id B))"
    using ll by (rule CEV_set_derivable.Theorem)
  have d_app_imp:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (App prop_id A) (App prop_id B)"
    using d_eq d_ll by (rule CEV_set_derivable.Derive_MP)
  have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using A_in A_type by (rule CEV_set_derivable.Assumption)
  have A_to_app: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (App prop_id A)"
    using A_type by (rule CEV_imp_app_prop_id)
  have d_A_to_app: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp A (App prop_id A)"
    using A_to_app by (rule CEV_set_derivable.Theorem)
  have d_app_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s App prop_id A"
    using d_A d_A_to_app by (rule CEV_set_derivable.Derive_MP)
  have d_app_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s App prop_id B"
    using d_app_A d_app_imp by (rule CEV_set_derivable.Derive_MP)
  have app_to_B: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App prop_id B) B"
    using B_type by (rule CEV_app_prop_id_imp)
  have d_app_to_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (App prop_id B) B"
    using app_to_B by (rule CEV_set_derivable.Theorem)
  have d_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s B"
    using d_app_B d_app_to_B by (rule CEV_set_derivable.Derive_MP)
  show "B \<in> T"
    using henkin d_B by (rule CEV_clean_Henkin_closed_under_set_derivable)
qed

lemma CEV_clean_Henkin_prop_identity_mem_iff:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and eq_in: "Eq Prop A B \<in> T"
  shows "A \<in> T \<longleftrightarrow> B \<in> T"
proof
  assume "A \<in> T"
  then show "B \<in> T"
    using CEV_clean_Henkin_prop_identity_forward[
      OF henkin A_type B_type eq_in] by blast
next
  assume B_in: "B \<in> T"
  have AB: "CEV_local_term_equiv \<Gamma> T Prop A B"
    using A_type B_type eq_in unfolding CEV_local_term_equiv_def by blast
  have BA: "CEV_local_term_equiv \<Gamma> T Prop B A"
    using henkin AB by (rule CEV_local_term_equiv_sym)
  have BA_in: "Eq Prop B A \<in> T"
    using BA unfolding CEV_local_term_equiv_def by blast
  show "A \<in> T"
    using henkin B_type A_type BA_in B_in
    by (rule CEV_clean_Henkin_prop_identity_forward)
qed

definition CEV_local_holds ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_local_holds \<Gamma> T X \<longleftrightarrow> (\<exists>A.
    \<Gamma> \<turnstile> A : Prop \<and>
    X = CEV_local_term_class \<Gamma> T Prop A \<and> A \<in> T)"

lemma CEV_local_holds_class_iff:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "CEV_local_holds \<Gamma> T
      (CEV_local_term_class \<Gamma> T Prop A) \<longleftrightarrow> A \<in> T"
proof
  assume holds:
      "CEV_local_holds \<Gamma> T (CEV_local_term_class \<Gamma> T Prop A)"
  then obtain B where B_type: "\<Gamma> \<turnstile> B : Prop"
    and classes:
      "CEV_local_term_class \<Gamma> T Prop A =
        CEV_local_term_class \<Gamma> T Prop B"
    and B_in: "B \<in> T"
    unfolding CEV_local_holds_def by blast
  have AB: "CEV_local_term_equiv \<Gamma> T Prop A B"
    using CEV_local_term_class_eq[OF henkin A_type B_type] classes by blast
  have eq_in: "Eq Prop A B \<in> T"
    using AB unfolding CEV_local_term_equiv_def by blast
  show "A \<in> T"
    using CEV_clean_Henkin_prop_identity_mem_iff[
      OF henkin A_type B_type eq_in] B_in by blast
next
  assume A_in: "A \<in> T"
  show "CEV_local_holds \<Gamma> T
      (CEV_local_term_class \<Gamma> T Prop A)"
    unfolding CEV_local_holds_def using A_type A_in by blast
qed

section \<open>The identity-diagram coherence lemma\<close>

text \<open>
  For the modal truth lemma it is enough to use the identity substitution.
  Starting from a clean Henkin world \<open>S\<close>, its identity diagram contains
  exactly the identities true at \<open>S\<close>.  If \<open>\<box>\<^sub>o A\<close> is absent from
  \<open>S\<close>, the diagram must be consistent with \<open>\<not>A\<close>.  This is the
  syntactic core of the Bacon--Dorr successor construction.

  The proof below does not assume a contextual form of Vector Equivalence.
  Instead it uses only (i) necessitation for theorems, (ii) modal K, and
  (iii) rigidity of identity, already derived as
  \<open>E \<longrightarrow> \<box>\<^sub>o E\<close> when \<open>E\<close> is an identity formula.
\<close>

definition CEV_identity_diagram :: "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_identity_diagram \<Gamma> S =
    CEV_subst_identity_diagram \<Gamma> S \<Gamma> Var"

lemma CEV_identity_diagram_iff:
  "E \<in> CEV_identity_diagram \<Gamma> S \<longleftrightarrow>
    (\<exists>\<sigma> M N. E = Eq \<sigma> M N \<and>
      \<Gamma> \<turnstile> M : \<sigma> \<and> \<Gamma> \<turnstile> N : \<sigma> \<and>
      Eq \<sigma> M N \<in> S)"
  unfolding CEV_identity_diagram_def CEV_subst_identity_diagram_def
  by auto

lemma CEV_identity_diagram_typed:
  "typed_theory \<Gamma> (CEV_identity_diagram \<Gamma> S)"
  unfolding CEV_identity_diagram_def
  using CEV_subst_identity_diagram_typed[OF term_subst_typed_Var] .

lemma CEV_set_derivable_box_lift:
  assumes derivable: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s A"
    and boxed_assumptions:
      "\<And>B. B \<in> U \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o A"
  using derivable boxed_assumptions
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A U \<Gamma>)
  then show ?case
    by blast
next
  case (Theorem \<Gamma> A U)
  have "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o A"
    using Theorem.hyps by (rule CEV_necessitation)
  then show ?case
    by (rule CEV_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> U A B)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Derive_MP.hyps(1) by (rule CEV_set_derivable_formula)
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using Derive_MP.hyps(2) by (rule CEV_set_derivable_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using imp_type by (auto elim: has_type.cases)
  have d_box_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o A"
    using Derive_MP.IH(1)[OF Derive_MP.prems] .
  have d_box_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o (Imp A B)"
    using Derive_MP.IH(2)[OF Derive_MP.prems] .
  have K:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (\<box>\<^sub>o (Imp A B)) (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B))"
    using CEV_modal_K[OF A_type B_type]
    by (simp add: modal_K_def)
  have d_K:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (\<box>\<^sub>o (Imp A B)) (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B))"
    using K by (rule CEV_set_derivable.Theorem)
  have d_step:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
    using d_box_imp d_K by (rule CEV_set_derivable.Derive_MP)
  show ?case
    using d_box_A d_step by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_identity_diagram_formula_boxed:
  assumes E_in: "E \<in> CEV_identity_diagram \<Gamma> S"
  shows "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o E"
proof -
  obtain \<sigma> M N where E_def: "E = Eq \<sigma> M N"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and E_source: "Eq \<sigma> M N \<in> S"
    using E_in unfolding CEV_identity_diagram_iff by blast
  have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using M_type N_type by auto
  have d_E: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Eq \<sigma> M N"
    using E_source E_type by (rule CEV_set_derivable.Assumption)
  have rigid:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Eq \<sigma> M N) (\<box>\<^sub>o (Eq \<sigma> M N))"
    using CEV_eq_truth_of_eq[OF M_type N_type]
    by (simp add: ObjBox_def)
  have d_rigid:
      "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Eq \<sigma> M N) (\<box>\<^sub>o (Eq \<sigma> M N))"
    using rigid by (rule CEV_set_derivable.Theorem)
  have "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o (Eq \<sigma> M N)"
    using d_E d_rigid by (rule CEV_set_derivable.Derive_MP)
  then show ?thesis
    using E_def by simp
qed

theorem CEV_identity_diagram_derivable_implies_box_derivable:
  assumes "\<Gamma> ; CEV_identity_diagram \<Gamma> S \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o A"
  using assms
proof (rule CEV_set_derivable_box_lift)
  fix E
  assume "E \<in> CEV_identity_diagram \<Gamma> S"
  then show "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o E"
    by (rule CEV_identity_diagram_formula_boxed)
qed

theorem CEV_identity_separator_consistent:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
  shows "CEV_consistent \<Gamma>
    (insert (Neg A) (CEV_identity_diagram \<Gamma> S))"
proof -
  have not_d:
      "\<not> \<Gamma> ; CEV_identity_diagram \<Gamma> S \<turnstile>\<^sub>CEV\<^sub>s A"
  proof
    assume d_A:
        "\<Gamma> ; CEV_identity_diagram \<Gamma> S \<turnstile>\<^sub>CEV\<^sub>s A"
    have d_box: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o A"
      using d_A by (rule CEV_identity_diagram_derivable_implies_box_derivable)
    have box_in: "\<box>\<^sub>o A \<in> S"
      using henkin d_box by (rule CEV_clean_Henkin_closed_under_set_derivable)
    show False
      using box_absent box_in by blast
  qed
  show ?thesis
    using A_type not_d by (rule CEV_consistent_insert_neg_of_not_set_derivable)
qed

lemma CEV_box_absent_of_formula_absent:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and A_absent: "A \<notin> S"
  shows "\<box>\<^sub>o A \<notin> S"
proof
  assume box_in: "\<box>\<^sub>o A \<in> S"
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop"
    using A_type by (rule typed_ObjBox)
  have d_box: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s \<box>\<^sub>o A"
    using box_in box_type by (rule CEV_set_derivable.Assumption)
  have T: "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o A) A"
    using CEV_modal_T[OF A_type] by (simp add: modal_T_def)
  have d_T: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s Imp (\<box>\<^sub>o A) A"
    using T by (rule CEV_set_derivable.Theorem)
  have d_A: "\<Gamma> ; S \<turnstile>\<^sub>CEV\<^sub>s A"
    using d_box d_T by (rule CEV_set_derivable.Derive_MP)
  have "A \<in> S"
    using henkin d_A by (rule CEV_clean_Henkin_closed_under_set_derivable)
  then show False
    using A_absent by blast
qed

corollary CEV_identity_separates_unequal_consistently:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and unequal: "Eq \<sigma> M N \<notin> S"
  shows "CEV_consistent \<Gamma>
    (insert (Neg (Eq \<sigma> M N)) (CEV_identity_diagram \<Gamma> S))"
proof -
  have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using M_type N_type by auto
  have box_absent: "\<box>\<^sub>o (Eq \<sigma> M N) \<notin> S"
    using henkin E_type unequal by (rule CEV_box_absent_of_formula_absent)
  show ?thesis
    using henkin E_type box_absent by (rule CEV_identity_separator_consistent)
qed

text \<open>
  This settles the coherence question for the identity-diagram successor:
  every identity true at the source can be preserved while falsifying any
  proposition not necessary there.  In particular, genuinely unequal source
  terms can be separated at a consistent successor.

  The separator theory above is generally infinite.  The finite-base Henkin
  theorem therefore needs the following reserve-sensitive generalization.
\<close>

section \<open>Henkin extension from an infinite base with a fresh reserve\<close>

definition CEV_fresh_extendible_base :: "oterm set \<Rightarrow> bool" where
  "CEV_fresh_extendible_base B \<longleftrightarrow>
    (\<forall>T A. B \<subseteq> T \<longrightarrow> finite (T - B) \<longrightarrow>
      (\<exists>c. fresh_const_for c T A))"

text \<open>
  This condition says that after adjoining any finite collection of formulas
  to the base, a constant remains fresh for the enlarged theory and the next
  witness body.  A disjoint countable reserve of Henkin constants suffices.
  Stating the condition explicitly keeps the proof independent of any
  accidental convention about strings used as constant names.
\<close>

lemma CEV_fresh_extendible_base_if_infinite_unused:
  assumes unused: "infinite (UNIV - consts_of_set B)"
  shows "CEV_fresh_extendible_base B"
  unfolding CEV_fresh_extendible_base_def
proof (intro allI impI)
  fix T A
  assume base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
  have finite_extra_consts: "finite (consts_of_set (T - B))"
    using finite_extra by (rule finite_consts_of_set)
  have finite_forbidden:
      "finite (consts_of_set (T - B) \<union> consts_of A)"
    using finite_extra_consts by simp
  have cover:
      "consts_of_set T \<subseteq>
        consts_of_set B \<union> consts_of_set (T - B)"
    unfolding consts_of_set_def by blast
  have not_subset:
      "\<not> UNIV - consts_of_set B \<subseteq>
        consts_of_set (T - B) \<union> consts_of A"
  proof
    assume subset:
        "UNIV - consts_of_set B \<subseteq>
          consts_of_set (T - B) \<union> consts_of A"
    have "finite (UNIV - consts_of_set B)"
      by (rule finite_subset[OF subset finite_forbidden])
    then show False
      using unused by blast
  qed
  obtain c where c_unused: "c \<notin> consts_of_set B"
    and c_extra: "c \<notin> consts_of_set (T - B)"
    and c_A: "c \<notin> consts_of A"
    using not_subset by blast
  have c_T: "c \<notin> consts_of_set T"
    using cover c_unused c_extra by blast
  show "\<exists>c. fresh_const_for c T A"
    using c_T c_A unfolding fresh_const_for_def by blast
qed

lemma staged_henkin_chain_extends_base:
  "B \<subseteq> staged_henkin_chain \<Gamma> B enum n"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "staged_henkin_chain \<Gamma> B enum n \<subseteq>
      staged_henkin_chain \<Gamma> B enum (Suc n)"
    by (rule staged_henkin_chain_step)
  then show ?case
    using Suc.IH by blast
qed

lemma staged_henkin_chain_finite_over_base:
  "finite (staged_henkin_chain \<Gamma> B enum n - B)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain \<sigma> A where spec: "enum n = (\<sigma>, A)"
    by (cases "enum n") auto
  let ?T = "staged_henkin_chain \<Gamma> B enum n"
  let ?W =
    "henkin_witness_axiom (fresh_const_for_stage ?T A) \<sigma> A"
  have finite_insert: "finite (insert ?W (?T - B))"
    using Suc.IH by simp
  have subset: "insert ?W ?T - B \<subseteq> insert ?W (?T - B)"
    by blast
  have finite_step: "finite (insert ?W ?T - B)"
    by (rule finite_subset[OF subset finite_insert])
  show ?case
    using Suc.IH finite_step
    by (simp add: staged_henkin_step_def spec)
qed

lemma fresh_const_for_stage_from_reserve:
  assumes reserve: "CEV_fresh_extendible_base B"
    and base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
  shows "fresh_const_for (fresh_const_for_stage T A) T A"
proof -
  obtain c where fresh: "fresh_const_for c T A"
    using reserve base_sub finite_extra
    unfolding CEV_fresh_extendible_base_def by blast
  show ?thesis
    unfolding fresh_const_for_stage_def
    using fresh by (metis someI_ex)
qed

lemma CEV_staged_henkin_step_consistent_from_reserve:
  assumes reserve: "CEV_fresh_extendible_base B"
    and base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh:
        "fresh_const_for (fresh_const_for_stage T A) T A"
      using reserve base_sub finite_extra
      by (rule fresh_const_for_stage_from_reserve)
    have fresh_T:
        "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A:
        "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CEV_consistent \<Gamma>
        (insert
          (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using typed consistent fresh_T fresh_A True
      by (rule CEV_consistent_insert_fresh_witness_axiom_clean)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma CEV_staged_henkin_chain_consistent_from_reserve:
  assumes reserve: "CEV_fresh_extendible_base B"
    and typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
  shows "CEV_consistent \<Gamma> (staged_henkin_chain \<Gamma> B enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  let ?T = "staged_henkin_chain \<Gamma> B enum n"
  have base_sub: "B \<subseteq> ?T"
    by (rule staged_henkin_chain_extends_base)
  have finite_extra: "finite (?T - B)"
    by (rule staged_henkin_chain_finite_over_base)
  have typed_T: "typed_theory \<Gamma> ?T"
    using Suc.prems(2) by (rule staged_henkin_chain_typed)
  have consistent_T: "CEV_consistent \<Gamma> ?T"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1) base_sub finite_extra typed_T consistent_T
    by (simp add: CEV_staged_henkin_step_consistent_from_reserve)
qed

lemma CEV_staged_henkin_extension_consistent_from_reserve:
  assumes reserve: "CEV_fresh_extendible_base B"
    and typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
  shows "CEV_consistent \<Gamma> (staged_henkin_extension \<Gamma> B enum)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false:
      "\<Gamma> ; staged_henkin_extension \<Gamma> B enum
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> B enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_false by (rule CEV_set_derivable_finite_support)
  have U_sub_union:
      "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> B enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> B enum n \<subseteq>
      staged_henkin_chain \<Gamma> B enum (Suc n)"
    by (rule staged_henkin_chain_step)
  obtain n where U_sub_chain:
      "U \<subseteq> staged_henkin_chain \<Gamma> B enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have d_chain:
      "\<Gamma> ; staged_henkin_chain \<Gamma> B enum n
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_set_derivable_mono)
  have chain_consistent:
      "CEV_consistent \<Gamma> (staged_henkin_chain \<Gamma> B enum n)"
    using assms by (rule CEV_staged_henkin_chain_consistent_from_reserve)
  show False
    using d_chain chain_consistent unfolding CEV_consistent_def by blast
qed

theorem CEV_clean_Henkin_extension_from_fresh_extendible_base:
  assumes reserve: "CEV_fresh_extendible_base B"
    and typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "B \<subseteq> T"
proof -
  obtain body_enum where
      body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?S = "staged_henkin_extension \<Gamma> B body_enum"
  have B_sub_S: "B \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have typed_S: "typed_theory \<Gamma> ?S"
    using typed by (rule staged_henkin_extension_typed)
  have consistent_S: "CEV_consistent \<Gamma> ?S"
    using reserve typed consistent
    by (rule CEV_staged_henkin_extension_consistent_from_reserve)
  have available_S: "Henkin_witness_axioms_available \<Gamma> ?S"
    using body_enum
    by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where
      formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?T = "CEV_lindenbaum_extension \<Gamma> ?S formula_enum"
  have S_sub_T: "?S \<subseteq> ?T"
    by (rule CEV_lindenbaum_extension_extends)
  have local_T: "CEV_locally_maximal_consistent \<Gamma> ?T"
    using typed_S consistent_S formula_enum
    by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  have available_T: "Henkin_witness_axioms_available \<Gamma> ?T"
    using available_S S_sub_T by (rule Henkin_witness_axioms_available_mono)
  have witnessed_T: "Henkin_witnessed \<Gamma> ?T"
    using local_T available_T
    by (rule Henkin_witnessed_of_CEV_local_maximal_available_clean)
  have henkin_T: "CEV_clean_Henkin_theory \<Gamma> ?T"
    using local_T witnessed_T unfolding CEV_clean_Henkin_theory_def by blast
  have B_sub_T: "B \<subseteq> ?T"
    using B_sub_S S_sub_T by blast
  show ?thesis
    using that[OF henkin_T B_sub_T] .
qed

text \<open>
  Historical conditional interface: the full identity diagram contains the
  reflexive identity for every constant name.  Hence the fresh-reserve
  assumption below cannot hold for a clean Henkin source.  This is proved
  explicitly by \<open>CEV_identity_separator_not_fresh_extendible\<close> in
  \<open>Bacon_Supported_Canonical\<close>.  The theorem and its reserve-dependent
  successor corollaries are retained as vacuous implications, not as usable
  existence results.  Use \<open>CEV_supported_modal_successor\<close> instead.
\<close>

theorem CEV_identity_separator_Henkin_target:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
    and reserve: "CEV_fresh_extendible_base
      (insert (Neg A) (CEV_identity_diagram \<Gamma> S))"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "CEV_identity_diagram \<Gamma> S \<subseteq> T"
    and "Neg A \<in> T"
proof -
  let ?B = "insert (Neg A) (CEV_identity_diagram \<Gamma> S)"
  have typed_B: "typed_theory \<Gamma> ?B"
    using A_type CEV_identity_diagram_typed
    unfolding typed_theory_def by auto
  have consistent_B: "CEV_consistent \<Gamma> ?B"
    using henkin A_type box_absent by (rule CEV_identity_separator_consistent)
  obtain T where henkin_T: "CEV_clean_Henkin_theory \<Gamma> T"
    and B_sub_T: "?B \<subseteq> T"
    using reserve typed_B consistent_B
    by (rule CEV_clean_Henkin_extension_from_fresh_extendible_base)
  have diagram_sub: "CEV_identity_diagram \<Gamma> S \<subseteq> T"
    using B_sub_T by blast
  have neg_in: "Neg A \<in> T"
    using B_sub_T by blast
  show ?thesis
    using that[OF henkin_T diagram_sub neg_in] .
qed

corollary CEV_identity_unequal_Henkin_target:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and unequal: "Eq \<sigma> M N \<notin> S"
    and reserve: "CEV_fresh_extendible_base
      (insert (Neg (Eq \<sigma> M N)) (CEV_identity_diagram \<Gamma> S))"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "CEV_identity_diagram \<Gamma> S \<subseteq> T"
    and "Neg (Eq \<sigma> M N) \<in> T"
proof -
  have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using M_type N_type by auto
  have box_absent: "\<box>\<^sub>o (Eq \<sigma> M N) \<notin> S"
    using henkin E_type unequal by (rule CEV_box_absent_of_formula_absent)
  show ?thesis
    using henkin E_type box_absent reserve that
    by (rule CEV_identity_separator_Henkin_target)
qed

lemma CEV_identity_diagram_subset_gives_arrow:
  assumes source: "CEV_clean_Henkin_theory \<Gamma> S"
    and target: "CEV_clean_Henkin_theory \<Gamma> T"
    and diagram_sub: "CEV_identity_diagram \<Gamma> S \<subseteq> T"
  shows "CEV_quotient_arrow \<Gamma> S \<Gamma> T Var"
proof -
  have subst_diagram_sub:
      "CEV_subst_identity_diagram \<Gamma> S \<Gamma> Var \<subseteq> T"
    using diagram_sub unfolding CEV_identity_diagram_def .
  show ?thesis
    using CEV_quotient_arrow_iff_diagram_subset[
      OF source target term_subst_typed_Var] subst_diagram_sub
    by blast
qed

lemma CEV_clean_Henkin_formula_absent_of_neg_in:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and neg_in: "Neg A \<in> T"
  shows "A \<notin> T"
proof
  assume A_in: "A \<in> T"
  have d_A: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    using A_in A_type by (rule CEV_set_derivable.Assumption)
  have d_false: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_A neg_in by (rule CEV_set_derives_ObjFalse_of_formula_and_neg)
  have consistent: "CEV_consistent \<Gamma> T"
    using CEV_clean_Henkin_local[OF henkin]
    unfolding CEV_locally_maximal_consistent_def by blast
  show False
    using consistent d_false unfolding CEV_consistent_def by blast
qed

theorem CEV_identity_modal_successor:
  assumes source: "CEV_clean_Henkin_theory \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
    and reserve: "CEV_fresh_extendible_base
      (insert (Neg A) (CEV_identity_diagram \<Gamma> S))"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "CEV_quotient_arrow \<Gamma> S \<Gamma> T Var"
    and "Neg A \<in> T"
    and "A \<notin> T"
proof -
  obtain T where target: "CEV_clean_Henkin_theory \<Gamma> T"
    and diagram_sub: "CEV_identity_diagram \<Gamma> S \<subseteq> T"
    and neg_in: "Neg A \<in> T"
    using source A_type box_absent reserve
    by (rule CEV_identity_separator_Henkin_target)
  have arrow: "CEV_quotient_arrow \<Gamma> S \<Gamma> T Var"
    using source target diagram_sub by (rule CEV_identity_diagram_subset_gives_arrow)
  have A_absent: "A \<notin> T"
    using target A_type neg_in by (rule CEV_clean_Henkin_formula_absent_of_neg_in)
  show ?thesis
    using that[OF target arrow neg_in A_absent] .
qed

theorem CEV_identity_arrow_separates_unequal_classes:
  assumes source: "CEV_clean_Henkin_theory \<Gamma> S"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and unequal: "Eq \<sigma> M N \<notin> S"
    and reserve: "CEV_fresh_extendible_base
      (insert (Neg (Eq \<sigma> M N)) (CEV_identity_diagram \<Gamma> S))"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "CEV_quotient_arrow \<Gamma> S \<Gamma> T Var"
    and
      "CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M)
        \<noteq>
       CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N)"
proof -
  let ?E = "Eq \<sigma> M N"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using M_type N_type by auto
  have box_absent: "\<box>\<^sub>o ?E \<notin> S"
    using source E_type unequal by (rule CEV_box_absent_of_formula_absent)
  obtain T where target: "CEV_clean_Henkin_theory \<Gamma> T"
    and arrow: "CEV_quotient_arrow \<Gamma> S \<Gamma> T Var"
    and neg_in: "Neg ?E \<in> T"
    and E_absent: "?E \<notin> T"
    using source E_type box_absent reserve
    by (rule CEV_identity_modal_successor)
  have classes_neq:
      "CEV_local_term_class \<Gamma> T \<sigma> M \<noteq>
        CEV_local_term_class \<Gamma> T \<sigma> N"
  proof
    assume classes_eq:
        "CEV_local_term_class \<Gamma> T \<sigma> M =
          CEV_local_term_class \<Gamma> T \<sigma> N"
    have equiv: "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
      using CEV_local_term_class_eq[OF target M_type N_type] classes_eq
      by blast
    have "?E \<in> T"
      using equiv unfolding CEV_local_term_equiv_def by blast
    then show False
      using E_absent by blast
  qed
  have map_M:
      "CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M) =
        CEV_local_term_class \<Gamma> T \<sigma> M"
    using CEV_quotient_map_class[OF arrow M_type] by simp
  have map_N:
      "CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N) =
        CEV_local_term_class \<Gamma> T \<sigma> N"
    using CEV_quotient_map_class[OF arrow N_type] by simp
  have separated:
      "CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M)
        \<noteq>
       CEV_quotient_map \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N)"
    using classes_neq map_M map_N by simp
  show ?thesis
    using that[OF target arrow separated] .
qed

text \<open>
  These final unrestricted-reserve implications do not establish the
  existence of a successor: their reserve premise is incompatible with the
  clean Henkin source, as \<open>Bacon_Supported_Canonical\<close> proves.  That next
  theory restricts the preserved diagram to a supported language and proves
  applicable successor results with a fresh witness block.

  Even preservation of unequal classes at a target is not the profile
  separation needed for Bacon--Dorr Definition 3.11 and Theorem 3.12
  (pp. 50--52).  Quasi-Fregeanness requires different truth values at some
  target; quasi-functionality requires different application values there.
  Neither the historical result above nor unequal-class preservation alone
  supplies the complete intensional-category or action-model construction.
\<close>

end
