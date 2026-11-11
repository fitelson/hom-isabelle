theory Goodman_PP_Refutation_Kit
  imports "Goodman_Integration_M5_Object.Goodman_M5_Nested_Collision"
begin

text \<open>
  TECHNICAL THEORY for the formalization of the note
  \<open>reports/PP_RECOMBINATION_EXPLANATORY_PROOF_2026-11-11.tex\<close>.
  Derived rules of the axiom extension
  \<open>\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A\<close>, valid for every stock \<open>T\<close>.  Nothing here adds an
  axiom; every rule is derived from the constructors of \<open>CEV_axiom_proves\<close>
  and existing base theorems.
\<close>

abbreviation gr_u :: otype where
  "gr_u \<equiv> Prop \<rightarrow>\<^sub>o Prop"

section \<open>Typing inversion\<close>

lemma grk_ImpD1: "\<Gamma> \<turnstile> Imp A B : Prop \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  by (auto elim: has_type.cases)

lemma grk_ImpD2: "\<Gamma> \<turnstile> Imp A B : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  by (auto elim: has_type.cases)

lemma grk_ConjD1: "\<Gamma> \<turnstile> Conj A B : Prop \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  by (auto elim: has_type.cases)

lemma grk_ConjD2: "\<Gamma> \<turnstile> Conj A B : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
  by (auto elim: has_type.cases)

lemma grk_ForallD: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> A : Prop"
  by (auto elim: has_type.cases)

lemmas grk_ty = CEV_axiom_proves_formula
lemmas grk_imp_ty1 = grk_ImpD1[OF CEV_axiom_proves_formula]
lemmas grk_imp_ty2 = grk_ImpD2[OF CEV_axiom_proves_formula]

lemma grk_app_ty:
  "\<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> \<Gamma> \<turnstile> App Y p : Prop"
  by (rule has_type.App)

named_theorems gr_ty "typing introduction rules for the recombination development"

lemmas [gr_ty] =
  has_type.Neg has_type.Conj has_type.Disj has_type.Imp has_type.Eq
  has_type.Forall has_type.Exists
  typed_ObjBox typed_ObjTrue typed_ObjFalse grk_app_ty typed_shift_ctx typed_var0

section \<open>De Bruijn bookkeeping\<close>

named_theorems grs "simplification rules for renaming and substitution"

lemma grk_subst0_rename_Suc[grs]: "subst0 N (rename Suc M) = M"
  using subst0_shift[of N M] by (simp add: shift_def)

lemma grk_subst_case_rename_Suc[grs]: "subst (case_nat N Var) (rename Suc M) = M"
  using subst_case_nat_shift[of N M] by (simp add: shift_def)

lemma grk_rename_ObjTrue[grs]: "rename \<rho> ObjTrue = ObjTrue"
  by (simp add: ObjTrue_def)

lemma grk_subst_ObjTrue[grs]: "subst s ObjTrue = ObjTrue"
  by (simp add: ObjTrue_def)

lemma grk_rename_ObjFalse[grs]: "rename \<rho> ObjFalse = ObjFalse"
  by (simp add: ObjFalse_def ObjTrue_def)

lemma grk_subst_ObjFalse[grs]: "subst s ObjFalse = ObjFalse"
  by (simp add: ObjFalse_def ObjTrue_def)

lemma grk_rename_ObjBox[grs]: "rename \<rho> (\<box>\<^sub>o A) = \<box>\<^sub>o (rename \<rho> A)"
  by (simp add: ObjBox_def ObjTrue_def)

lemma grk_subst_ObjBox[grs]: "subst s (\<box>\<^sub>o A) = \<box>\<^sub>o (subst s A)"
  by (simp add: ObjBox_def ObjTrue_def)

lemma grk_subst0_simps[grs]:
  "subst0 M (Var 0) = M"
  "subst0 M (Var (Suc n)) = Var n"
  "subst0 M (App F A) = App (subst0 M F) (subst0 M A)"
  "subst0 M (Neg A) = Neg (subst0 M A)"
  "subst0 M (Conj A B) = Conj (subst0 M A) (subst0 M B)"
  "subst0 M (Disj A B) = Disj (subst0 M A) (subst0 M B)"
  "subst0 M (Imp A B) = Imp (subst0 M A) (subst0 M B)"
  "subst0 M (Eq \<sigma> A B) = Eq \<sigma> (subst0 M A) (subst0 M B)"
  "subst0 M (\<box>\<^sub>o A) = \<box>\<^sub>o (subst0 M A)"
  "subst0 M ObjTrue = ObjTrue"
  "subst0 M ObjFalse = ObjFalse"
  "subst0 M (shift A) = A"
  by (simp_all add: subst0_def grs)

lemma grk_shift_simps[grs]:
  "shift (App F A) = App (shift F) (shift A)"
  "shift (Neg A) = Neg (shift A)"
  "shift (Conj A B) = Conj (shift A) (shift B)"
  "shift (Disj A B) = Disj (shift A) (shift B)"
  "shift (Imp A B) = Imp (shift A) (shift B)"
  "shift (Eq \<sigma> A B) = Eq \<sigma> (shift A) (shift B)"
  "shift (\<box>\<^sub>o A) = \<box>\<^sub>o (shift A)"
  "shift ObjTrue = ObjTrue"
  "shift ObjFalse = ObjFalse"
  by (simp_all add: shift_def grs)

lemmas grk_rename_lift_shift = shift_rename_lift[symmetric]

section \<open>Propositional reasoning\<close>

named_theorems gr_eval "truth-functional unfolding of defined formulas"

text \<open>
  Tautology side conditions \<open>\<And>v. prop_eval v A\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> prop_eval v C\<close> are
  discharged by rewriting with the equations of \<open>prop_eval\<close> (and the
  one-layer unfoldings in \<open>gr_eval\<close>) WITHOUT using the premises as rewrite
  rules, then calling blast.  (Plain simp/auto can take tens of seconds on
  biconditional premises, which become mutually conditional rewrite rules.)
\<close>

method_setup gr_taut = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD
      (TRY (Local_Defs.unfold_tac ctxt
          (@{thms prop_eval.simps} @ Named_Theorems.get ctxt @{named_theorems gr_eval}))
        THEN ALLGOALS (Blast.blast_tac ctxt)))
\<close> "propositional side conditions: unfold prop_eval, then blast"

lemma grk_taut:
  assumes ty: "\<Gamma> \<turnstile> A : Prop"
    and taut: "\<And>v. prop_eval v A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  by (rule CEVp_M5_propositional[OF ty]) (simp add: taut)

lemma grk_PC1:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
proof -
  have at: "\<Gamma> \<turnstile> A : Prop" by (rule grk_ty[OF d])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A C"
    by (rule grk_taut[OF has_type.Imp[OF at ct]]) (simp add: taut)
  then show ?thesis by (rule CEV_axiom_proves.MP[OF d])
qed

lemma grk_PC2:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A1" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A2"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
  by (rule grk_PC1[OF CEV_axiom_conj_intro[OF d1 d2] ct]) (simp add: taut)

lemma grk_PC3:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A1" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A2"
    and d3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A3"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow>
      prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
  by (rule grk_PC2[OF CEV_axiom_conj_intro[OF d1 d2] d3 ct]) (simp add: taut)

lemma grk_PC4:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A1" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A2"
    and d3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A3" and d4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A4"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow>
      prop_eval v A4 \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
  by (rule grk_PC3[OF CEV_axiom_conj_intro[OF d1 d2] d3 d4 ct]) (simp add: taut)

lemma grk_PC5:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A1" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A2"
    and d3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A3" and d4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A4"
    and d5: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A5"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow>
      prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
  by (rule grk_PC4[OF CEV_axiom_conj_intro[OF d1 d2] d3 d4 d5 ct]) (simp add: taut)

lemma grk_PC6:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A1" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A2"
    and d3: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A3" and d4: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A4"
    and d5: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A5" and d6: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A6"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow>
      prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v A6 \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
  by (rule grk_PC5[OF CEV_axiom_conj_intro[OF d1 d2] d3 d4 d5 d6 ct]) (simp add: taut)

lemmas grk_MP = CEV_axiom_proves.MP

lemma grk_imp_trans:
  assumes ab: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    and bc: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A C"
  by (rule grk_PC2[OF ab bc has_type.Imp[OF grk_imp_ty1[OF ab] grk_imp_ty2[OF bc]]])
    gr_taut

lemma grk_conj1:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  by (rule grk_PC1[OF d grk_ConjD1[OF grk_ty[OF d]]]) simp

lemma grk_conj2:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  by (rule grk_PC1[OF d grk_ConjD2[OF grk_ty[OF d]]]) simp

lemmas grk_iff_intro = CEV_axiom_conj_intro

lemma grk_iff_sym:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (B \<longleftrightarrow>\<^sub>o A)"
  by (rule grk_iff_intro[OF grk_conj2[OF d] grk_conj1[OF d]])

lemma grk_iff_trans:
  assumes ab: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
    and bc: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (B \<longleftrightarrow>\<^sub>o C)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o C)"
  by (rule grk_iff_intro[OF
        grk_imp_trans[OF grk_conj1[OF ab] grk_conj1[OF bc]]
        grk_imp_trans[OF grk_conj2[OF bc] grk_conj2[OF ab]]])

lemma grk_iff_mp:
  assumes ab: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
    and a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  by (rule grk_MP[OF a grk_conj1[OF ab]])

lemma grk_iff_mp_rev:
  assumes ab: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
    and b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  by (rule grk_MP[OF b grk_conj2[OF ab]])

section \<open>S4\<close>

lemmas grk_nec = CEV_axiom_necessitation

lemma grk_T:
  "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) A"
  by (rule gi_M5_modal_T)

lemma grk_4:
  "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (\<box>\<^sub>o A))"
  by (rule gi_M5_modal_four)

lemma grk_K:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp A B)) (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B))"
  using CEV_axiom_proves.Base[OF CEV_modal_K[OF at bt]] by (simp only: modal_K_def)

lemma grk_box_mono:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
  by (rule gi_M5_box_mono[OF grk_imp_ty1[OF d] grk_imp_ty2[OF d] d])

lemma grk_box_mono2:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp B C)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o C))"
proof -
  have bct: "\<Gamma> \<turnstile> Imp B C : Prop" by (rule grk_imp_ty2[OF d])
  have s1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B C))"
    by (rule grk_box_mono[OF d])
  have s2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp B C)) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o C))"
    by (rule grk_K[OF grk_ImpD1[OF bct] grk_ImpD2[OF bct]])
  show ?thesis by (rule grk_imp_trans[OF s1 s2])
qed

lemma grk_box_iff:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o A \<longleftrightarrow>\<^sub>o \<box>\<^sub>o B)"
  by (rule grk_iff_intro[OF grk_box_mono[OF grk_conj1[OF d]]
        grk_box_mono[OF grk_conj2[OF d]]])

text \<open>A boxed branch that implies \<open>Q\<close> as a theorem implies \<open>\<box>Q\<close>.\<close>

lemma grk_box_stable:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) Q"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o Q)"
proof -
  have bt: "\<Gamma> \<turnstile> \<box>\<^sub>o A : Prop" by (rule grk_imp_ty1[OF d])
  have at: "\<Gamma> \<turnstile> A : Prop"
    using bt by (auto simp: ObjBox_def elim: has_type.cases)
  show ?thesis by (rule grk_imp_trans[OF grk_4[OF at] grk_box_mono[OF d]])
qed

section \<open>Quantifiers\<close>

lemma grk_UI:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall \<sigma> A) (subst0 M A)"
  by (rule CEV_axiom_proves.Base)
    (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI assms)

lemma grk_EG:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (subst0 M A) (Exists \<sigma> A)"
  by (rule CEV_axiom_proves.Base)
    (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG assms)

lemma grk_gen_imp:
  assumes pt: "\<Gamma> \<turnstile> P : Prop"
    and d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (Forall \<sigma> Q)"
  by (rule CEV_axiom_proves.Gen[OF pt grk_imp_ty2[OF d] d])

lemma grk_gen:
  assumes d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Q"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall \<sigma> Q"
proof -
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) Q"
    using CEV_axiom_imp_of_right[OF typed_ObjTrue d] by simp
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Forall \<sigma> Q)"
    by (rule grk_gen_imp[OF typed_ObjTrue])
  then show ?thesis by (rule grk_MP[OF CEV_axiom_proves_ObjTrue])
qed

lemma grk_inst_imp:
  assumes qt: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> P) Q"
  by (rule CEV_axiom_proves.Inst[OF grk_imp_ty1[OF d] qt d])

section \<open>Beta conversion\<close>

lemma grk_beta:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  by (rule CEV_axiom_proves.Base)
    (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Beta assms)

lemma grk_beta1:
  assumes ty: "\<Gamma> \<turnstile> App (Lam \<sigma> M) N : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam \<sigma> M) N \<longleftrightarrow>\<^sub>o subst0 N M)"
proof (rule grk_beta[OF ty])
  show "\<Gamma> \<turnstile> subst0 N M : Prop"
    by (rule beta_contract_preserves_typing[OF beta_contract.beta ty])
  show "compatible_step beta_contract (App (Lam \<sigma> M) N) (subst0 N M)"
    by (rule compatible_step.root, rule beta_contract.beta)
qed

lemma grk_beta2:
  assumes ty: "\<Gamma> \<turnstile> App (App (Lam \<sigma> (Lam \<tau> M)) N) P : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    (App (App (Lam \<sigma> (Lam \<tau> M)) N) P \<longleftrightarrow>\<^sub>o
      subst0 P (subst (lift_subst (case_nat N Var)) M))"
proof -
  let ?M' = "subst (lift_subst (case_nat N Var)) M"
  have red: "subst0 N (Lam \<tau> M) = Lam \<tau> ?M'"
    by (simp add: subst0_def)
  obtain \<rho> where ft: "\<Gamma> \<turnstile> App (Lam \<sigma> (Lam \<tau> M)) N : \<rho> \<rightarrow>\<^sub>o Prop"
    and pt: "\<Gamma> \<turnstile> P : \<rho>"
    using ty by (auto elim: has_type.cases)
  have ft': "\<Gamma> \<turnstile> Lam \<tau> ?M' : \<rho> \<rightarrow>\<^sub>o Prop"
    using beta_contract_preserves_typing[OF beta_contract.beta ft] red by simp
  have mid: "\<Gamma> \<turnstile> App (Lam \<tau> ?M') P : Prop"
    by (rule has_type.App[OF ft' pt])
  have s1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App (App (Lam \<sigma> (Lam \<tau> M)) N) P \<longleftrightarrow>\<^sub>o App (Lam \<tau> ?M') P)"
  proof (rule grk_beta[OF ty mid])
    have "compatible_step beta_contract
        (App (App (Lam \<sigma> (Lam \<tau> M)) N) P) (App (subst0 N (Lam \<tau> M)) P)"
      by (intro compatible_step.App_left compatible_step.root beta_contract.beta)
    then show "compatible_step beta_contract
        (App (App (Lam \<sigma> (Lam \<tau> M)) N) P) (App (Lam \<tau> ?M') P)"
      by (simp only: red)
  qed
  have s2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (Lam \<tau> ?M') P \<longleftrightarrow>\<^sub>o subst0 P ?M')"
    by (rule grk_beta1[OF mid])
  show ?thesis by (rule grk_iff_trans[OF s1 s2])
qed

section \<open>Identity\<close>

lemma grk_iff_eq:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A B"
proof -
  have it: "\<Gamma> \<turnstile> Imp A B : Prop" by (rule grk_ConjD1[OF grk_ty[OF d]])
  show ?thesis
    by (rule CEV_axiom_zeroary_equivalence[OF grk_ImpD1[OF it] grk_ImpD2[OF it] d])
qed

lemma grk_LL:
  assumes "\<Gamma> \<turnstile> A : \<sigma>" and "\<Gamma> \<turnstile> B : \<sigma>" and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))"
  by (rule CEV_axiom_proves.Base)
    (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL assms)

lemma grk_eq_sym:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
  by (rule CEV_axiom_proves.Base[OF CEV_eq_sym[OF assms]])

lemma grk_eq_trans:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "\<Gamma> \<turnstile> N : \<sigma>" and "\<Gamma> \<turnstile> P : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
  by (rule CEV_axiom_proves.Base[OF CEV_eq_trans[OF assms]])

lemma grk_eq_app:
  assumes "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and "\<Gamma> \<turnstile> A : \<sigma>" and "\<Gamma> \<turnstile> B : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq \<sigma> A B) (Eq \<tau> (App F A) (App F B))"
  by (rule CEV_axiom_proves.Base[OF CEV_eq_app_right[OF assms]])

lemma grk_eq_imp:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop A B) (Imp A B)"
proof -
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop A B) (Imp (App prop_id A) (App prop_id B))"
    by (rule grk_LL[OF at bt typed_prop_id])
  have i1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (App prop_id A)"
    by (rule CEV_axiom_proves.Base[OF CEV_imp_app_prop_id[OF at]])
  have i2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (App prop_id B) B"
    by (rule CEV_axiom_proves.Base[OF CEV_app_prop_id_imp[OF bt]])
  have ct: "\<Gamma> \<turnstile> Imp (Eq Prop A B) (Imp A B) : Prop"
    by (intro gr_ty at bt)
  show ?thesis by (rule grk_PC3[OF ll i1 i2 ct]) gr_taut
qed

lemma grk_eq_iff:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop A B) (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have ct: "\<Gamma> \<turnstile> Imp (Eq Prop A B) (A \<longleftrightarrow>\<^sub>o B) : Prop"
    by (intro gr_ty at bt)
  show ?thesis
    by (rule grk_PC3[OF grk_eq_imp[OF at bt] grk_eq_sym[OF at bt]
          grk_eq_imp[OF bt at] ct]) gr_taut
qed

text \<open>Identity of propositions from their necessary equivalence.\<close>

lemma grk_box_iff_eq:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (A \<longleftrightarrow>\<^sub>o B)) (Eq Prop A B)"
proof -
  let ?E = "(A \<longleftrightarrow>\<^sub>o B)"
  let ?F = "Lam Prop (Eq Prop (Conj (shift A) (Var 0)) (Conj (shift B) (Var 0)))"
  let ?AT = "Conj A ObjTrue"
  let ?BT = "Conj B ObjTrue"
  have et: "\<Gamma> \<turnstile> ?E : Prop" by (intro gr_ty at bt)
  have att: "\<Gamma> \<turnstile> ?AT : Prop" by (intro gr_ty at)
  have btt: "\<Gamma> \<turnstile> ?BT : Prop" by (intro gr_ty bt)
  have ft: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam gr_ty at bt)
  have ll: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop ?E ObjTrue) (Imp (App ?F ?E) (App ?F ObjTrue))"
    by (rule grk_LL[OF et typed_ObjTrue ft])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F ?E \<longleftrightarrow>\<^sub>o
      subst0 ?E (Eq Prop (Conj (shift A) (Var 0)) (Conj (shift B) (Var 0))))"
    by (rule grk_beta1[OF has_type.App[OF ft et]])
  then have b1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      (App ?F ?E \<longleftrightarrow>\<^sub>o Eq Prop (Conj A ?E) (Conj B ?E))"
    by (simp add: grs)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F ObjTrue \<longleftrightarrow>\<^sub>o
      subst0 ObjTrue (Eq Prop (Conj (shift A) (Var 0)) (Conj (shift B) (Var 0))))"
    by (rule grk_beta1[OF has_type.App[OF ft typed_ObjTrue]])
  then have b2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F ObjTrue \<longleftrightarrow>\<^sub>o Eq Prop ?AT ?BT)"
    by (simp add: grs)
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Conj A ?E) (Conj B ?E)"
  proof (rule grk_iff_eq, rule grk_taut)
    show "\<Gamma> \<turnstile> (Conj A ?E \<longleftrightarrow>\<^sub>o Conj B ?E) : Prop" by (intro gr_ty at bt)
  qed gr_taut
  have a1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A ?AT"
  proof (rule grk_iff_eq, rule grk_PC1[OF CEV_axiom_proves_ObjTrue])
    show "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o ?AT) : Prop" by (intro gr_ty at)
  qed gr_taut
  have a2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?BT B"
  proof (rule grk_iff_eq, rule grk_PC1[OF CEV_axiom_proves_ObjTrue])
    show "\<Gamma> \<turnstile> (?BT \<longleftrightarrow>\<^sub>o B) : Prop" by (intro gr_ty bt)
  qed gr_taut
  have t1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop A ?AT) (Imp (Eq Prop ?AT ?BT) (Eq Prop A ?BT))"
    by (rule grk_eq_trans[OF at att btt])
  have t2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Eq Prop A ?BT) (Imp (Eq Prop ?BT B) (Eq Prop A B))"
    by (rule grk_eq_trans[OF at btt bt])
  have mid_ty: "\<Gamma> \<turnstile> Imp (Eq Prop ?E ObjTrue) (Eq Prop ?AT ?BT) : Prop"
    by (intro gr_ty at bt)
  have mid: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop ?E ObjTrue) (Eq Prop ?AT ?BT)"
    by (rule grk_PC4[OF ll b1 b2 e1 mid_ty]) gr_taut
  have fin_ty: "\<Gamma> \<turnstile> Imp (Eq Prop ?E ObjTrue) (Eq Prop A B) : Prop"
    by (intro gr_ty at bt)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop ?E ObjTrue) (Eq Prop A B)"
    by (rule grk_PC5[OF mid a1 a2 t1 t2 fin_ty]) gr_taut
  then show ?thesis by (simp only: ObjBox_def)
qed

section \<open>A typing method with backtracking\<close>

text \<open>
  Class-level application (\<open>\<Z>(Y)\<close>, with \<open>\<Z> : (t \<rightarrow> t) \<rightarrow> t\<close>) and
  operator-level application (\<open>Yp\<close>) both have type \<open>Prop\<close>, so typing goals
  need search.  \<open>gr_typ\<close> is a depth-first search with backtracking over the
  collection \<open>gr_ty\<close> and the facts given to it.
\<close>

abbreviation gr_cls :: otype where
  "gr_cls \<equiv> gr_u \<rightarrow>\<^sub>o Prop"

lemma grk_cls_app_ty:
  "\<Gamma> \<turnstile> Z : gr_cls \<Longrightarrow> \<Gamma> \<turnstile> Y : gr_u \<Longrightarrow> \<Gamma> \<turnstile> App Z Y : Prop"
  by (rule has_type.App)

lemma typed_var1: "s0 # s1 # \<Gamma> \<turnstile> Var (Suc 0) : s1"
  by simp

lemma typed_var2: "s0 # s1 # s2 # \<Gamma> \<turnstile> Var (Suc (Suc 0)) : s2"
  by simp

lemma typed_var3: "s0 # s1 # s2 # s3 # \<Gamma> \<turnstile> Var (Suc (Suc (Suc 0))) : s3"
  by simp

lemmas [gr_ty] =
  has_type.Lam grk_cls_app_ty typed_var1 typed_var2 typed_var3 typed_pp_Pure typed_pp_pure

method_setup gr_typ = \<open>
  Attrib.thms >> (fn ths => fn ctxt =>
    let
      val rules = ths @ Named_Theorems.get ctxt @{named_theorems gr_ty}
      fun solve i =
        SOLVED' (assume_tac ctxt ORELSE' (resolve_tac ctxt rules THEN_ALL_NEW solve)) i
    in SIMPLE_METHOD' solve end)
\<close> "typing goals: depth-first search with backtracking over gr_ty and the given facts"

lemma grk_EqD1: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop \<Longrightarrow> \<Gamma> \<turnstile> M : \<sigma>"
  by (auto elim: has_type.cases)

lemma grk_EqD2: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma>"
  by (auto elim: has_type.cases)

lemma grk_ExistsD: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> A : Prop"
  by (auto elim: has_type.cases)

section \<open>Further truth-functional unfoldings\<close>

lemma grk_ObjFalse_eval[gr_eval]: "prop_eval v ObjFalse = (\<not> prop_eval v ObjTrue)"
  by (simp add: ObjFalse_def)

lemma grk_pp_pure_eval[gr_eval]: "prop_eval v (pp_pure \<sigma> M) = v (App (pp_Pure \<sigma>) M)"
  by (simp add: pp_pure_def)

section \<open>Identity, continued\<close>

lemma grk_eq_sym_rule:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> M N"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> N M"
  by (rule grk_MP[OF d grk_eq_sym[OF grk_EqD1[OF grk_ty[OF d]] grk_EqD2[OF grk_ty[OF d]]]])

lemma grk_eq_trans_rule:
  assumes d1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> M N" and d2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> N P"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq \<sigma> M P"
  by (rule grk_MP[OF d2 grk_MP[OF d1
        grk_eq_trans[OF grk_EqD1[OF grk_ty[OF d1]] grk_EqD2[OF grk_ty[OF d1]]
          grk_EqD2[OF grk_ty[OF d2]]]]])

text \<open>Double negation as an identity.\<close>

lemma grk_DN:
  assumes pt: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Neg (Neg p)) p"
  by (rule grk_iff_eq, rule grk_taut) (gr_typ pt, gr_taut)

text \<open>Substitution of identicals in the right conjunct.\<close>

lemma grk_eq_conj_right:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop" and ct: "\<Gamma> \<turnstile> C : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop A B) (Eq Prop (Conj C A) (Conj C B))"
proof -
  let ?F = "Lam Prop (Conj (shift C) (Var 0))"
  have ft: "\<Gamma> \<turnstile> ?F : gr_u" by (gr_typ ct)
  have app: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop A B) (Eq Prop (App ?F A) (App ?F B))"
    by (rule grk_eq_app[OF ft at bt])
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F A \<longleftrightarrow>\<^sub>o subst0 A (Conj (shift C) (Var 0)))"
    by (rule grk_beta1[OF has_type.App[OF ft at]])
  then have ba: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F A \<longleftrightarrow>\<^sub>o Conj C A)" by (simp add: grs)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F B \<longleftrightarrow>\<^sub>o subst0 B (Conj (shift C) (Var 0)))"
    by (rule grk_beta1[OF has_type.App[OF ft bt]])
  then have bb: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (App ?F B \<longleftrightarrow>\<^sub>o Conj C B)" by (simp add: grs)
  have e1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Conj C A) (App ?F A)"
    by (rule grk_iff_eq[OF grk_iff_sym[OF ba]])
  have e2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App ?F B) (Conj C B)"
    by (rule grk_iff_eq[OF bb])
  have t1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop (Conj C A) (App ?F A))
      (Imp (Eq Prop (App ?F A) (App ?F B)) (Eq Prop (Conj C A) (App ?F B)))"
    by (rule grk_eq_trans) (gr_typ at bt ct ft)+
  have t2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq Prop (Conj C A) (App ?F B))
      (Imp (Eq Prop (App ?F B) (Conj C B)) (Eq Prop (Conj C A) (Conj C B)))"
    by (rule grk_eq_trans) (gr_typ at bt ct ft)+
  have ty: "\<Gamma> \<turnstile> Imp (Eq Prop A B) (Eq Prop (Conj C A) (Conj C B)) : Prop"
    by (gr_typ at bt ct)
  show ?thesis by (rule grk_PC5[OF app e1 e2 t1 t2 ty]) gr_taut
qed

section \<open>S4, continued\<close>

lemma grk_box_mono3:
  assumes d: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp B (Imp C D))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (Imp (\<box>\<^sub>o C) (\<box>\<^sub>o D)))"
proof -
  have t1: "\<Gamma> \<turnstile> Imp B (Imp C D) : Prop" by (rule grk_imp_ty2[OF d])
  have t2: "\<Gamma> \<turnstile> Imp C D : Prop" by (rule grk_ImpD2[OF t1])
  have s1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o (Imp C D)))"
    by (rule grk_box_mono2[OF d])
  have s2: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Imp C D)) (Imp (\<box>\<^sub>o C) (\<box>\<^sub>o D))"
    by (rule grk_K[OF grk_ImpD1[OF t2] grk_ImpD2[OF t2]])
  have ty: "\<Gamma> \<turnstile> Imp (\<box>\<^sub>o A) (Imp (\<box>\<^sub>o B) (Imp (\<box>\<^sub>o C) (\<box>\<^sub>o D))) : Prop"
    by (gr_typ grk_imp_ty1[OF d] grk_ImpD1[OF t1] grk_ImpD1[OF t2] grk_ImpD2[OF t2])
  show ?thesis by (rule grk_PC2[OF s1 s2 ty]) gr_taut
qed

text \<open>The S4 theorem \<open>\<box>A \<or> \<box>B \<rightarrow> \<box>(\<box>A \<or> \<box>B)\<close>.\<close>

lemma grk_box_disj_stable:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Disj (\<box>\<^sub>o A) (\<box>\<^sub>o B)) (\<box>\<^sub>o (Disj (\<box>\<^sub>o A) (\<box>\<^sub>o B)))"
proof -
  let ?D = "Disj (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) ?D"
    by (rule grk_taut) (gr_typ at bt, gr_taut)
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o B) ?D"
    by (rule grk_taut) (gr_typ at bt, gr_taut)
  have a': "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o A) (\<box>\<^sub>o ?D)" by (rule grk_box_stable[OF a])
  have b': "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o B) (\<box>\<^sub>o ?D)" by (rule grk_box_stable[OF b])
  have ty: "\<Gamma> \<turnstile> Imp ?D (\<box>\<^sub>o ?D) : Prop" by (gr_typ at bt)
  show ?thesis by (rule grk_PC2[OF a' b' ty]) gr_taut
qed

text \<open>Universal instantiation inside the box.\<close>

lemma grk_boxed_UI:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (\<box>\<^sub>o (Forall \<sigma> A)) (\<box>\<^sub>o (subst0 M A))"
  by (rule grk_box_mono[OF grk_UI[OF assms]])

section \<open>Quantifiers, continued: eigenvariable reasoning\<close>

lemma grk_shift_Forall: "shift (Forall \<sigma> A) = Forall \<sigma> (rename (lift_ren Suc) A)"
  by (simp add: shift_def)

lemma grk_shift_Exists: "shift (Exists \<sigma> A) = Exists \<sigma> (rename (lift_ren Suc) A)"
  by (simp add: shift_def)

lemma grk_subst0_Forall:
  "subst0 M (Forall \<sigma> A) = Forall \<sigma> (subst (lift_subst (case_nat M Var)) A)"
  by (simp add: subst0_def)

lemma grk_subst0_Exists:
  "subst0 M (Exists \<sigma> A) = Exists \<sigma> (subst (lift_subst (case_nat M Var)) A)"
  by (simp add: subst0_def)

text \<open>
  After a quantified formula has been shifted into the context of its own
  variable, it can be instantiated at (resp. witnessed by) that variable.
\<close>

lemma grk_UI_var:
  assumes at: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (Forall \<sigma> A)) A"
proof -
  have ft: "\<sigma> # \<Gamma> \<turnstile> shift (Forall \<sigma> A) : Prop"
    by (rule typed_shift_ctx[OF has_type.Forall[OF at]])
  have bt: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : Prop"
    by (rule grk_ForallD[OF ft[unfolded grk_shift_Forall]])
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Forall \<sigma> (rename (lift_ren Suc) A)) (subst0 (Var 0) (rename (lift_ren Suc) A))"
    by (rule grk_UI[OF bt typed_var0])
  then show ?thesis by (simp add: grk_shift_Forall)
qed

lemma grk_EG_var:
  assumes at: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (shift (Exists \<sigma> A))"
proof -
  have ft: "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    by (rule typed_shift_ctx[OF has_type.Exists[OF at]])
  have bt: "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : Prop"
    by (rule grk_ExistsD[OF ft[unfolded grk_shift_Exists]])
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (subst0 (Var 0) (rename (lift_ren Suc) A)) (Exists \<sigma> (rename (lift_ren Suc) A))"
    by (rule grk_EG[OF bt typed_var0])
  then show ?thesis by (simp add: grk_shift_Exists)
qed

text \<open>Monotonicity of the quantifiers under a hypothesis not mentioning the variable.\<close>

lemma grk_forall_mono_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift H) (Imp A B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (Imp (Forall \<sigma> A) (Forall \<sigma> B))"
proof -
  have abt: "\<sigma> # \<Gamma> \<turnstile> Imp A B : Prop" by (rule grk_imp_ty2[OF d])
  have at: "\<sigma> # \<Gamma> \<turnstile> A : Prop" by (rule grk_ImpD1[OF abt])
  have bt: "\<sigma> # \<Gamma> \<turnstile> B : Prop" by (rule grk_ImpD2[OF abt])
  let ?P = "Conj H (Forall \<sigma> A)"
  have pt: "\<Gamma> \<turnstile> ?P : Prop" by (gr_typ ht at)
  have ui: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift (Forall \<sigma> A)) A" by (rule grk_UI_var[OF at])
  have ty1: "\<sigma> # \<Gamma> \<turnstile> Imp (Conj (shift H) (shift (Forall \<sigma> A))) B : Prop"
    by (gr_typ ht at bt)
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Conj (shift H) (shift (Forall \<sigma> A))) B"
    by (rule grk_PC2[OF d ui ty1]) gr_taut
  then have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ?P) B" by (simp add: grk_shift_simps)
  then have g: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?P (Forall \<sigma> B)" by (rule grk_gen_imp[OF pt])
  have ty: "\<Gamma> \<turnstile> Imp H (Imp (Forall \<sigma> A) (Forall \<sigma> B)) : Prop" by (gr_typ ht at bt)
  show ?thesis by (rule grk_PC1[OF g ty]) gr_taut
qed

lemma grk_exists_mono_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop"
    and d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift H) (Imp A B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (Imp (Exists \<sigma> A) (Exists \<sigma> B))"
proof -
  have abt: "\<sigma> # \<Gamma> \<turnstile> Imp A B : Prop" by (rule grk_imp_ty2[OF d])
  have at: "\<sigma> # \<Gamma> \<turnstile> A : Prop" by (rule grk_ImpD1[OF abt])
  have bt: "\<sigma> # \<Gamma> \<turnstile> B : Prop" by (rule grk_ImpD2[OF abt])
  let ?Q = "Imp H (Exists \<sigma> B)"
  have qt: "\<Gamma> \<turnstile> ?Q : Prop" by (gr_typ ht bt)
  have eg: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B (shift (Exists \<sigma> B))" by (rule grk_EG_var[OF bt])
  have ty1: "\<sigma> # \<Gamma> \<turnstile> Imp A (Imp (shift H) (shift (Exists \<sigma> B))) : Prop"
    by (gr_typ ht at bt)
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp (shift H) (shift (Exists \<sigma> B)))"
    by (rule grk_PC2[OF d eg ty1]) gr_taut
  then have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (shift ?Q)" by (simp add: grk_shift_simps)
  then have i: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> A) ?Q" by (rule grk_inst_imp[OF qt])
  have ty: "\<Gamma> \<turnstile> Imp H (Imp (Exists \<sigma> A) (Exists \<sigma> B)) : Prop" by (gr_typ ht at bt)
  show ?thesis by (rule grk_PC1[OF i ty]) gr_taut
qed

text \<open>Existential elimination under a hypothesis.\<close>

lemma grk_exists_E_imp:
  assumes ht: "\<Gamma> \<turnstile> H : Prop" and qt: "\<Gamma> \<turnstile> Q : Prop"
    and d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift H) (Imp A (shift Q))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp H (Imp (Exists \<sigma> A) Q)"
proof -
  have at: "\<sigma> # \<Gamma> \<turnstile> A : Prop" by (rule grk_ImpD1[OF grk_imp_ty2[OF d]])
  let ?Q = "Imp H Q"
  have qt': "\<Gamma> \<turnstile> ?Q : Prop" by (gr_typ ht qt)
  have ty1: "\<sigma> # \<Gamma> \<turnstile> Imp A (Imp (shift H) (shift Q)) : Prop" by (gr_typ ht qt at)
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp (shift H) (shift Q))"
    by (rule grk_PC1[OF d ty1]) gr_taut
  then have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (shift ?Q)" by (simp add: grk_shift_simps)
  then have i: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> A) ?Q" by (rule grk_inst_imp[OF qt'])
  have ty: "\<Gamma> \<turnstile> Imp H (Imp (Exists \<sigma> A) Q) : Prop" by (gr_typ ht qt at)
  show ?thesis by (rule grk_PC1[OF i ty]) gr_taut
qed

text \<open>Hypothesis-free versions.\<close>

lemma grk_forall_mono:
  assumes d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Forall \<sigma> A) (Forall \<sigma> B)"
proof -
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) (Imp A B)"
    using CEV_axiom_imp_of_right[OF typed_ObjTrue d] by simp
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Imp (Forall \<sigma> A) (Forall \<sigma> B))"
    by (rule grk_forall_mono_imp[OF typed_ObjTrue])
  then show ?thesis by (rule grk_MP[OF CEV_axiom_proves_ObjTrue])
qed

lemma grk_exists_mono:
  assumes d: "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> A) (Exists \<sigma> B)"
proof -
  have "\<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) (Imp A B)"
    using CEV_axiom_imp_of_right[OF typed_ObjTrue d] by simp
  then have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Imp (Exists \<sigma> A) (Exists \<sigma> B))"
    by (rule grk_exists_mono_imp[OF typed_ObjTrue])
  then show ?thesis by (rule grk_MP[OF CEV_axiom_proves_ObjTrue])
qed

end
