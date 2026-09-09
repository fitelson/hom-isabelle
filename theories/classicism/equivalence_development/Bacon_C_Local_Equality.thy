theory Bacon_C_Local_Equality
  imports Bacon_Classicism.Bacon_S4
begin

section \<open>Axiom-based local deduction and equality\<close>

text \<open>
  ⊢C M =σ N concerns identity of terms of type σ; ⊢C P ↔ Q concerns
  material equivalence of propositions.  We first establish the local
  deduction and identity laws used in Bacon--Dorr Appendix A, pp.65–67,
  and Bacon, Theorem 6.1, printed p.126.

  Isabelle representation.  C_proves is the axiom-based calculus C.
  Write ⊤₀ := ∀p.(p → p) for its chosen term ObjTrue.  The typing context
  Γ records variable types, not additional object-language assumptions.

  Status.  The arguments below use C alone.  Importing the surrounding
  development does not license the Equivalence rules of CE or CEV, and
  neither rule nor a necessitation theorem is used in these proofs.
\<close>

subsection \<open>Propositional reasoning in C\<close>

text \<open>
  ⊢C P for every classical tautology P; ⊢C A and ⊢C B yield ⊢C A ∧ B.
  Source: Bacon--Dorr Figure 2, p.8, PC and MP.

  Isabelle representation.  prop_tautology checks the displayed Boolean
  skeleton.  C_closure_proves_ObjTrue imports the H proof of ⊤₀.
  Status.  These are truth-theorems, not equations identifying all true propositions.
\<close>

lemma C_closure_prop_tautology:
  assumes "prop_tautology \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
  using assms by (intro C_proves.H H_proves.PC)

lemma C_closure_proves_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>C ObjTrue"
  by (intro C_proves.H H_proves_ObjTrue)

lemma C_closure_imp_of_right_theorem:
  assumes "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile>\<^sub>C B"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule C_proves_formula)
  have taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
    unfolding prop_tautology_def using assms(1) B_type by auto
  have "\<Gamma> \<turnstile>\<^sub>C Imp B (Imp A B)"
    by (rule C_closure_prop_tautology[OF taut])
  then show ?thesis by (rule C_proves.MP[OF assms(2)])
qed

lemma C_closure_conj_intro:
  assumes "\<Gamma> \<turnstile>\<^sub>C A" and "\<Gamma> \<turnstile>\<^sub>C B"
  shows "\<Gamma> \<turnstile>\<^sub>C Conj A B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule C_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule C_proves_formula)
  have taut: "prop_tautology \<Gamma> (Imp A (Imp B (Conj A B)))"
    using A_type B_type by (rule prop_tautology_conj_intro)
  have "\<Gamma> \<turnstile>\<^sub>C Imp A (Imp B (Conj A B))"
    by (rule C_closure_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>C Imp B (Conj A B)"
    by (rule C_proves.MP[OF assms(1)])
  then show ?thesis by (rule C_proves.MP[OF assms(2)])
qed

lemmas C_closure_beta_step = C_beta_step

subsection \<open>Local assumptions, deduction, and equality laws\<close>

text \<open>
  If A ⊢C B by assumptions, C theorems, and modus ponens, then ⊢C A → B.
  Sources: Bacon--Dorr Figure 2, p.8, PC and MP; Appendix A.2, pp.65–67,
  for the later proof-induction use of local implications.

  Isabelle representation.  C_closure_from Γ A B is this auxiliary
  one-assumption consequence relation.  It is not C_proves in a larger
  type context and has no local generalization or Equivalence constructor.

  Status.  The deduction theorem therefore discharges only these local
  assumptions.  It does not internalize theorem-level Equivalence or a
  quantifier rule beneath an arbitrary antecedent.
\<close>

inductive C_closure_from :: "ctx \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  Assumption[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> C_closure_from \<Gamma> A A"
| Theorem[intro]: "\<Gamma> \<turnstile>\<^sub>C B \<Longrightarrow> C_closure_from \<Gamma> A B"
| MP[intro]: "C_closure_from \<Gamma> A B \<Longrightarrow>
    C_closure_from \<Gamma> A (Imp B C) \<Longrightarrow> C_closure_from \<Gamma> A C"

lemma C_closure_from_formula:
  assumes "C_closure_from \<Gamma> A B"
  shows "\<Gamma> \<turnstile> B : Prop"
  using assms
proof (induction rule: C_closure_from.induct)
  case (Assumption \<Gamma> A)
  then show ?case
    by simp
next
  case (Theorem \<Gamma> B A)
  then show ?case
    by (rule C_proves_formula)
next
  case (MP \<Gamma> A B C)
  then show ?case
    by (auto elim: has_type.cases)
qed

lemma C_closure_from_deduction:
  assumes "C_closure_from \<Gamma> A B"
  shows "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>C Imp A B"
  using assms
proof (induction rule: C_closure_from.induct)
  case Assumption
  then show ?case
    by (intro C_closure_prop_tautology prop_tautology_imp_self)
next
  case Theorem
  show ?case
    by (rule C_closure_imp_of_right_theorem[OF Theorem.prems Theorem.hyps])
next
  case (MP \<Gamma> A B C)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using MP.hyps(1) by (rule C_closure_from_formula)
  have imp_type: "\<Gamma> \<turnstile> Imp B C : Prop"
    using MP.hyps(2) by (rule C_closure_from_formula)
  have C_type: "\<Gamma> \<turnstile> C : Prop"
    using imp_type by (auto elim: has_type.cases)
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C)))"
    unfolding prop_tautology_def
    using MP.prems B_type C_type imp_type by auto
  have "\<Gamma> \<turnstile>\<^sub>C Imp (Imp A B) (Imp (Imp A (Imp B C)) (Imp A C))"
    by (rule C_closure_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>C Imp (Imp A (Imp B C)) (Imp A C)"
    by (rule C_proves.MP[OF MP.IH(1)[OF MP.prems]])
  then show ?case
    by (rule C_proves.MP[OF MP.IH(2)[OF MP.prems]])
qed

lemma C_closure_from_local_MP:
  assumes "C_closure_from \<Gamma> A B"
    and "C_closure_from \<Gamma> A (Imp B C)"
  shows "C_closure_from \<Gamma> A C"
  using assms by (rule C_closure_from.MP)

lemma C_closure_taut_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A (Imp B A)"
proof -
  have "prop_tautology \<Gamma> (Imp A (Imp B A))"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule C_closure_prop_tautology)
qed

lemma C_closure_conj_left_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Conj A B) A"
proof -
  have "prop_tautology \<Gamma> (Imp (Conj A B) A)"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule C_closure_prop_tautology)
qed

lemma C_closure_conj_right_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Conj A B) B"
proof -
  have "prop_tautology \<Gamma> (Imp (Conj A B) B)"
    unfolding prop_tautology_def
    using assms by auto
  then show ?thesis
    by (rule C_closure_prop_tautology)
qed

lemma C_closure_uncurry_conj:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "\<Gamma> \<turnstile> R : Prop"
    and "\<Gamma> \<turnstile>\<^sub>C Imp (Conj P Q) R"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp P (Imp Q R)"
proof -
  have imp_type: "\<Gamma> \<turnstile> Imp (Conj P Q) R : Prop"
    using assms(1) assms(2) assms(3) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (Imp (Conj P Q) R) (Imp P (Imp Q R)))"
    unfolding prop_tautology_def
    using assms(1) assms(2) assms(3) imp_type by auto
  have "\<Gamma> \<turnstile>\<^sub>C Imp (Imp (Conj P Q) R) (Imp P (Imp Q R))"
    by (rule C_closure_prop_tautology[OF taut])
  then show ?thesis
    by (rule C_proves.MP[OF assms(4)])
qed

text \<open>
  From ⊢C P ↔ Q we may use either material implication; in particular,
  (λp.p)A ↔ A supplies the identity-predicate application used below.
  Source: Bacon--Dorr Figure 2, p.8, PC, MP, and β.

  Isabelle representation.  These helpers concern implication extraction
  and the term prop_id, not equality of arbitrary coextensive propositions.
  Status.  No CE or CEV Equivalence constructor is invoked.
\<close>

lemma C_closure_beta_left_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A B"
proof -
  have AB_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B))"
    unfolding prop_tautology_def
    using assms(1,2) AB_type by auto
  have "\<Gamma> \<turnstile>\<^sub>C Imp (A \<longleftrightarrow>\<^sub>o B) (Imp A B)"
    by (rule C_closure_prop_tautology[OF taut])
  then show ?thesis
    by (rule C_proves.MP[OF assms(3)])
qed

lemma C_closure_beta_right_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp B A"
proof -
  have AB_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A))"
    unfolding prop_tautology_def
    using assms(1,2) AB_type by auto
  have "\<Gamma> \<turnstile>\<^sub>C Imp (A \<longleftrightarrow>\<^sub>o B) (Imp B A)"
    by (rule C_closure_prop_tautology[OF taut])
  then show ?thesis
    by (rule C_proves.MP[OF assms(3)])
qed

lemma C_closure_beta_prop_id:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C (App prop_id A \<longleftrightarrow>\<^sub>o A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  have step: "compatible_step beta_contract (App prop_id A) A"
  proof -
    have "beta_contract (App (Lam Prop (Var 0)) A) (subst0 A (Var 0))"
      by (rule beta_contract.beta)
    then show ?thesis
      unfolding prop_id_def subst0_def by auto
  qed
  show ?thesis
    using app_type assms step by (rule C_closure_beta_step)
qed

lemma C_closure_app_prop_id_imp:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (App prop_id A) A"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  show ?thesis
    using app_type assms C_closure_beta_prop_id[OF assms]
    by (rule C_closure_beta_left_imp)
qed

lemma C_closure_imp_app_prop_id:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp A (App prop_id A)"
proof -
  have app_type: "\<Gamma> \<turnstile> App prop_id A : Prop"
    using assms typed_prop_id by auto
  show ?thesis
    using app_type assms C_closure_beta_prop_id[OF assms]
    by (rule C_closure_beta_right_imp)
qed

lemma C_closure_prop_id_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>C App prop_id ObjTrue"
proof -
  have true_type: "\<Gamma> \<turnstile> ObjTrue : Prop"
    by (rule typed_ObjTrue)
  have "\<Gamma> \<turnstile>\<^sub>C Imp ObjTrue (App prop_id ObjTrue)"
    using true_type by (rule C_closure_imp_app_prop_id)
  then show ?thesis
    by (rule C_proves.MP[OF C_closure_proves_ObjTrue])
qed

text \<open>
  ⊢C (M =σ N) → (N =σ M).
  Source: Bacon--Dorr Figure 2, p.8, Ref and LL.

  Isabelle representation.  LL is instantiated with λx:σ.(x =σ M);
  C_closure_from keeps the equality premise local until deduction.
  Status.  Symmetry is derived inside C, not supplied as an extra axiom.
\<close>

lemma C_closure_eq_sym:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
proof -
  let ?F = "Lam \<sigma> (Eq \<sigma> (Var 0) (shift M))"
  have shifted_M_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    using assms(1) by (rule weakening_front)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (Var 0) (shift M) : Prop"
    using shifted_M_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_M_type: "\<Gamma> \<turnstile> App ?F M : Prop"
    using F_type assms(1) by auto
  have app_N_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type assms(2) by auto
  have ref_M: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M M"
    using assms(1) by (intro C_proves.H H_proves.Ref)
  have beta_M: "\<Gamma> \<turnstile>\<^sub>C (App ?F M \<longleftrightarrow>\<^sub>o Eq \<sigma> M M)"
  proof -
    have target_type: "\<Gamma> \<turnstile> Eq \<sigma> M M : Prop"
      using assms(1) by auto
    have step: "compatible_step beta_contract (App ?F M) (Eq \<sigma> M M)"
    proof -
      have "compatible_step beta_contract (App ?F M)
          (subst0 M (Eq \<sigma> (Var 0) (shift M)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_M_type target_type step by (rule C_closure_beta_step)
  qed
  have app_M: "\<Gamma> \<turnstile>\<^sub>C App ?F M"
  proof -
    have "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M M) (App ?F M)"
      using app_M_type C_proves_formula[OF ref_M] beta_M
      by (rule C_closure_beta_right_imp)
    then show ?thesis
      by (rule C_proves.MP[OF ref_M])
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))"
    using assms(1,2) F_type
    by (intro C_proves.H H_proves.LL)
  have local_N: "C_closure_from \<Gamma> (Eq \<sigma> M N) (App ?F N)"
  proof -
    have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
      using assms by auto
    have local_E: "C_closure_from \<Gamma> (Eq \<sigma> M N) (Eq \<sigma> M N)"
      by (intro C_closure_from.Assumption E_type)
    have local_ll: "C_closure_from \<Gamma> (Eq \<sigma> M N)
        (Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N)))"
      by (intro C_closure_from.Theorem ll)
    have local_imp: "C_closure_from \<Gamma> (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))"
      by (rule C_closure_from.MP[OF local_E local_ll])
    have local_app_M: "C_closure_from \<Gamma> (Eq \<sigma> M N) (App ?F M)"
      by (intro C_closure_from.Theorem app_M)
    show ?thesis
      by (rule C_closure_from.MP[OF local_app_M local_imp])
  qed
  have local_sym: "C_closure_from \<Gamma> (Eq \<sigma> M N) (Eq \<sigma> N M)"
  proof -
    have target_type: "\<Gamma> \<turnstile> Eq \<sigma> N M : Prop"
      using assms by auto
    have beta_N: "\<Gamma> \<turnstile>\<^sub>C (App ?F N \<longleftrightarrow>\<^sub>o Eq \<sigma> N M)"
    proof -
      have step: "compatible_step beta_contract (App ?F N) (Eq \<sigma> N M)"
      proof -
        have "compatible_step beta_contract (App ?F N)
            (subst0 N (Eq \<sigma> (Var 0) (shift M)))"
          by (intro compatible_step.root beta_contract.beta)
        then show ?thesis
          by (simp add: subst0_def)
      qed
      show ?thesis
        using app_N_type target_type step by (rule C_closure_beta_step)
    qed
    have imp_sym: "\<Gamma> \<turnstile>\<^sub>C Imp (App ?F N) (Eq \<sigma> N M)"
      using app_N_type target_type beta_N by (rule C_closure_beta_left_imp)
    have local_imp_sym: "C_closure_from \<Gamma> (Eq \<sigma> M N) (Imp (App ?F N) (Eq \<sigma> N M))"
      by (intro C_closure_from.Theorem imp_sym)
    have "C_closure_from \<Gamma> (Eq \<sigma> M N) (App ?F N)"
      by (rule local_N)
    then show ?thesis
      by (rule C_closure_from.MP[OF _ local_imp_sym])
  qed
  have E_type: "\<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
    using assms by auto
  from local_sym E_type show ?thesis
    by (rule C_closure_from_deduction)
qed

lemma C_closure_eq_sym_from:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> N M"
proof -
  have "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Eq \<sigma> N M)"
    using assms(1,2) by (rule C_closure_eq_sym)
  then show ?thesis
    by (rule C_proves.MP[OF assms(3)])
qed

text \<open>
  ⊢C (M =σ N) → ((N =σ P) → (M =σ P)).
  Source: Bacon--Dorr Figure 2, p.8, Ref and LL.

  Isabelle representation.  A typed equality predicate and the local
  deduction theorem produce the implication chain.
  Status.  The following theorem-level wrapper requires both equality premises.
\<close>

lemma C_closure_eq_trans:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> P : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
proof -
  let ?E_MN = "Eq \<sigma> M N"
  let ?E_NP = "Eq \<sigma> N P"
  let ?E_MP = "Eq \<sigma> M P"
  let ?C = "Conj ?E_MN ?E_NP"
  let ?F = "Lam \<sigma> (Eq \<sigma> (shift M) (Var 0))"
  have shifted_M_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<sigma>"
    using assms(1) by (rule weakening_front)
  have body_type: "\<sigma> # \<Gamma> \<turnstile> Eq \<sigma> (shift M) (Var 0) : Prop"
    using shifted_M_type by auto
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using body_type by auto
  have app_N_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type assms(2) by auto
  have app_P_type: "\<Gamma> \<turnstile> App ?F P : Prop"
    using F_type assms(3) by auto
  have E_MN_type: "\<Gamma> \<turnstile> ?E_MN : Prop"
    using assms(1,2) by auto
  have E_NP_type: "\<Gamma> \<turnstile> ?E_NP : Prop"
    using assms(2,3) by auto
  have E_MP_type: "\<Gamma> \<turnstile> ?E_MP : Prop"
    using assms(1,3) by auto
  have beta_N: "\<Gamma> \<turnstile>\<^sub>C (App ?F N \<longleftrightarrow>\<^sub>o ?E_MN)"
  proof -
    have step: "compatible_step beta_contract (App ?F N) ?E_MN"
    proof -
      have "compatible_step beta_contract (App ?F N)
          (subst0 N (Eq \<sigma> (shift M) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_N_type E_MN_type step by (rule C_closure_beta_step)
  qed
  have beta_P: "\<Gamma> \<turnstile>\<^sub>C (App ?F P \<longleftrightarrow>\<^sub>o ?E_MP)"
  proof -
    have step: "compatible_step beta_contract (App ?F P) ?E_MP"
    proof -
      have "compatible_step beta_contract (App ?F P)
          (subst0 P (Eq \<sigma> (shift M) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis
        by (simp add: subst0_def)
    qed
    show ?thesis
      using app_P_type E_MP_type step by (rule C_closure_beta_step)
  qed
  have ll: "\<Gamma> \<turnstile>\<^sub>C Imp ?E_NP (Imp (App ?F N) (App ?F P))"
    using assms(2,3) F_type
    by (intro C_proves.H H_proves.LL)
  have local_MP: "C_closure_from \<Gamma> ?C ?E_MP"
  proof -
    have C_type: "\<Gamma> \<turnstile> ?C : Prop"
      using E_MN_type E_NP_type by auto
    have local_C: "C_closure_from \<Gamma> ?C ?C"
      by (intro C_closure_from.Assumption C_type)
    have left_imp: "\<Gamma> \<turnstile>\<^sub>C Imp ?C ?E_MN"
      using E_MN_type E_NP_type by (rule C_closure_conj_left_imp)
    have right_imp: "\<Gamma> \<turnstile>\<^sub>C Imp ?C ?E_NP"
      using E_MN_type E_NP_type by (rule C_closure_conj_right_imp)
    have local_MN: "C_closure_from \<Gamma> ?C ?E_MN"
      by (rule C_closure_from.MP[OF local_C C_closure_from.Theorem[OF left_imp]])
    have local_NP: "C_closure_from \<Gamma> ?C ?E_NP"
      by (rule C_closure_from.MP[OF local_C C_closure_from.Theorem[OF right_imp]])
    have imp_MN_app_N: "\<Gamma> \<turnstile>\<^sub>C Imp ?E_MN (App ?F N)"
      using app_N_type E_MN_type beta_N by (rule C_closure_beta_right_imp)
    have local_app_N: "C_closure_from \<Gamma> ?C (App ?F N)"
      by (rule C_closure_from.MP[OF local_MN C_closure_from.Theorem[OF imp_MN_app_N]])
    have local_app_imp: "C_closure_from \<Gamma> ?C (Imp (App ?F N) (App ?F P))"
      by (rule C_closure_from.MP[OF local_NP C_closure_from.Theorem[OF ll]])
    have local_app_P: "C_closure_from \<Gamma> ?C (App ?F P)"
      by (rule C_closure_from.MP[OF local_app_N local_app_imp])
    have imp_app_P_MP: "\<Gamma> \<turnstile>\<^sub>C Imp (App ?F P) ?E_MP"
      using app_P_type E_MP_type beta_P by (rule C_closure_beta_left_imp)
    show ?thesis
      by (rule C_closure_from.MP[OF local_app_P C_closure_from.Theorem[OF imp_app_P_MP]])
  qed
  have "\<Gamma> \<turnstile>\<^sub>C Imp ?C ?E_MP"
  proof (rule C_closure_from_deduction[OF local_MP])
    show "\<Gamma> \<turnstile> ?C : Prop"
      using E_MN_type E_NP_type by auto
  qed
  then show ?thesis
    by (rule C_closure_uncurry_conj[OF E_MN_type E_NP_type E_MP_type])
qed

lemma C_closure_eq_trans_from:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
    and "\<Gamma> \<turnstile> P : \<sigma>"
    and "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
    and "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> N P"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M P"
proof -
  have "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))"
    using assms(1) assms(2) assms(3) by (rule C_closure_eq_trans)
  then have "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<sigma> N P) (Eq \<sigma> M P)"
    by (rule C_proves.MP[OF assms(4)])
  then show ?thesis
    by (rule C_proves.MP[OF assms(5)])
qed

end
