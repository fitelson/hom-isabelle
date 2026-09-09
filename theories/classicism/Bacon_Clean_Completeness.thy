theory Bacon_Clean_Completeness
  imports Bacon_Clean_Canonical_Base
begin

section \<open>Unconditional Henkin completeness for H and C\<close>

text \<open>
  For each calculus X considered here, the endpoint reads: a typed formula
  is an X-theorem exactly when it belongs to every corresponding canonical
  theory.  The counterworld direction extends the consistent set containing
  the negation of an unprovable formula; the other direction uses closure
  under theorems.  Unconditional means that counterworld existence is proved
  here, not assumed as a completeness interface.

  This is syntactic membership semantics.  In the later Henkin endpoints,
  the worlds also contain witnesses for existential formulas.  They are not
  yet BBK models with an interpretation on arbitrary semantic assignments.
  Thus these results supply ingredients for Bacon--Dorr Theorem 3.2
  (pp. 44--45) and Bacon's Theorem 15.3 (pp. 320--321), not the complete
  action-model theorem, Bacon--Dorr Theorem 3.23 (p. 58).
\<close>

definition H_clean_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. H_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

definition C_clean_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. C_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

theorem H_clean_Henkin_valid_iff_proves:
  "H_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>H A"
proof
  assume valid: "H_clean_Henkin_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding H_clean_Henkin_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>H A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>H A"
    obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
      using enumerates_witness_bodies_exists by blast
    obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
      using enumerates_formulas_exists by blast
    obtain T where henkin: "H_Henkin_theory \<Gamma> T"
      and neg_in: "Neg A \<in> T"
      using A_type not_proves body_enum formula_enum
      by (rule H_canonical_Henkin_theory_for_unprovable_staged)
    have not_A: "A \<notin> T"
      using henkin A_type neg_in by (simp add: H_Henkin_neg_mem_iff)
    have "A \<in> T"
      using valid henkin unfolding H_clean_Henkin_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule H_proves_formula)
  have "\<And>T. H_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix T
    assume henkin: "H_Henkin_theory \<Gamma> T"
    show "A \<in> T"
      using henkin proves by (rule H_Henkin_contains_theorems)
  qed
  then show "H_clean_Henkin_valid_in_context \<Gamma> A"
    unfolding H_clean_Henkin_valid_in_context_def using A_type by blast
qed

theorem C_clean_Henkin_valid_iff_proves:
  "C_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>C A"
proof
  assume valid: "C_clean_Henkin_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding C_clean_Henkin_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>C A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>C A"
    obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
      using enumerates_witness_bodies_exists by blast
    obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
      using enumerates_formulas_exists by blast
    obtain T where henkin: "C_Henkin_theory \<Gamma> T"
      and neg_in: "Neg A \<in> T"
      using A_type not_proves body_enum formula_enum
      by (rule C_canonical_Henkin_theory_for_unprovable_staged)
    have not_A: "A \<notin> T"
      using henkin A_type neg_in by (simp add: C_Henkin_neg_mem_iff)
    have "A \<in> T"
      using valid henkin unfolding C_clean_Henkin_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule C_proves_formula)
  have "\<And>T. C_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix T
    assume henkin: "C_Henkin_theory \<Gamma> T"
    show "A \<in> T"
      using henkin proves by (rule C_Henkin_contains_theorems)
  qed
  then show "C_clean_Henkin_valid_in_context \<Gamma> A"
    unfolding C_clean_Henkin_valid_in_context_def using A_type by blast
qed

section \<open>Unconditional Lindenbaum completeness for clean CE and CEV\<close>

text \<open>
  The old semantic extension used a contextual equivalence rule.  The results
  below do not.  A canonical world is simply a typed, negation-complete set
  that is consistent for the relevant theorem relation.  This first
  completeness layer is proof-theoretic: truth at a canonical world is
  membership.  Henkin witnesses and the intended global quotient semantics
  are separate later obligations.
\<close>

definition CE_clean_canonical_world :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_clean_canonical_world \<Gamma> T \<longleftrightarrow>
    CE_locally_maximal_consistent \<Gamma> T"

definition CEV_clean_canonical_world :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_clean_canonical_world \<Gamma> T \<longleftrightarrow>
    CEV_locally_maximal_consistent \<Gamma> T"

definition CE_clean_canonical_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CE_clean_canonical_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CE_clean_canonical_world \<Gamma> T \<longrightarrow> A \<in> T)"

definition CEV_clean_canonical_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_clean_canonical_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CEV_clean_canonical_world \<Gamma> T \<longrightarrow> A \<in> T)"

lemma CE_clean_canonical_world_contains_theorems:
  assumes "CE_clean_canonical_world \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "A \<in> T"
  using assms
  unfolding CE_clean_canonical_world_def
  by (rule CE_locally_maximal_consistent_contains_theorems)

lemma CEV_clean_canonical_world_contains_theorems:
  assumes "CEV_clean_canonical_world \<Gamma> T"
    and "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "A \<in> T"
  using assms
  unfolding CEV_clean_canonical_world_def
  by (rule CEV_locally_maximal_consistent_contains_theorems)

theorem CE_clean_canonical_valid_iff_proves:
  "CE_clean_canonical_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>CE A"
proof
  assume valid: "CE_clean_canonical_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CE_clean_canonical_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>CE A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
    have initial_typed: "typed_theory \<Gamma> {Neg A}"
      unfolding typed_theory_def using A_type by auto
    have initial_consistent: "CE_consistent \<Gamma> {Neg A}"
      using A_type not_proves by (rule CE_consistent_singleton_neg_of_not_proves)
    obtain enum where enum: "enumerates_formulas \<Gamma> enum"
      using enumerates_formulas_exists by blast
    let ?T = "CE_lindenbaum_extension \<Gamma> {Neg A} enum"
    have world: "CE_clean_canonical_world \<Gamma> ?T"
      unfolding CE_clean_canonical_world_def
      using initial_typed initial_consistent enum
      by (rule CE_lindenbaum_extension_locally_maximal_consistent)
    have neg_in: "Neg A \<in> ?T"
      using CE_lindenbaum_extension_extends[of "{Neg A}" \<Gamma> enum] by blast
    have consistent: "CE_consistent \<Gamma> ?T"
      using world unfolding CE_clean_canonical_world_def
        CE_locally_maximal_consistent_def by blast
    have not_A: "A \<notin> ?T"
    proof
      assume A_in: "A \<in> ?T"
      have d_A: "\<Gamma> ; ?T \<turnstile>\<^sub>CE\<^sub>s A"
        using A_in A_type by (rule CE_set_derivable.Assumption)
      have "\<Gamma> ; ?T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
        using d_A neg_in by (rule CE_set_derives_ObjFalse_of_formula_and_neg)
      then show False
        using consistent unfolding CE_consistent_def by blast
    qed
    have "A \<in> ?T"
      using valid world
      unfolding CE_clean_canonical_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>CE A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule CE_proves_formula)
  have "\<forall>T. CE_clean_canonical_world \<Gamma> T \<longrightarrow> A \<in> T"
    using proves CE_clean_canonical_world_contains_theorems by blast
  then show "CE_clean_canonical_valid_in_context \<Gamma> A"
    unfolding CE_clean_canonical_valid_in_context_def
    using A_type by blast
qed

theorem CEV_clean_canonical_valid_iff_proves:
  "CEV_clean_canonical_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>CEV A"
proof
  assume valid: "CEV_clean_canonical_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CEV_clean_canonical_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>CEV A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
    have initial_typed: "typed_theory \<Gamma> {Neg A}"
      unfolding typed_theory_def using A_type by auto
    have initial_consistent: "CEV_consistent \<Gamma> {Neg A}"
      using A_type not_proves by (rule CEV_consistent_singleton_neg_of_not_proves)
    obtain enum where enum: "enumerates_formulas \<Gamma> enum"
      using enumerates_formulas_exists by blast
    let ?T = "CEV_lindenbaum_extension \<Gamma> {Neg A} enum"
    have world: "CEV_clean_canonical_world \<Gamma> ?T"
      unfolding CEV_clean_canonical_world_def
      using initial_typed initial_consistent enum
      by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
    have neg_in: "Neg A \<in> ?T"
      using CEV_lindenbaum_extension_extends[of "{Neg A}" \<Gamma> enum] by blast
    have consistent: "CEV_consistent \<Gamma> ?T"
      using world unfolding CEV_clean_canonical_world_def
        CEV_locally_maximal_consistent_def by blast
    have not_A: "A \<notin> ?T"
    proof
      assume A_in: "A \<in> ?T"
      have d_A: "\<Gamma> ; ?T \<turnstile>\<^sub>CEV\<^sub>s A"
        using A_in A_type by (rule CEV_set_derivable.Assumption)
      have "\<Gamma> ; ?T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
        using d_A neg_in by (rule CEV_set_derives_ObjFalse_of_formula_and_neg)
      then show False
        using consistent unfolding CEV_consistent_def by blast
    qed
    have "A \<in> ?T"
      using valid world
      unfolding CEV_clean_canonical_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>CEV A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule CEV_proves_formula)
  have "\<forall>T. CEV_clean_canonical_world \<Gamma> T \<longrightarrow> A \<in> T"
    using proves CEV_clean_canonical_world_contains_theorems by blast
  then show "CEV_clean_canonical_valid_in_context \<Gamma> A"
    unfolding CEV_clean_canonical_valid_in_context_def
    using A_type by blast
qed

section \<open>Clean CE Henkin extension\<close>

lemma CE_set_derivable_subst_const_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CE\<^sub>s
    subst_const c \<sigma> N A"
  using assms
proof (induction rule: CE_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems
    by (rule subst_const_preserves_typing)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CE_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CE subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule CE_proves_subst_const)
  then show ?case
    by (rule CE_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CE\<^sub>s
        subst_const c \<sigma> N A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CE\<^sub>s
        subst_const c \<sigma> N (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CE\<^sub>s
        Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CE_set_derivable.Derive_MP)
qed

lemma CE_set_derivable_shift_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CE\<^sub>s shift A"
  using assms
proof (induction rule: CE_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using Assumption.hyps(2) by (rule weakening_front)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CE_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  have "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE rename Suc A"
    using Theorem.hyps by (rule CE_proves_rename) auto
  then show ?case
    unfolding shift_def by (rule CE_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_imp:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CE\<^sub>s
        Imp (shift A) (shift B)"
    using Derive_MP.IH(2) unfolding shift_def by simp
  show ?case
    using Derive_MP.IH(1) d_imp by (rule CE_set_derivable.Derive_MP)
qed

lemma CE_set_derivable_abstract_const_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>CE\<^sub>s
    abstract_const c \<sigma> A"
proof -
  have shifted:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CE\<^sub>s shift A"
    using assms by (rule CE_set_derivable_shift_clean)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have substituted:
      "\<sigma> # \<Gamma> ;
        subst_const c \<sigma> (Var 0) ` (shift ` T)
        \<turnstile>\<^sub>CE\<^sub>s subst_const c \<sigma> (Var 0) (shift A)"
    using shifted var_type by (rule CE_set_derivable_subst_const_clean)
  have image_eq:
      "subst_const c \<sigma> (Var 0) ` (shift ` T) =
        abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  show ?thesis
    using substituted image_eq unfolding abstract_const_def by simp
qed

lemma CE_set_derivable_shifted_inst_list_clean:
  assumes typed: "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and d: "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CE\<^sub>s
      Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CE\<^sub>s Imp (Exists \<sigma> P) Q"
  using assms
proof (induction \<Delta> arbitrary: Q)
  case Nil
  have d_empty:
      "\<sigma> # \<Gamma> ; {} \<turnstile>\<^sub>CE\<^sub>s Imp P (shift Q)"
    using Nil.prems(2) by simp
  have d_thm: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE Imp P (shift Q)"
    using d_empty by (rule CE_set_empty_imp_proves)
  have inst: "\<Gamma> \<turnstile>\<^sub>CE Imp (Exists \<sigma> P) Q"
    using P_type Nil.prems(4) d_thm by (rule CE_proves.Inst)
  then show ?case
    by (rule CE_set_derivable.Theorem)
next
  case (Cons A \<Delta>)
  let ?E = "Exists \<sigma> P"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Cons.prems(1) by simp
  have tail_typed: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(1) by simp
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Cons.prems(4) by (rule weakening_front)
  have d_cons:
      "\<sigma> # \<Gamma> ; insert (shift A) (shift ` set \<Delta>)
        \<turnstile>\<^sub>CE\<^sub>s Imp P (shift Q)"
    using Cons.prems(2) by simp
  have d_deduct:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CE\<^sub>s
        Imp (shift A) (Imp P (shift Q))"
    using shift_A_type d_cons by (rule CE_set_derivable_deduction)
  have swap:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CE
        Imp (Imp (shift A) (Imp P (shift Q)))
          (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_swap:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CE\<^sub>s
        Imp (Imp (shift A) (Imp P (shift Q)))
          (Imp P (Imp (shift A) (shift Q)))"
    using swap by (rule CE_set_derivable.Theorem)
  have d_swapped:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CE\<^sub>s
        Imp P (shift (Imp A Q))"
    using d_deduct d_swap unfolding shift_def
    by (auto intro: CE_set_derivable.Derive_MP)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type Cons.prems(4) by auto
  have IH:
      "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CE\<^sub>s Imp ?E (Imp A Q)"
    using tail_typed d_swapped P_type AQ_type by (rule Cons.IH)
  have lifted:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CE\<^sub>s
        Imp ?E (Imp A Q)"
    using IH by (rule CE_set_derivable_mono) blast
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using P_type by auto
  have reorder:
      "\<Gamma> \<turnstile>\<^sub>CE
        Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using E_type A_type Cons.prems(4)
    by (intro CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_reorder:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CE\<^sub>s
        Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using reorder by (rule CE_set_derivable.Theorem)
  have d_A_to:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CE\<^sub>s
        Imp A (Imp ?E Q)"
    using lifted d_reorder by (rule CE_set_derivable.Derive_MP)
  have d_A:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CE\<^sub>s A"
    by (rule CE_set_derivable.Assumption) (simp_all add: A_type)
  have d_final:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CE\<^sub>s Imp ?E Q"
    using d_A d_A_to by (rule CE_set_derivable.Derive_MP)
  show ?case
    using d_final by simp
qed

lemma CE_set_derivable_shifted_inst_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CE\<^sub>s
      Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp (Exists \<sigma> P) Q"
proof -
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> shift ` T"
    and d_U: "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s Imp P (shift Q)"
    using assms(2) by (rule CE_set_derivable_finite_support)
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> U \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> U"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using U_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  obtain Bs where set_Bs: "set Bs = U"
    using finite_U finite_list by blast
  let ?\<Delta> = "map pre Bs"
  have set_\<Delta>_sub: "set ?\<Delta> \<subseteq> T"
    using pre_prop set_Bs by auto
  have shift_set_\<Delta>: "shift ` set ?\<Delta> = U"
    using pre_prop set_Bs by auto
  have typed_\<Delta>: "\<And>A. A \<in> set ?\<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    using assms(1) set_\<Delta>_sub unfolding typed_theory_def by blast
  have d_\<Delta>:
      "\<sigma> # \<Gamma> ; shift ` set ?\<Delta> \<turnstile>\<^sub>CE\<^sub>s
        Imp P (shift Q)"
    using d_U shift_set_\<Delta> by simp
  have lower:
      "\<Gamma> ; set ?\<Delta> \<turnstile>\<^sub>CE\<^sub>s Imp (Exists \<sigma> P) Q"
    using typed_\<Delta> d_\<Delta> assms(3,4)
    by (rule CE_set_derivable_shifted_inst_list_clean)
  show ?thesis
    using lower set_\<Delta>_sub by (rule CE_set_derivable_mono)
qed

lemma CE_set_derivable_abstract_fresh_witness_false_clean:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
      \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "\<sigma> # \<Gamma> ;
    insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)
      \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d:
      "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` insert ?W T
        \<turnstile>\<^sub>CE\<^sub>s abstract_const c \<sigma> ObjFalse"
    using assms(1) by (rule CE_set_derivable_abstract_const_clean)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  show ?thesis
    using abs_d abs_T abs_W by simp
qed

lemma CE_set_derivable_fresh_witness_false_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
      \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type:
      "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_ext:
      "\<sigma> # \<Gamma> ; insert ?P (shift ` T)
        \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using d fresh_T fresh_A
    by (rule CE_set_derivable_abstract_fresh_witness_false_clean)
  have d_imp_false:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CE\<^sub>s Imp ?P ObjFalse"
    using P_type d_ext by (rule CE_set_derivable_deduction)
  have d_imp_shift_false:
      "\<sigma> # \<Gamma> ; shift ` T
        \<turnstile>\<^sub>CE\<^sub>s Imp ?P (shift ObjFalse)"
    using d_imp_false by simp
  have lower: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Imp ?Q ObjFalse"
    using typed d_imp_shift_false P_type typed_ObjFalse
    by (rule CE_set_derivable_shifted_inst_clean)
  have Q_thm: "\<Gamma> \<turnstile>\<^sub>CE ?Q"
    using A_type
    by (intro CE_proves.C C_proves.H
        H_proves_exists_imp_shift_exists)
  have d_Q: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ?Q"
    using Q_thm by (rule CE_set_derivable.Theorem)
  show ?thesis
    using d_Q lower by (rule CE_set_derivable.Derive_MP)
qed

lemma CE_consistent_insert_fresh_witness_axiom_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and consistent: "CE_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CE_consistent \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold CE_consistent_def, intro notI)
  assume d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
    \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  have "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using typed d fresh_T fresh_A A_type
    by (rule CE_set_derivable_fresh_witness_false_clean)
  then show False
    using consistent unfolding CE_consistent_def by blast
qed

lemma CE_staged_henkin_step_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CE_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
      using typed consistent fresh_T fresh_A True
      by (rule CE_consistent_insert_fresh_witness_axiom_clean)
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using True by simp
  next
    case False
    then show ?thesis
      unfolding staged_henkin_step_def spec_def using consistent by simp
  qed
qed

lemma CE_staged_henkin_chain_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(1) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(2) by (rule staged_henkin_chain_typed)
  have consistent_n:
      "CE_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using finite_n typed_n consistent_n
    by (simp add: CE_staged_henkin_step_consistent_clean)
qed

lemma CE_staged_henkin_extension_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CE_consistent \<Gamma> T"
  shows "CE_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold CE_consistent_def, intro notI)
  assume d_false:
      "\<Gamma> ; staged_henkin_extension \<Gamma> T enum
        \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using d_false by (rule CE_set_derivable_finite_support)
  have U_sub_union:
      "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  obtain n where U_sub_chain:
      "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have "\<Gamma> ; staged_henkin_chain \<Gamma> T enum n
      \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CE_set_derivable_mono)
  moreover have
      "CE_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule CE_staged_henkin_chain_consistent_clean)
  ultimately show False
    unfolding CE_consistent_def by blast
qed

definition CE_clean_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CE_clean_Henkin_theory \<Gamma> T \<longleftrightarrow>
    CE_locally_maximal_consistent \<Gamma> T \<and> Henkin_witnessed \<Gamma> T"

lemma Henkin_witnessed_of_CE_local_maximal_available_clean:
  assumes local: "CE_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where ax_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using available A_type
    unfolding Henkin_witness_axioms_available_def by blast
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have ax_type: "\<Gamma> \<turnstile> henkin_witness_axiom c \<sigma> A : Prop"
    using A_type by (rule henkin_witness_axiom_typed)
  have d_exists: "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s Exists \<sigma> A"
    using exists_in exists_type by (rule CE_set_derivable.Assumption)
  have d_ax_raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s henkin_witness_axiom c \<sigma> A"
    using ax_in ax_type by (rule CE_set_derivable.Assumption)
  have d_ax:
      "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s
        Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A)"
    using d_ax_raw unfolding henkin_witness_axiom_def by simp
  have d_inst:
      "\<Gamma> ; T \<turnstile>\<^sub>CE\<^sub>s subst0 (Const c \<sigma>) A"
    using d_exists d_ax by (rule CE_set_derivable.Derive_MP)
  have inst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using local d_inst
    by (rule CE_locally_maximal_consistent_deductively_closed)
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using inst_in by (intro exI[of _ "Const c \<sigma>"]) auto
qed

lemma Henkin_witness_axioms_available_mono:
  assumes "Henkin_witness_axioms_available \<Gamma> T"
    and "T \<subseteq> U"
  shows "Henkin_witness_axioms_available \<Gamma> U"
  using assms unfolding Henkin_witness_axioms_available_def by blast

theorem CE_clean_Henkin_countermodel:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  obtains T where "CE_clean_Henkin_theory \<Gamma> T"
    and "Neg A \<in> T"
    and "A \<notin> T"
proof -
  let ?T0 = "{Neg A}"
  have finite_T0: "finite ?T0"
    by simp
  have typed_T0: "typed_theory \<Gamma> ?T0"
    unfolding typed_theory_def using A_type by auto
  have consistent_T0: "CE_consistent \<Gamma> ?T0"
    using A_type not_proves by (rule CE_consistent_singleton_neg_of_not_proves)
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?S = "staged_henkin_extension \<Gamma> ?T0 body_enum"
  have T0_sub_S: "?T0 \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have typed_S: "typed_theory \<Gamma> ?S"
    using typed_T0 by (rule staged_henkin_extension_typed)
  have consistent_S: "CE_consistent \<Gamma> ?S"
    using finite_T0 typed_T0 consistent_T0
    by (rule CE_staged_henkin_extension_consistent_clean)
  have available_S: "Henkin_witness_axioms_available \<Gamma> ?S"
    using body_enum
    by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?T = "CE_lindenbaum_extension \<Gamma> ?S formula_enum"
  have S_sub_T: "?S \<subseteq> ?T"
    by (rule CE_lindenbaum_extension_extends)
  have local_T: "CE_locally_maximal_consistent \<Gamma> ?T"
    using typed_S consistent_S formula_enum
    by (rule CE_lindenbaum_extension_locally_maximal_consistent)
  have available_T: "Henkin_witness_axioms_available \<Gamma> ?T"
    using available_S S_sub_T by (rule Henkin_witness_axioms_available_mono)
  have witnessed_T: "Henkin_witnessed \<Gamma> ?T"
    using local_T available_T
    by (rule Henkin_witnessed_of_CE_local_maximal_available_clean)
  have henkin_T: "CE_clean_Henkin_theory \<Gamma> ?T"
    using local_T witnessed_T unfolding CE_clean_Henkin_theory_def by blast
  have neg_in: "Neg A \<in> ?T"
    using T0_sub_S S_sub_T by blast
  have consistent_T: "CE_consistent \<Gamma> ?T"
    using local_T unfolding CE_locally_maximal_consistent_def by blast
  have not_A: "A \<notin> ?T"
  proof
    assume A_in: "A \<in> ?T"
    have d_A: "\<Gamma> ; ?T \<turnstile>\<^sub>CE\<^sub>s A"
      using A_in A_type by (rule CE_set_derivable.Assumption)
    have "\<Gamma> ; ?T \<turnstile>\<^sub>CE\<^sub>s ObjFalse"
      using d_A neg_in by (rule CE_set_derives_ObjFalse_of_formula_and_neg)
    then show False
      using consistent_T unfolding CE_consistent_def by blast
  qed
  show ?thesis
    using that henkin_T neg_in not_A by blast
qed

definition CE_clean_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CE_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CE_clean_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

theorem CE_clean_Henkin_valid_iff_proves:
  "CE_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>CE A"
proof
  assume valid: "CE_clean_Henkin_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CE_clean_Henkin_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>CE A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
    then obtain T where henkin: "CE_clean_Henkin_theory \<Gamma> T"
      and not_A: "A \<notin> T"
      using CE_clean_Henkin_countermodel[OF A_type not_proves] by blast
    have "A \<in> T"
      using valid henkin
      unfolding CE_clean_Henkin_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>CE A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule CE_proves_formula)
  have "\<And>T. CE_clean_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix T
    assume henkin: "CE_clean_Henkin_theory \<Gamma> T"
    have local: "CE_locally_maximal_consistent \<Gamma> T"
      using henkin unfolding CE_clean_Henkin_theory_def by blast
    show "A \<in> T"
      using local proves by (rule CE_locally_maximal_consistent_contains_theorems)
  qed
  then show "CE_clean_Henkin_valid_in_context \<Gamma> A"
    unfolding CE_clean_Henkin_valid_in_context_def
    using A_type by blast
qed
section \<open>Clean CEV Henkin extension\<close>

lemma CEV_set_derivable_subst_const_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CEV\<^sub>s
    subst_const c \<sigma> N A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_type: "\<Gamma> \<turnstile> subst_const c \<sigma> N A : Prop"
    using Assumption.hyps(2) Assumption.prems
    by (rule subst_const_preserves_typing)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CEV_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  have "\<Gamma> \<turnstile>\<^sub>CEV subst_const c \<sigma> N A"
    using Theorem.hyps Theorem.prems by (rule CEV_proves_subst_const)
  then show ?case
    by (rule CEV_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_A:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CEV\<^sub>s
        subst_const c \<sigma> N A"
    using Derive_MP.prems by (rule Derive_MP.IH(1))
  have d_imp_raw:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CEV\<^sub>s
        subst_const c \<sigma> N (Imp A B)"
    using Derive_MP.prems by (rule Derive_MP.IH(2))
  have d_imp:
      "\<Gamma> ; subst_const c \<sigma> N ` T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (subst_const c \<sigma> N A) (subst_const c \<sigma> N B)"
    using d_imp_raw by simp
  show ?case
    using d_A d_imp by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_set_derivable_shift_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CEV\<^sub>s shift A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  have A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using Assumption.hyps(2) by (rule weakening_front)
  show ?case
    using Assumption.hyps(1) A_type
    by (intro CEV_set_derivable.Assumption) auto
next
  case (Theorem \<Gamma> A T)
  have "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV rename Suc A"
    using Theorem.hyps by (rule CEV_proves_rename) auto
  then show ?case
    unfolding shift_def by (rule CEV_set_derivable.Theorem)
next
  case (Derive_MP \<Gamma> T A B)
  have d_imp:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (shift A) (shift B)"
    using Derive_MP.IH(2) unfolding shift_def by simp
  show ?case
    using Derive_MP.IH(1) d_imp by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_set_derivable_abstract_const_clean:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` T \<turnstile>\<^sub>CEV\<^sub>s
    abstract_const c \<sigma> A"
proof -
  have shifted:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CEV\<^sub>s shift A"
    using assms by (rule CEV_set_derivable_shift_clean)
  have var_type: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>"
    by simp
  have substituted:
      "\<sigma> # \<Gamma> ;
        subst_const c \<sigma> (Var 0) ` (shift ` T)
        \<turnstile>\<^sub>CEV\<^sub>s subst_const c \<sigma> (Var 0) (shift A)"
    using shifted var_type by (rule CEV_set_derivable_subst_const_clean)
  have image_eq:
      "subst_const c \<sigma> (Var 0) ` (shift ` T) =
        abstract_const c \<sigma> ` T"
    unfolding abstract_const_def by auto
  show ?thesis
    using substituted image_eq unfolding abstract_const_def by simp
qed

lemma CEV_set_derivable_shifted_inst_list_clean:
  assumes typed: "\<And>A. A \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and d: "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s
      Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s Imp (Exists \<sigma> P) Q"
  using assms
proof (induction \<Delta> arbitrary: Q)
  case Nil
  have d_empty:
      "\<sigma> # \<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sub>s Imp P (shift Q)"
    using Nil.prems(2) by simp
  have d_thm: "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q)"
    using d_empty by (rule CEV_set_empty_imp_proves)
  have inst: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using P_type Nil.prems(4) d_thm by (rule CEV_proves.Inst)
  then show ?case
    by (rule CEV_set_derivable.Theorem)
next
  case (Cons A \<Delta>)
  let ?E = "Exists \<sigma> P"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using Cons.prems(1) by simp
  have tail_typed: "\<And>B. B \<in> set \<Delta> \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    using Cons.prems(1) by simp
  have shift_A_type: "\<sigma> # \<Gamma> \<turnstile> shift A : Prop"
    using A_type by (rule weakening_front)
  have shift_Q_type: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Cons.prems(4) by (rule weakening_front)
  have d_cons:
      "\<sigma> # \<Gamma> ; insert (shift A) (shift ` set \<Delta>)
        \<turnstile>\<^sub>CEV\<^sub>s Imp P (shift Q)"
    using Cons.prems(2) by simp
  have d_deduct:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s
        Imp (shift A) (Imp P (shift Q))"
    using shift_A_type d_cons by (rule CEV_set_derivable_deduction)
  have swap:
      "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp (shift A) (Imp P (shift Q)))
          (Imp P (Imp (shift A) (shift Q)))"
    using shift_A_type P_type shift_Q_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_swap:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Imp (shift A) (Imp P (shift Q)))
          (Imp P (Imp (shift A) (shift Q)))"
    using swap by (rule CEV_set_derivable.Theorem)
  have d_swapped:
      "\<sigma> # \<Gamma> ; shift ` set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s
        Imp P (shift (Imp A Q))"
    using d_deduct d_swap unfolding shift_def
    by (auto intro: CEV_set_derivable.Derive_MP)
  have AQ_type: "\<Gamma> \<turnstile> Imp A Q : Prop"
    using A_type Cons.prems(4) by auto
  have IH:
      "\<Gamma> ; set \<Delta> \<turnstile>\<^sub>CEV\<^sub>s Imp ?E (Imp A Q)"
    using tail_typed d_swapped P_type AQ_type by (rule Cons.IH)
  have lifted:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CEV\<^sub>s
        Imp ?E (Imp A Q)"
    using IH by (rule CEV_set_derivable_mono) blast
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using P_type by auto
  have reorder:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using E_type A_type Cons.prems(4)
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_swap_imp)
  have d_reorder:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Imp ?E (Imp A Q)) (Imp A (Imp ?E Q))"
    using reorder by (rule CEV_set_derivable.Theorem)
  have d_A_to:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CEV\<^sub>s
        Imp A (Imp ?E Q)"
    using lifted d_reorder by (rule CEV_set_derivable.Derive_MP)
  have d_A:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CEV\<^sub>s A"
    by (rule CEV_set_derivable.Assumption) (simp_all add: A_type)
  have d_final:
      "\<Gamma> ; insert A (set \<Delta>) \<turnstile>\<^sub>CEV\<^sub>s Imp ?E Q"
    using d_A d_A_to by (rule CEV_set_derivable.Derive_MP)
  show ?case
    using d_final by simp
qed

lemma CEV_set_derivable_shifted_inst_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CEV\<^sub>s
      Imp P (shift Q)"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q_type: "\<Gamma> \<turnstile> Q : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp (Exists \<sigma> P) Q"
proof -
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> shift ` T"
    and d_U: "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s Imp P (shift Q)"
    using assms(2) by (rule CEV_set_derivable_finite_support)
  define pre where "pre B = (SOME A. A \<in> T \<and> B = shift A)" for B
  have pre_prop: "\<And>B. B \<in> U \<Longrightarrow> pre B \<in> T \<and> B = shift (pre B)"
  proof -
    fix B
    assume "B \<in> U"
    then have "\<exists>A. A \<in> T \<and> B = shift A"
      using U_sub by blast
    then show "pre B \<in> T \<and> B = shift (pre B)"
      unfolding pre_def by (rule someI_ex)
  qed
  obtain Bs where set_Bs: "set Bs = U"
    using finite_U finite_list by blast
  let ?\<Delta> = "map pre Bs"
  have set_\<Delta>_sub: "set ?\<Delta> \<subseteq> T"
    using pre_prop set_Bs by auto
  have shift_set_\<Delta>: "shift ` set ?\<Delta> = U"
    using pre_prop set_Bs by auto
  have typed_\<Delta>: "\<And>A. A \<in> set ?\<Delta> \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    using assms(1) set_\<Delta>_sub unfolding typed_theory_def by blast
  have d_\<Delta>:
      "\<sigma> # \<Gamma> ; shift ` set ?\<Delta> \<turnstile>\<^sub>CEV\<^sub>s
        Imp P (shift Q)"
    using d_U shift_set_\<Delta> by simp
  have lower:
      "\<Gamma> ; set ?\<Delta> \<turnstile>\<^sub>CEV\<^sub>s Imp (Exists \<sigma> P) Q"
    using typed_\<Delta> d_\<Delta> assms(3,4)
    by (rule CEV_set_derivable_shifted_inst_list_clean)
  show ?thesis
    using lower set_\<Delta>_sub by (rule CEV_set_derivable_mono)
qed

lemma CEV_set_derivable_abstract_fresh_witness_false_clean:
  assumes "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
      \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    and "c \<notin> consts_of_set T"
    and "c \<notin> consts_of A"
  shows "\<sigma> # \<Gamma> ;
    insert (Imp (shift (Exists \<sigma> A)) A) (shift ` T)
      \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  let ?W = "henkin_witness_axiom c \<sigma> A"
  have abs_d:
      "\<sigma> # \<Gamma> ; abstract_const c \<sigma> ` insert ?W T
        \<turnstile>\<^sub>CEV\<^sub>s abstract_const c \<sigma> ObjFalse"
    using assms(1) by (rule CEV_set_derivable_abstract_const_clean)
  have abs_T: "abstract_const c \<sigma> ` T = shift ` T"
    using assms(2) by (rule abstract_const_image_fresh_set)
  have abs_W: "abstract_const c \<sigma> ?W = Imp (shift (Exists \<sigma> A)) A"
    using assms(3) by (rule abstract_const_henkin_witness_axiom_fresh)
  show ?thesis
    using abs_d abs_T abs_W by simp
qed

lemma CEV_set_derivable_fresh_witness_false_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
      \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  let ?P = "Imp (shift (Exists \<sigma> A)) A"
  let ?Q = "Exists \<sigma> ?P"
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have shifted_exists_type:
      "\<sigma> # \<Gamma> \<turnstile> shift (Exists \<sigma> A) : Prop"
    using exists_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_exists_type A_type by auto
  have d_ext:
      "\<sigma> # \<Gamma> ; insert ?P (shift ` T)
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d fresh_T fresh_A
    by (rule CEV_set_derivable_abstract_fresh_witness_false_clean)
  have d_imp_false:
      "\<sigma> # \<Gamma> ; shift ` T \<turnstile>\<^sub>CEV\<^sub>s Imp ?P ObjFalse"
    using P_type d_ext by (rule CEV_set_derivable_deduction)
  have d_imp_shift_false:
      "\<sigma> # \<Gamma> ; shift ` T
        \<turnstile>\<^sub>CEV\<^sub>s Imp ?P (shift ObjFalse)"
    using d_imp_false by simp
  have lower: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Imp ?Q ObjFalse"
    using typed d_imp_shift_false P_type typed_ObjFalse
    by (rule CEV_set_derivable_shifted_inst_clean)
  have Q_thm: "\<Gamma> \<turnstile>\<^sub>CEV ?Q"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H
        H_proves_exists_imp_shift_exists)
  have d_Q: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ?Q"
    using Q_thm by (rule CEV_set_derivable.Theorem)
  show ?thesis
    using d_Q lower by (rule CEV_set_derivable.Derive_MP)
qed

lemma CEV_consistent_insert_fresh_witness_axiom_clean:
  assumes typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
    and fresh_T: "c \<notin> consts_of_set T"
    and fresh_A: "c \<notin> consts_of A"
    and A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "CEV_consistent \<Gamma> (insert (henkin_witness_axiom c \<sigma> A) T)"
proof (unfold CEV_consistent_def, intro notI)
  assume d: "\<Gamma> ; insert (henkin_witness_axiom c \<sigma> A) T
    \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using typed d fresh_T fresh_A A_type
    by (rule CEV_set_derivable_fresh_witness_false_clean)
  then show False
    using consistent unfolding CEV_consistent_def by blast
qed

lemma CEV_staged_henkin_step_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (staged_henkin_step \<Gamma> spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage T A) T A"
      using finite_T by (rule fresh_const_for_stage_fresh)
    have fresh_T: "fresh_const_for_stage T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by blast
    have fresh_A: "fresh_const_for_stage T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast
    have "CEV_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage T A) \<sigma> A) T)"
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

lemma CEV_staged_henkin_chain_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have finite_n: "finite (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(1) by (rule staged_henkin_chain_finite)
  have typed_n: "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems(2) by (rule staged_henkin_chain_typed)
  have consistent_n:
      "CEV_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using finite_n typed_n consistent_n
    by (simp add: CEV_staged_henkin_step_consistent_clean)
qed

lemma CEV_staged_henkin_extension_consistent_clean:
  assumes finite_T: "finite T"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (staged_henkin_extension \<Gamma> T enum)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false:
      "\<Gamma> ; staged_henkin_extension \<Gamma> T enum
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> staged_henkin_extension \<Gamma> T enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_false by (rule CEV_set_derivable_finite_support)
  have U_sub_union:
      "U \<subseteq> (\<Union>n. staged_henkin_chain \<Gamma> T enum n)"
    using U_sub unfolding staged_henkin_extension_def .
  have step: "\<And>n. staged_henkin_chain \<Gamma> T enum n \<subseteq>
      staged_henkin_chain \<Gamma> T enum (Suc n)"
    by (rule staged_henkin_chain_step)
  obtain n where U_sub_chain:
      "U \<subseteq> staged_henkin_chain \<Gamma> T enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have "\<Gamma> ; staged_henkin_chain \<Gamma> T enum n
      \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_set_derivable_mono)
  moreover have
      "CEV_consistent \<Gamma> (staged_henkin_chain \<Gamma> T enum n)"
    using assms by (rule CEV_staged_henkin_chain_consistent_clean)
  ultimately show False
    unfolding CEV_consistent_def by blast
qed

definition CEV_clean_Henkin_theory :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_clean_Henkin_theory \<Gamma> T \<longleftrightarrow>
    CEV_locally_maximal_consistent \<Gamma> T \<and> Henkin_witnessed \<Gamma> T"

lemma Henkin_witnessed_of_CEV_local_maximal_available_clean:
  assumes local: "CEV_locally_maximal_consistent \<Gamma> T"
    and available: "Henkin_witness_axioms_available \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where ax_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using available A_type
    unfolding Henkin_witness_axioms_available_def by blast
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have ax_type: "\<Gamma> \<turnstile> henkin_witness_axiom c \<sigma> A : Prop"
    using A_type by (rule henkin_witness_axiom_typed)
  have d_exists: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Exists \<sigma> A"
    using exists_in exists_type by (rule CEV_set_derivable.Assumption)
  have d_ax_raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s henkin_witness_axiom c \<sigma> A"
    using ax_in ax_type by (rule CEV_set_derivable.Assumption)
  have d_ax:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A)"
    using d_ax_raw unfolding henkin_witness_axiom_def by simp
  have d_inst:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s subst0 (Const c \<sigma>) A"
    using d_exists d_ax by (rule CEV_set_derivable.Derive_MP)
  have inst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using local d_inst
    by (rule CEV_locally_maximal_consistent_deductively_closed)
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using inst_in by (intro exI[of _ "Const c \<sigma>"]) auto
qed

theorem CEV_clean_Henkin_countermodel:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "Neg A \<in> T"
    and "A \<notin> T"
proof -
  let ?T0 = "{Neg A}"
  have finite_T0: "finite ?T0"
    by simp
  have typed_T0: "typed_theory \<Gamma> ?T0"
    unfolding typed_theory_def using A_type by auto
  have consistent_T0: "CEV_consistent \<Gamma> ?T0"
    using A_type not_proves by (rule CEV_consistent_singleton_neg_of_not_proves)
  obtain body_enum where body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?S = "staged_henkin_extension \<Gamma> ?T0 body_enum"
  have T0_sub_S: "?T0 \<subseteq> ?S"
    by (rule staged_henkin_extension_extends)
  have typed_S: "typed_theory \<Gamma> ?S"
    using typed_T0 by (rule staged_henkin_extension_typed)
  have consistent_S: "CEV_consistent \<Gamma> ?S"
    using finite_T0 typed_T0 consistent_T0
    by (rule CEV_staged_henkin_extension_consistent_clean)
  have available_S: "Henkin_witness_axioms_available \<Gamma> ?S"
    using body_enum
    by (rule staged_henkin_extension_witness_axioms_available)
  obtain formula_enum where formula_enum: "enumerates_formulas \<Gamma> formula_enum"
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
  have neg_in: "Neg A \<in> ?T"
    using T0_sub_S S_sub_T by blast
  have consistent_T: "CEV_consistent \<Gamma> ?T"
    using local_T unfolding CEV_locally_maximal_consistent_def by blast
  have not_A: "A \<notin> ?T"
  proof
    assume A_in: "A \<in> ?T"
    have d_A: "\<Gamma> ; ?T \<turnstile>\<^sub>CEV\<^sub>s A"
      using A_in A_type by (rule CEV_set_derivable.Assumption)
    have "\<Gamma> ; ?T \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
      using d_A neg_in by (rule CEV_set_derives_ObjFalse_of_formula_and_neg)
    then show False
      using consistent_T unfolding CEV_consistent_def by blast
  qed
  show ?thesis
    using that henkin_T neg_in not_A by blast
qed

definition CEV_clean_Henkin_valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>T. CEV_clean_Henkin_theory \<Gamma> T \<longrightarrow> A \<in> T)"

theorem CEV_clean_Henkin_valid_iff_proves:
  "CEV_clean_Henkin_valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>CEV A"
proof
  assume valid: "CEV_clean_Henkin_valid_in_context \<Gamma> A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using valid unfolding CEV_clean_Henkin_valid_in_context_def by blast
  show "\<Gamma> \<turnstile>\<^sub>CEV A"
  proof (rule ccontr)
    assume not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
    then obtain T where henkin: "CEV_clean_Henkin_theory \<Gamma> T"
      and not_A: "A \<notin> T"
      using CEV_clean_Henkin_countermodel[OF A_type not_proves] by blast
    have "A \<in> T"
      using valid henkin
      unfolding CEV_clean_Henkin_valid_in_context_def by blast
    then show False
      using not_A by blast
  qed
next
  assume proves: "\<Gamma> \<turnstile>\<^sub>CEV A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using proves by (rule CEV_proves_formula)
  have "\<And>T. CEV_clean_Henkin_theory \<Gamma> T \<Longrightarrow> A \<in> T"
  proof -
    fix T
    assume henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    have local: "CEV_locally_maximal_consistent \<Gamma> T"
      using henkin unfolding CEV_clean_Henkin_theory_def by blast
    show "A \<in> T"
      using local proves by (rule CEV_locally_maximal_consistent_contains_theorems)
  qed
  then show "CEV_clean_Henkin_valid_in_context \<Gamma> A"
    unfolding CEV_clean_Henkin_valid_in_context_def
    using A_type by blast
qed

end
