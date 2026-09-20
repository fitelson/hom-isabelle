theory Bacon_CEV_Axiom_Extension
  imports 
    "Goodman_Legacy_01.Bacon_PP_Question"
begin

section \<open>CEV with an added stock of axioms\<close>

text \<open>
  The existing judgement \<open>\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A\<close> is local consequence:
  members of \<open>T\<close> may be used only as assumptions and the only closure rule
  above them is modus ponens.  That is the right relation for Lindenbaum and
  canonical-theory arguments, but it is not the relation expressed by adding
  principles to CEV as axioms.  In an axiom extension, Generalization,
  Instantiation, and theorem-level vector Equivalence remain applicable to
  results using the added axioms.

  The following judgement is the smallest such extension.  The base rule
  packages every theorem of the already certified CEV calculus; the remaining
  rules are exactly CEV's theorem-producing closure rules.
\<close>

inductive CEV_axiom_proves ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<turnstile>\<^sub>CEV\<^sup>+ _" [50, 50, 50] 50) where
  Axiom[intro]:
    "A \<in> T \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
| Base[intro]:
    "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
| VectorEquivalence[intro]:
    "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
      \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
      \<sigma>s @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body \<sigma>s F G \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Eq (arrow_type \<sigma>s Prop) F G"
| MP[intro]:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
| Gen[intro]:
    "\<Gamma> \<turnstile> P : Prop \<Longrightarrow>
      \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
      \<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (Forall \<sigma> Q)"
| Inst[intro]:
    "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow>
      \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
      \<sigma> # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q) \<Longrightarrow>
      \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Exists \<sigma> P) Q"

lemma CEV_axiom_proves_formula:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  then show ?case by simp
next
  case (Base \<Gamma> A T)
  then show ?case by (rule CEV_proves_formula)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  then show ?case by auto
next
  case (MP \<Gamma> T A B)
  then show ?case by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q T)
  then show ?case by auto
next
  case (Inst \<sigma> \<Gamma> P Q T)
  then show ?case by auto
qed

lemma CEV_axiom_proves_mono:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and "T \<subseteq> U"
  shows "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
proof (induction rule: CEV_axiom_proves.induct)
  case (Axiom A T \<Gamma>)
  then show ?case by (intro CEV_axiom_proves.Axiom) blast+
next
  case (Base \<Gamma> A T)
  show ?case
    using Base.hyps by (rule CEV_axiom_proves.Base)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G T)
  have IH:
    "\<sigma>s @ \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ zeta_body \<sigma>s F G"
    using VectorEquivalence.prems by (rule VectorEquivalence.IH)
  show ?case
    using VectorEquivalence.hyps(1,2) IH
    by (rule CEV_axiom_proves.VectorEquivalence)
next
  case (MP \<Gamma> T A B)
  have d_A: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ A"
    using MP.prems by (rule MP.IH(1))
  have d_imp: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    using MP.prems by (rule MP.IH(2))
  show ?case
    using d_A d_imp by (rule CEV_axiom_proves.MP)
next
  case (Gen \<Gamma> P \<sigma> Q T)
  have IH: "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift P) Q"
    using Gen.prems by (rule Gen.IH)
  show ?case
    using Gen.hyps(1,2) IH by (rule CEV_axiom_proves.Gen)
next
  case (Inst \<sigma> \<Gamma> P Q T)
  have IH: "\<sigma> # \<Gamma> ; U \<turnstile>\<^sub>CEV\<^sup>+ Imp P (shift Q)"
    using Inst.prems by (rule Inst.IH)
  show ?case
    using Inst.hyps(1,2) IH by (rule CEV_axiom_proves.Inst)
qed

lemma CEV_set_derivable_imp_axiom_proves:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
proof (induction rule: CEV_set_derivable.induct)
  case (Assumption A T \<Gamma>)
  then show ?case by (rule CEV_axiom_proves.Axiom)
next
  case (Theorem \<Gamma> A T)
  then show ?case by (rule CEV_axiom_proves.Base)
next
  case (Derive_MP \<Gamma> T A B)
  show ?case
    using Derive_MP.IH by (rule CEV_axiom_proves.MP)
qed

definition CEV_axiom_consistent :: "ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_axiom_consistent \<Gamma> T \<longleftrightarrow>
    \<not> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"

lemma CEV_axiom_consistent_imp_local_consistent:
  assumes "CEV_axiom_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> T"
  using assms CEV_set_derivable_imp_axiom_proves
  unfolding CEV_axiom_consistent_def CEV_consistent_def
  by blast

definition pp_recombination_axiom_consistency_question :: bool where
  "pp_recombination_axiom_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_recombination_PP_axioms"

definition pp_full_QLN_axiom_consistency_question :: bool where
  "pp_full_QLN_axiom_consistency_question \<longleftrightarrow>
    CEV_axiom_consistent [] pp_full_QLN_PP_axioms"

lemma pp_recombination_axiom_consistency_imp_local:
  assumes "pp_recombination_axiom_consistency_question"
  shows "pp_recombination_consistency_question"
  using assms CEV_axiom_consistent_imp_local_consistent
  unfolding pp_recombination_axiom_consistency_question_def
    pp_recombination_consistency_question_def
  by blast

lemma pp_full_QLN_axiom_consistency_imp_local:
  assumes "pp_full_QLN_axiom_consistency_question"
  shows "pp_full_QLN_consistency_question"
  using assms CEV_axiom_consistent_imp_local_consistent
  unfolding pp_full_QLN_axiom_consistency_question_def
    pp_full_QLN_consistency_question_def
  by blast

subsection \<open>Necessitation is admissible in every axiom extension\<close>

lemma CEV_axiom_proves_ObjTrue:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
  using CEV_proves_ObjTrue by (rule CEV_axiom_proves.Base)

lemma CEV_axiom_imp_of_right:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_axiom_proves_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp A B)"
    using assms(1) B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_imp_of_right)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B (Imp A B)"
    using taut by (rule CEV_axiom_proves.Base)
  show ?thesis
    using assms(2) d_taut by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_conj_intro:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_axiom_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_axiom_proves_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_intro)
  have d_taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp A (Imp B (Conj A B))"
    using taut by (rule CEV_axiom_proves.Base)
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B (Conj A B)"
    using assms(1) d_taut by (rule CEV_axiom_proves.MP)
  show ?thesis
    using assms(2) step by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_biconditional_of_theorems:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_axiom_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_axiom_proves_formula)
  have d_AB: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
    using A_type assms(2) by (rule CEV_axiom_imp_of_right)
  have d_BA: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B A"
    using B_type assms(1) by (rule CEV_axiom_imp_of_right)
  show ?thesis
    using d_AB d_BA by (rule CEV_axiom_conj_intro)
qed

lemma CEV_axiom_zeroary_equivalence:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A B"
proof -
  have zeta:
    "[] @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body [] A B"
    using assms(3) by (simp add: zeta_body_def fresh_vars_def)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq (arrow_type [] Prop) A B"
  proof (rule CEV_axiom_proves.VectorEquivalence[
      where \<sigma>s = "[]" and F = A and G = B])
    show "\<Gamma> \<turnstile> A : arrow_type [] Prop"
      using assms(1) by simp
  next
    show "\<Gamma> \<turnstile> B : arrow_type [] Prop"
      using assms(2) by simp
  next
    show "[] @ \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ zeta_body [] A B"
      using zeta .
  qed
  then show ?thesis by simp
qed

theorem CEV_axiom_necessitation:
  assumes "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (\<box>\<^sub>o A)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule CEV_axiom_proves_formula)
  have iff_true:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o ObjTrue)"
    using assms CEV_axiom_proves_ObjTrue
    by (rule CEV_axiom_biconditional_of_theorems)
  have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A ObjTrue"
    using A_type typed_ObjTrue iff_true
    by (rule CEV_axiom_zeroary_equivalence)
  then show ?thesis by (simp add: ObjBox_def)
qed

text \<open>
  This theorem is the precise reason the local-assumption consistency question
  and the axiom-extension consistency question must not be identified.
  Added axioms can be necessitated in the latter.
\<close>

subsection \<open>Local reasoning inside an axiom extension\<close>

text \<open>
  Local assumptions must remain distinct from added axioms.  In particular,
  theorem-level Equivalence and its derived Necessitation rule may be applied
  to theorems of the axiom extension, but not to formulas that depend on a
  temporary local assumption.  The following auxiliary judgement enforces
  exactly that boundary.
\<close>

inductive CEV_axiom_from ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ ; _ \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s _" [50, 50, 50, 50] 50) where
  Assumption[intro]:
    "A \<in> S \<Longrightarrow> \<Gamma> \<turnstile> A : Prop \<Longrightarrow>
      \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
| Theorem[intro]:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A \<Longrightarrow>
      \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
| MP[intro]:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A \<Longrightarrow>
      \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A B \<Longrightarrow>
      \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"

lemma CEV_axiom_from_formula:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_axiom_from.induct)
  case (Assumption A S \<Gamma> T)
  then show ?case by simp
next
  case (Theorem \<Gamma> T A S)
  then show ?case by (rule CEV_axiom_proves_formula)
next
  case (MP \<Gamma> T S A B)
  then show ?case by (auto elim: has_type.cases)
qed

lemma CEV_axiom_from_mono:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and "S \<subseteq> U"
  shows "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  using assms
proof (induction rule: CEV_axiom_from.induct)
  case (Assumption A S \<Gamma> T)
  then show ?case by (intro CEV_axiom_from.Assumption) blast+
next
  case (Theorem \<Gamma> T A S)
  show ?case
    using Theorem.hyps by (rule CEV_axiom_from.Theorem)
next
  case (MP \<Gamma> T S A B)
  have d_A: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    using MP.prems by (rule MP.IH(1))
  have d_imp: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp A B"
    using MP.prems by (rule MP.IH(2))
  show ?case
    using d_A d_imp by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_empty_iff:
  "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A \<longleftrightarrow>
    \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof
  assume d: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  have aux:
    "\<And>S B. \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B \<Longrightarrow>
      S = {} \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
  proof -
    fix S B
    assume d_B: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
    then show "S = {} \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
    proof (induction rule: CEV_axiom_from.induct)
      case (Assumption B S \<Gamma> T)
      then show ?case by simp
    next
      case (Theorem \<Gamma> T B S)
      then show ?case by simp
    next
      case (MP \<Gamma> T S B C)
      have d_B: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
        using MP.prems by (rule MP.IH(1))
      have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp B C"
        using MP.prems by (rule MP.IH(2))
      show ?case
        using d_B d_imp by (rule CEV_axiom_proves.MP)
    qed
  qed
  show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
    using d by (rule aux[OF _ refl])
next
  assume "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  then show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    by (rule CEV_axiom_from.Theorem)
qed

lemma CEV_axiom_from_deduction:
  assumes "\<Gamma> \<turnstile> X : Prop"
    and "\<Gamma> ; T ; insert X S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp X B"
proof -
  have aux:
    "\<And>Y U. \<Gamma> \<turnstile> Y : Prop \<Longrightarrow>
      insert X S \<subseteq> insert Y U \<Longrightarrow>
      \<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp Y B"
    using assms(2)
  proof (induction rule: CEV_axiom_from.induct)
    case (Assumption B V \<Gamma> T)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using Assumption.prems by blast
    have V_sub: "V \<subseteq> insert Y U"
      using Assumption.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Assumption.hyps by simp
    show ?case
    proof (cases "B = Y")
      case True
      have base: "\<Gamma> \<turnstile>\<^sub>CEV Imp Y Y"
        using Y_type
        by (intro CEV_proves.CE CE_proves.C C_proves.H H_imp_self)
      have d_YY: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp Y Y"
        using base by (rule CEV_axiom_proves.Base)
      have "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp Y Y"
        using d_YY by (rule CEV_axiom_from.Theorem)
      then show ?thesis
        using True by simp
    next
      case False
      have B_in: "B \<in> U"
        using Assumption.hyps V_sub False by blast
      have d_B: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
        using B_in B_type by (rule CEV_axiom_from.Assumption)
      have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp Y B)"
        using Y_type B_type
        by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
            prop_tautology_imp_of_right)
      have d_taut: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
          Imp B (Imp Y B)"
        using taut
        by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
      show ?thesis
        using d_B d_taut by (rule CEV_axiom_from.MP)
    qed
  next
    case (Theorem \<Gamma> T B V)
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using Theorem.hyps by (rule CEV_axiom_proves_formula)
    have d_imp: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp Y B"
      using Theorem.prems(1) Theorem.hyps
      by (rule CEV_axiom_imp_of_right)
    show ?case
      using d_imp by (rule CEV_axiom_from.Theorem)
  next
    case (MP \<Gamma> T V B C)
    have Y_type: "\<Gamma> \<turnstile> Y : Prop"
      using MP.prems by blast
    have V_sub: "V \<subseteq> insert Y U"
      using MP.prems by blast
    have B_type: "\<Gamma> \<turnstile> B : Prop"
      using MP.hyps(1) by (rule CEV_axiom_from_formula)
    have C_type: "\<Gamma> \<turnstile> C : Prop"
      using MP.hyps(2)
      by (auto dest: CEV_axiom_from_formula elim: has_type.cases)
    have taut: "\<Gamma> \<turnstile>\<^sub>CEV
        Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using Y_type B_type C_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
          prop_tautology_deduction_mp)
    have d_taut: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (Imp Y B) (Imp (Imp Y (Imp B C)) (Imp Y C))"
      using taut
      by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
    have IH_B: "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp Y B"
      using Y_type V_sub by (rule MP.IH(1))
    have IH_imp:
      "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp Y (Imp B C)"
      using Y_type V_sub by (rule MP.IH(2))
    have step:
      "\<Gamma> ; T ; U \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (Imp Y (Imp B C)) (Imp Y C)"
      using IH_B d_taut by (rule CEV_axiom_from.MP)
    show ?case
      using IH_imp step by (rule CEV_axiom_from.MP)
  qed
  show ?thesis
    using assms(1) by (rule aux) blast
qed

lemma CEV_axiom_from_singleton_imp:
  assumes "\<Gamma> \<turnstile> X : Prop"
    and "\<Gamma> ; T ; {X} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp X B"
proof -
  have "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp X B"
    using assms by (rule CEV_axiom_from_deduction)
  then show ?thesis
    using CEV_axiom_from_empty_iff by blast
qed

subsection \<open>Reusable elimination rules\<close>

lemma CEV_axiom_UI:
  assumes body_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and universal: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall \<sigma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst0 M A"
proof -
  have ui: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall \<sigma> A) (subst0 M A)"
    using body_type term_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have d_ui:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Forall \<sigma> A) (subst0 M A)"
    using ui by (rule CEV_axiom_proves.Base)
  show ?thesis
    using universal d_ui by (rule CEV_axiom_proves.MP)
qed

lemma CEV_axiom_from_UI:
  assumes body_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and universal:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Forall \<sigma> A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 M A"
proof -
  have ui: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Forall \<sigma> A) (subst0 M A)"
    using body_type term_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have d_ui:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Forall \<sigma> A) (subst0 M A)"
    using ui
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using universal d_ui by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_UI_typed:
  assumes universal_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and universal: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall \<sigma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ subst0 M A"
proof -
  have "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using universal_type by (auto elim: has_type.cases)
  then show ?thesis
    using term_type universal by (rule CEV_axiom_UI)
qed

lemma CEV_axiom_from_UI_typed:
  assumes universal_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    and term_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and universal:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Forall \<sigma> A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 M A"
proof -
  have "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using universal_type by (auto elim: has_type.cases)
  then show ?thesis
    using term_type universal by (rule CEV_axiom_from_UI)
qed

lemma CEV_axiom_from_conj_left:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    using CEV_axiom_from_formula[OF assms]
    by (auto elim: has_type.cases)+
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) A"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_left)
  have d_taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Conj A B) A"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_conj_right:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj A B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    using CEV_axiom_from_formula[OF assms]
    by (auto elim: has_type.cases)+
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj A B) B"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_right)
  have d_taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Conj A B) B"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using assms d_taut by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_conj_intro:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj A B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_axiom_from_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_axiom_from_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_intro)
  have d_taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp A (Imp B (Conj A B))"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp B (Conj A B)"
    using assms(1) d_taut by (rule CEV_axiom_from.MP)
  show ?thesis
    using assms(2) step by (rule CEV_axiom_from.MP)
qed

lemma CEV_axiom_from_contradiction:
  assumes "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_axiom_from_formula)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (Neg A) ObjFalse)"
    using A_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_contradiction)
  have d_taut:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp A (Imp (Neg A) ObjFalse)"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Neg A) ObjFalse"
    using assms(1) d_taut by (rule CEV_axiom_from.MP)
  show ?thesis
    using assms(2) step by (rule CEV_axiom_from.MP)
qed

end
