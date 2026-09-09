theory Bacon_Zeta
  imports Bacon_Modal_Derivations
begin

section \<open>Vector equivalence and zeta-style closure\<close>

text \<open>
  The zero-ary equivalence rule in \<open>Bacon_Modal_Derivations\<close> turns a proved
  biconditional between propositions into propositional identity.  The full
  Bacon-Dorr rule is higher-type: if two terms agree on a fresh vector of
  arguments, they are identical at the corresponding function type.

  In the de Bruijn presentation, adding a fresh vector of variables means
  extending the type context at the front.  Old terms must then be shifted across
  that fresh prefix, and the fresh variables themselves are represented by
  \<open>Var 0\<close>, \<open>Var 1\<close>, ..., in the extended context.

  In standard notation, the principal rule is
  \<open>\<turnstile> F x\<^sub>1 \<dots> x\<^sub>n \<longleftrightarrow> G x\<^sub>1 \<dots> x\<^sub>n / \<turnstile> F = G\<close>,
  where the variables are fresh and both terms have relational result type
  \<open>\<sigma>\<^sub>1 \<rightarrow> \<dots> \<rightarrow> \<sigma>\<^sub>n \<rightarrow> Prop\<close>.  The helper \<open>zeta_body\<close> is the
  de Bruijn encoding of the premise.
\<close>

fun arrow_type :: "otype list \<Rightarrow> otype \<Rightarrow> otype" where
  "arrow_type [] \<tau> = \<tau>"
| "arrow_type (\<sigma> # \<sigma>s) \<tau> = \<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s \<tau>"

fun app_vec :: "oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "app_vec F [] = F"
| "app_vec F (A # As) = app_vec (App F A) As"

definition fresh_vars :: "nat \<Rightarrow> oterm list" where
  "fresh_vars n = map Var [0..<n]"

definition shift_ren :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_ren k c n = (if n < c then n else n + k)"

definition shift_by :: "nat \<Rightarrow> oterm \<Rightarrow> oterm" where
  "shift_by k M = rename (shift_ren k 0) M"

fun free_in :: "nat \<Rightarrow> oterm \<Rightarrow> bool" where
  "free_in k (Var n) = (k = n)"
| "free_in k (Const c \<sigma>) = False"
| "free_in k (App M N) = (free_in k M \<or> free_in k N)"
| "free_in k (Lam \<sigma> M) = free_in (Suc k) M"
| "free_in k (Eq \<sigma> M N) = (free_in k M \<or> free_in k N)"
| "free_in k (Neg A) = free_in k A"
| "free_in k (Conj A B) = (free_in k A \<or> free_in k B)"
| "free_in k (Disj A B) = (free_in k A \<or> free_in k B)"
| "free_in k (Imp A B) = (free_in k A \<or> free_in k B)"
| "free_in k (Forall \<sigma> A) = free_in (Suc k) A"
| "free_in k (Exists \<sigma> A) = free_in (Suc k) A"

definition fresh_for_extension :: "otype list \<Rightarrow> oterm \<Rightarrow> bool" where
  "fresh_for_extension \<sigma>s M \<longleftrightarrow> (\<forall>i < length \<sigma>s. \<not> free_in i M)"

lemma lift_ren_id[simp]:
  "lift_ren id = id"
  by (rule ext, rename_tac n, case_tac n) auto

lemma lift_ren_ident[simp]:
  "lift_ren (\<lambda>n. n) = (\<lambda>n. n)"
  by (rule ext, rename_tac n, case_tac n) auto

lemma rename_ident[simp]:
  "rename (\<lambda>n. n) M = M"
  by (induction M) auto

lemma rename_id[simp]:
  "rename id M = M"
  by (simp add: id_def)

lemma lift_ren_shift_ren[simp]:
  "lift_ren (shift_ren k c) = shift_ren k (Suc c)"
  by (rule ext, rename_tac n, case_tac n) (auto simp: shift_ren_def)

lemma shift_by_0[simp]:
  "shift_by 0 M = M"
  unfolding shift_by_def shift_ren_def by simp

lemma shift_by_1:
  "shift_by (Suc 0) M = shift M"
  unfolding shift_by_def shift_def shift_ren_def by simp

lemma lookup_append_shift:
  assumes "lookup \<Gamma> n = Some \<tau>"
  shows "lookup (\<Delta> @ \<Gamma>) (length \<Delta> + n) = Some \<tau>"
proof -
  from assms have n_lt: "n < length \<Gamma>" and nth: "\<Gamma> ! n = \<tau>"
    by (auto simp: lookup_def split: if_splits)
  then show ?thesis
    by (simp add: lookup_def nth_append)
qed

lemma shift_by_preserves_typing:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<Delta> @ \<Gamma> \<turnstile> shift_by (length \<Delta>) M : \<tau>"
  unfolding shift_by_def
  using assms
proof (rule renaming_preserves_typing)
  fix n \<sigma>
  assume "lookup \<Gamma> n = Some \<sigma>"
  then have "lookup (\<Delta> @ \<Gamma>) (length \<Delta> + n) = Some \<sigma>"
    by (rule lookup_append_shift)
  then show "lookup (\<Delta> @ \<Gamma>) (shift_ren (length \<Delta>) 0 n) = Some \<sigma>"
    by (simp add: shift_ren_def add.commute)
qed

lemma typed_fresh_vars:
  "list_all2 (\<lambda>V \<sigma>. \<sigma>s @ \<Gamma> \<turnstile> V : \<sigma>) (fresh_vars (length \<sigma>s)) \<sigma>s"
  unfolding fresh_vars_def list_all2_conv_all_nth
proof (intro conjI allI impI)
  show "length (map Var [0..<length \<sigma>s]) = length \<sigma>s"
    by simp
next
  fix i
  assume i_lt: "i < length (map Var [0..<length \<sigma>s])"
  then have "i < length \<sigma>s"
    by simp
  then have "lookup (\<sigma>s @ \<Gamma>) i = Some (\<sigma>s ! i)"
    by (simp add: lookup_def nth_append)
  with i_lt show "\<sigma>s @ \<Gamma> \<turnstile> (map Var [0..<length \<sigma>s]) ! i : \<sigma>s ! i"
    by auto
qed

lemma typed_app_vec:
  assumes "\<Gamma> \<turnstile> F : arrow_type \<sigma>s \<tau>"
    and "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) As \<sigma>s"
  shows "\<Gamma> \<turnstile> app_vec F As : \<tau>"
  using assms
proof (induction \<sigma>s arbitrary: F As)
  case Nil
  then show ?case
    by (cases As) auto
next
  case (Cons \<sigma> \<sigma>s)
  then obtain A As' where As_def: "As = A # As'"
    by (cases As) auto
  then have "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s \<tau>"
    using Cons.prems by simp
  moreover have "\<Gamma> \<turnstile> A : \<sigma>"
    using Cons.prems As_def by simp
  ultimately have "\<Gamma> \<turnstile> App F A : arrow_type \<sigma>s \<tau>"
    by auto
  moreover have "list_all2 (\<lambda>A \<sigma>. \<Gamma> \<turnstile> A : \<sigma>) As' \<sigma>s"
    using Cons.prems As_def by simp
  ultimately show ?case
    using Cons.IH As_def by simp
qed

lemma typed_app_fresh_vars:
  assumes "\<Gamma> \<turnstile> F : arrow_type \<sigma>s \<tau>"
  shows "\<sigma>s @ \<Gamma> \<turnstile> app_vec (shift_by (length \<sigma>s) F) (fresh_vars (length \<sigma>s)) : \<tau>"
proof -
  have "\<sigma>s @ \<Gamma> \<turnstile> shift_by (length \<sigma>s) F : arrow_type \<sigma>s \<tau>"
    using assms by (rule shift_by_preserves_typing)
  moreover have "list_all2 (\<lambda>A \<sigma>. \<sigma>s @ \<Gamma> \<turnstile> A : \<sigma>) (fresh_vars (length \<sigma>s)) \<sigma>s"
    by (rule typed_fresh_vars)
  ultimately show ?thesis
    by (rule typed_app_vec)
qed

definition zeta_body :: "otype list \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "zeta_body \<sigma>s F G =
    (app_vec (shift_by (length \<sigma>s) F) (fresh_vars (length \<sigma>s)) \<longleftrightarrow>\<^sub>o
     app_vec (shift_by (length \<sigma>s) G) (fresh_vars (length \<sigma>s)))"

lemma typed_zeta_body:
  assumes "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
  shows "\<sigma>s @ \<Gamma> \<turnstile> zeta_body \<sigma>s F G : Prop"
  unfolding zeta_body_def
  using typed_app_fresh_vars[OF assms(1)] typed_app_fresh_vars[OF assms(2)]
  by auto

lemma free_in_shift_ren_ge:
  assumes "free_in i (rename (shift_ren k c) M)"
    and "c \<le> i"
  shows "k + c \<le> i"
  using assms
proof (induction M arbitrary: i c)
  case (Var n)
  then show ?case
    by (auto simp: shift_ren_def)
next
  case (Const x1 x2)
  then show ?case
    by simp
next
  case (App M N)
  then show ?case
    by auto
next
  case (Lam \<sigma> M)
  then have "k + Suc c \<le> Suc i"
    using Lam.IH[of "Suc i" "Suc c"] by simp
  then show ?case
    by linarith
next
  case (Eq \<sigma> M N)
  then show ?case
    by auto
next
  case (Neg M)
  then show ?case
    by auto
next
  case (Conj M N)
  then show ?case
    by auto
next
  case (Disj M N)
  then show ?case
    by auto
next
  case (Imp M N)
  then show ?case
    by auto
next
  case (Forall \<sigma> M)
  then have "k + Suc c \<le> Suc i"
    using Forall.IH[of "Suc i" "Suc c"] by simp
  then show ?case
    by linarith
next
  case (Exists \<sigma> M)
  then have "k + Suc c \<le> Suc i"
    using Exists.IH[of "Suc i" "Suc c"] by simp
  then show ?case
    by linarith
qed

lemma free_in_shift_by_ge:
  assumes "free_in i (shift_by k M)"
  shows "k \<le> i"
  using free_in_shift_ren_ge[of i k 0 M] assms
  by (simp add: shift_by_def)

lemma shift_by_fresh_for_extension:
  "fresh_for_extension \<sigma>s (shift_by (length \<sigma>s) M)"
  unfolding fresh_for_extension_def
  using free_in_shift_by_ge by fastforce

text \<open>
  \<open>CEV\<close> is the vector-equivalence extension of \<open>CE\<close>.  When the vector is
  empty, the rule collapses to the propositional Equivalence rule.  When the
  vector is nonempty, the premise is checked in the freshly extended context
  \<open>\<sigma>s @ \<Gamma>\<close>, with the old terms shifted over that prefix.

  This is the theorem-level Bacon--Dorr rule.  In particular, CEV has no rule
  that internalizes an equivalence under an arbitrary antecedent.  Such a
  contextual strengthening is not part of the background theory.

  CEV is repository terminology for the axiom presentation of C extended by
  the explicit vector rule.  Bacon calls the rule-closed system simply C and
  proves that it coincides with the Classical-identity presentation.  That
  converse reduction is now proved as CEV_proves_to_C in the downstream
  Bacon_C_Presentation_Development session. Its adapter explicitly reconciles
  this ascending de Bruijn argument list with the source-order abstraction
  theorem. The reduction is not built into this inductive definition.
\<close>

inductive CEV_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" ("_ \<turnstile>\<^sub>CEV _" [50, 50] 50) where
  CE[intro]: "\<Gamma> \<turnstile>\<^sub>CE A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A"
| VectorEquivalence[intro]:
    "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop \<Longrightarrow>
      \<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop \<Longrightarrow>
      \<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body \<sigma>s F G \<Longrightarrow>
      \<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type \<sigma>s Prop) F G"
| MP[intro]: "\<Gamma> \<turnstile>\<^sub>CEV A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV B"
| Gen[intro]: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift P) Q \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp P (Forall \<sigma> Q)"
| Inst[intro]: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    \<sigma> # \<Gamma> \<turnstile>\<^sub>CEV Imp P (shift Q) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"

lemma CEV_proves_formula:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  then show ?case
    by (rule CE_proves_formula)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  then show ?case
    by auto
next
  case (MP \<Gamma> A B)
  then show ?case
    by (auto elim: has_type.cases)
next
  case (Gen \<Gamma> P \<sigma> Q)
  then show ?case
    by auto
next
  case (Inst \<sigma> \<Gamma> P Q)
  then show ?case
    by auto
qed

lemma CEV_zeroary_equivalence:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A B"
proof -
  have zeta: "[] @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body [] A B"
    using assms(3) by (simp add: zeta_body_def fresh_vars_def)
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type [] Prop) A B"
  proof (rule CEV_proves.VectorEquivalence[where \<sigma>s = "[]" and F = A and G = B])
    show "\<Gamma> \<turnstile> A : arrow_type [] Prop"
      using assms(1) by simp
  next
    show "\<Gamma> \<turnstile> B : arrow_type [] Prop"
      using assms(2) by simp
  next
    show "[] @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body [] A B"
      using zeta .
  qed
  then show ?thesis
    by simp
qed

lemma CEV_unary_equivalence:
  assumes "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
    and "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o Prop"
    and "\<sigma> # \<Gamma> \<turnstile>\<^sub>CEV
      (App (shift F) (Var 0) \<longleftrightarrow>\<^sub>o App (shift G) (Var 0))"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Eq (\<sigma> \<rightarrow>\<^sub>o Prop) F G"
proof -
  have zeta: "[\<sigma>] @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body [\<sigma>] F G"
    using assms(3)
    by (simp add: zeta_body_def fresh_vars_def shift_by_1)
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type [\<sigma>] Prop) F G"
  proof (rule CEV_proves.VectorEquivalence[where \<sigma>s = "[\<sigma>]" and F = F and G = G])
    show "\<Gamma> \<turnstile> F : arrow_type [\<sigma>] Prop"
      using assms(1) by simp
  next
    show "\<Gamma> \<turnstile> G : arrow_type [\<sigma>] Prop"
      using assms(2) by simp
  next
    show "[\<sigma>] @ \<Gamma> \<turnstile>\<^sub>CEV zeta_body [\<sigma>] F G"
      using zeta .
  qed
  then show ?thesis
    by simp
qed

lemma CEV_restricted_necessitation:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A ObjTrue"
  shows "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o A"
  using assms by (simp add: ObjBox_def)

lemma CEV_necessitation_from_equivalence_to_truth:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o A"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A ObjTrue"
  proof (rule CEV_zeroary_equivalence)
    show "\<Gamma> \<turnstile> A : Prop"
      using assms(1) .
  next
    show "\<Gamma> \<turnstile> ObjTrue : Prop"
      by (rule typed_ObjTrue)
  next
    show "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o ObjTrue)"
      using assms(2) .
  qed
  then show ?thesis
    by (rule CEV_restricted_necessitation)
qed

lemma CEV_lifts_CE_box_truth:
  "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o ObjTrue"
  by (intro CEV_proves.CE CE_lifts_C_box_truth)

section \<open>Theoremhood as equivalence with truth\<close>

lemma H_proves_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>H ObjTrue"
proof -
  let ?P = "Imp ObjTrue ObjTrue"
  let ?Q = "Imp (Var 0) (Var 0)"
  have P_type: "\<Gamma> \<turnstile> ?P : Prop"
    by (intro has_type.Imp typed_ObjTrue)
  have Q_type: "Prop # \<Gamma> \<turnstile> ?Q : Prop"
    by auto
  have shifted_P_type: "Prop # \<Gamma> \<turnstile> shift ?P : Prop"
    using P_type by (rule weakening_front)
  have taut: "prop_tautology (Prop # \<Gamma>) (Imp (shift ?P) ?Q)"
    unfolding prop_tautology_def
    using shifted_P_type Q_type by auto
  have "\<Gamma> \<turnstile>\<^sub>H Imp ?P (Forall Prop ?Q)"
    using P_type Q_type H_proves.PC[OF taut]
    by (rule H_proves.Gen)
  moreover have "\<Gamma> \<turnstile>\<^sub>H ?P"
    by (intro H_imp_self typed_ObjTrue)
  ultimately have "\<Gamma> \<turnstile>\<^sub>H Forall Prop ?Q"
    by (metis H_proves.MP)
  then show ?thesis
    by (simp add: ObjTrue_def)
qed

lemma CEV_proves_ObjTrue:
  "\<Gamma> \<turnstile>\<^sub>CEV ObjTrue"
  by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves_ObjTrue)

lemma CEV_prop_tautology:
  assumes "prop_tautology \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
  using assms
  by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)

lemma CEV_imp_of_right_theorem:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile>\<^sub>CEV B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_proves_formula)
  have taut: "prop_tautology \<Gamma> (Imp B (Imp A B))"
    unfolding prop_tautology_def
    using assms(1) B_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Imp A B)"
    by (rule CEV_prop_tautology[OF taut])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(2)])
qed

lemma CEV_conj_intro:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
    and "\<Gamma> \<turnstile>\<^sub>CEV B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Conj A B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_proves_formula)
  have taut: "prop_tautology \<Gamma> (Imp A (Imp B (Conj A B)))"
    unfolding prop_tautology_def
    using A_type B_type by auto
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    by (rule CEV_prop_tautology[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>CEV Imp B (Conj A B)"
    by (rule CEV_proves.MP[OF assms(1)])
  then show ?thesis
    by (rule CEV_proves.MP[OF assms(2)])
qed

lemma CEV_biconditional_of_theorems:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
    and "\<Gamma> \<turnstile>\<^sub>CEV B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule CEV_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule CEV_proves_formula)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
    using A_type assms(2) by (rule CEV_imp_of_right_theorem)
  moreover have "\<Gamma> \<turnstile>\<^sub>CEV Imp B A"
    using B_type assms(1) by (rule CEV_imp_of_right_theorem)
  ultimately show ?thesis
    by (rule CEV_conj_intro)
qed

lemma CEV_theorem_equiv_ObjTrue:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o ObjTrue)"
  using assms CEV_proves_ObjTrue
  by (rule CEV_biconditional_of_theorems)

lemma CEV_theorem_to_truth_induction:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o ObjTrue)"
  using assms
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  have "\<Gamma> \<turnstile>\<^sub>CEV A"
    using CE.hyps by (rule CEV_proves.CE)
  then show ?case
    by (rule CEV_theorem_equiv_ObjTrue)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq (arrow_type \<sigma>s Prop) F G"
    using VectorEquivalence.hyps
    by (rule CEV_proves.VectorEquivalence)
  then show ?case
    by (rule CEV_theorem_equiv_ObjTrue)
next
  case (MP \<Gamma> A B)
  have "\<Gamma> \<turnstile>\<^sub>CEV B"
    using MP.hyps(1,2) by (rule CEV_proves.MP)
  then show ?case
    by (rule CEV_theorem_equiv_ObjTrue)
next
  case (Gen \<Gamma> P \<sigma> Q)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp P (Forall \<sigma> Q)"
    using Gen.hyps(1,2,3) by (rule CEV_proves.Gen)
  then show ?case
    by (rule CEV_theorem_equiv_ObjTrue)
next
  case (Inst \<sigma> \<Gamma> P Q)
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp (Exists \<sigma> P) Q"
    using Inst.hyps(1,2,3) by (rule CEV_proves.Inst)
  then show ?case
    by (rule CEV_theorem_equiv_ObjTrue)
qed

lemma CEV_necessitation:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o A"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms by (rule CEV_proves_formula)
  have "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o ObjTrue)"
    using assms by (rule CEV_theorem_to_truth_induction)
  then show ?thesis
    using A_type
    by (metis CEV_necessitation_from_equivalence_to_truth)
qed

text \<open>
  The theorem above packages the biconditional-to-truth step needed for
  unrestricted CEV necessitation.  Despite its historical name, it is not
  Bacon and Dorr's Appendix A induction establishing an identity between
  abstractions of a theorem and truth inside axiom-based C: each branch
  reconstructs its CEV conclusion and applies propositional reasoning.  The
  positive modal K, T, and 4 derivations are completed in \<open>Bacon_S4\<close>.
\<close>

end
