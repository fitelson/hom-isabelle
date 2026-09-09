theory Bacon_Parametric_Substitution
  imports Bacon_Parametric_Syntax
begin

section \<open>Renaming and capture-avoiding substitution\<close>

text \<open>
  A[s] denotes simultaneous substitution; A[B/v] substitutes B for v.
  Beneath λv.A, the new bound variable is fixed and older free variables
  move past it, so substitution does not capture free variables of B.

  Isabelle representation: prename acts on de Bruijn slots; pshift inserts
  a slot; psubst and psubst0 implement the two substitutions.  lift_ren and
  plift_subst preserve slot zero when passing beneath a binder.

  Status: structural operations for arbitrary name carriers.  This file
  proves typing/signature preservation and string correspondence, not an
  object-language identity or a semantic substitution theorem.
\<close>

fun prename :: "(nat \<Rightarrow> nat) \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "prename r (PVar n) = PVar (r n)"
| "prename r (PConst c \<sigma>) = PConst c \<sigma>"
| "prename r (PApp M N) = PApp (prename r M) (prename r N)"
| "prename r (PLam \<sigma> M) = PLam \<sigma> (prename (lift_ren r) M)"
| "prename r (PEq \<sigma> M N) = PEq \<sigma> (prename r M) (prename r N)"
| "prename r (PNeg A) = PNeg (prename r A)"
| "prename r (PConj A B) = PConj (prename r A) (prename r B)"
| "prename r (PDisj A B) = PDisj (prename r A) (prename r B)"
| "prename r (PImp A B) = PImp (prename r A) (prename r B)"
| "prename r (PForall \<sigma> A) = PForall \<sigma> (prename (lift_ren r) A)"
| "prename r (PExists \<sigma> A) = PExists \<sigma> (prename (lift_ren r) A)"

definition pshift :: "'c pterm \<Rightarrow> 'c pterm" where
  "pshift M = prename Suc M"

fun plift_subst :: "(nat \<Rightarrow> 'c pterm) \<Rightarrow> nat \<Rightarrow> 'c pterm" where
  "plift_subst s 0 = PVar 0"
| "plift_subst s (Suc n) = prename Suc (s n)"

fun psubst :: "(nat \<Rightarrow> 'c pterm) \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "psubst s (PVar n) = s n"
| "psubst s (PConst c \<sigma>) = PConst c \<sigma>"
| "psubst s (PApp M N) = PApp (psubst s M) (psubst s N)"
| "psubst s (PLam \<sigma> M) = PLam \<sigma> (psubst (plift_subst s) M)"
| "psubst s (PEq \<sigma> M N) = PEq \<sigma> (psubst s M) (psubst s N)"
| "psubst s (PNeg A) = PNeg (psubst s A)"
| "psubst s (PConj A B) = PConj (psubst s A) (psubst s B)"
| "psubst s (PDisj A B) = PDisj (psubst s A) (psubst s B)"
| "psubst s (PImp A B) = PImp (psubst s A) (psubst s B)"
| "psubst s (PForall \<sigma> A) = PForall \<sigma> (psubst (plift_subst s) A)"
| "psubst s (PExists \<sigma> A) = PExists \<sigma> (psubst (plift_subst s) A)"

definition psubst0 :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "psubst0 T A = psubst (case_nat T PVar) A"

section \<open>Typing preservation\<close>

text \<open>
  If Γ ⊢ A:τ and the substituted terms have the declared variable types,
  then substitution preserves A:τ.

  Isabelle representation: prename_preserves_typing and psubst_preserves_typing
  carry explicit type-respecting map hypotheses; psubst0_preserves_typing
  specializes to A[B/v].

  Status: structural preservation only; arbitrary untyped substitutions are
  not covered.
\<close>

lemma prename_preserves_typing:
  assumes typed: "has_ptype \<Gamma> M \<tau>"
    and ren: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      lookup \<Delta> (r n) = Some \<sigma>"
  shows "has_ptype \<Delta> (prename r M) \<tau>"
  using typed ren
proof (induction arbitrary: \<Delta> r rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  have "lookup \<Delta> (r n) = Some \<tau>" using PVar.hyps by (rule PVar.prems)
  then show ?case by (simp only: prename.simps; rule has_ptype.PVar)
next
  case (PConst \<Gamma> c \<tau>)
  show ?case by (simp only: prename.simps; rule has_ptype.PConst)
next
  case (PApp \<Gamma> M \<sigma> \<tau> N)
  have M: "has_ptype \<Delta> (prename r M) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    using PApp.prems by (rule PApp.IH(1))
  have N: "has_ptype \<Delta> (prename r N) \<sigma>"
    using PApp.prems by (rule PApp.IH(2))
  show ?case by (simp only: prename.simps; rule has_ptype.PApp[OF M N])
next
  case (PLam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<rho>"
    by (rule lookup_lift_ren[OF PLam.prems])
  have "has_ptype (\<sigma> # \<Delta>) (prename (lift_ren r) M) \<tau>"
    using lifted by (rule PLam.IH)
  then show ?case by (simp only: prename.simps; rule has_ptype.PLam)
next
  case (PEq \<Gamma> M \<sigma> N)
  have M: "has_ptype \<Delta> (prename r M) \<sigma>" using PEq.prems by (rule PEq.IH(1))
  have N: "has_ptype \<Delta> (prename r N) \<sigma>" using PEq.prems by (rule PEq.IH(2))
  show ?case by (simp only: prename.simps; rule has_ptype.PEq[OF M N])
next
  case (PNeg \<Gamma> A)
  have "has_ptype \<Delta> (prename r A) Prop" using PNeg.prems by (rule PNeg.IH)
  then show ?case by (simp only: prename.simps; rule has_ptype.PNeg)
next
  case (PConj \<Gamma> A B)
  have A: "has_ptype \<Delta> (prename r A) Prop" using PConj.prems by (rule PConj.IH(1))
  have B: "has_ptype \<Delta> (prename r B) Prop" using PConj.prems by (rule PConj.IH(2))
  show ?case by (simp only: prename.simps; rule has_ptype.PConj[OF A B])
next
  case (PDisj \<Gamma> A B)
  have A: "has_ptype \<Delta> (prename r A) Prop" using PDisj.prems by (rule PDisj.IH(1))
  have B: "has_ptype \<Delta> (prename r B) Prop" using PDisj.prems by (rule PDisj.IH(2))
  show ?case by (simp only: prename.simps; rule has_ptype.PDisj[OF A B])
next
  case (PImp \<Gamma> A B)
  have A: "has_ptype \<Delta> (prename r A) Prop" using PImp.prems by (rule PImp.IH(1))
  have B: "has_ptype \<Delta> (prename r B) Prop" using PImp.prems by (rule PImp.IH(2))
  show ?case by (simp only: prename.simps; rule has_ptype.PImp[OF A B])
next
  case (PForall \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<rho>"
    by (rule lookup_lift_ren[OF PForall.prems])
  have "has_ptype (\<sigma> # \<Delta>) (prename (lift_ren r) A) Prop"
    using lifted by (rule PForall.IH)
  then show ?case by (simp only: prename.simps; rule has_ptype.PForall)
next
  case (PExists \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      lookup (\<sigma> # \<Delta>) (lift_ren r n) = Some \<rho>"
    by (rule lookup_lift_ren[OF PExists.prems])
  have "has_ptype (\<sigma> # \<Delta>) (prename (lift_ren r) A) Prop"
    using lifted by (rule PExists.IH)
  then show ?case by (simp only: prename.simps; rule has_ptype.PExists)
qed

lemma pshift_preserves_typing:
  assumes "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype (\<sigma> # \<Gamma>) (pshift M) \<tau>"
  unfolding pshift_def
  by (rule prename_preserves_typing[OF assms]) simp

lemma plift_subst_preserves_typing:
  assumes sub: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> has_ptype \<Delta> (s n) \<sigma>"
    and look: "lookup (\<rho> # \<Gamma>) n = Some \<sigma>"
  shows "has_ptype (\<rho> # \<Delta>) (plift_subst s n) \<sigma>"
proof (cases n)
  case 0
  have "\<sigma> = \<rho>" using look by (simp add: 0)
  then show ?thesis using 0 by (simp add: has_ptype.PVar)
next
  case (Suc m)
  have old: "lookup \<Gamma> m = Some \<sigma>" using look by (simp add: Suc)
  have typed: "has_ptype \<Delta> (s m) \<sigma>" by (rule sub[OF old])
  have shifted: "has_ptype (\<rho> # \<Delta>) (pshift (s m)) \<sigma>"
    by (rule pshift_preserves_typing[OF typed])
  show ?thesis using shifted by (simp add: Suc pshift_def)
qed

lemma psubst_preserves_typing:
  assumes typed: "has_ptype \<Gamma> M \<tau>"
    and sub: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> has_ptype \<Delta> (s n) \<sigma>"
  shows "has_ptype \<Delta> (psubst s M) \<tau>"
  using typed sub
proof (induction arbitrary: \<Delta> s rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  have "has_ptype \<Delta> (s n) \<tau>" by (rule PVar.prems[OF PVar.hyps])
  then show ?case by simp
next
  case (PConst \<Gamma> c \<tau>)
  show ?case by (simp only: psubst.simps; rule has_ptype.PConst)
next
  case (PApp \<Gamma> M \<sigma> \<tau> N)
  have M: "has_ptype \<Delta> (psubst s M) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    using PApp.prems by (rule PApp.IH(1))
  have N: "has_ptype \<Delta> (psubst s N) \<sigma>" using PApp.prems by (rule PApp.IH(2))
  show ?case by (simp only: psubst.simps; rule has_ptype.PApp[OF M N])
next
  case (PLam \<sigma> \<Gamma> M \<tau>)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      has_ptype (\<sigma> # \<Delta>) (plift_subst s n) \<rho>"
    by (rule plift_subst_preserves_typing[OF PLam.prems])
  have "has_ptype (\<sigma> # \<Delta>) (psubst (plift_subst s) M) \<tau>"
    using lifted by (rule PLam.IH)
  then show ?case by (simp only: psubst.simps; rule has_ptype.PLam)
next
  case (PEq \<Gamma> M \<sigma> N)
  have M: "has_ptype \<Delta> (psubst s M) \<sigma>" using PEq.prems by (rule PEq.IH(1))
  have N: "has_ptype \<Delta> (psubst s N) \<sigma>" using PEq.prems by (rule PEq.IH(2))
  show ?case by (simp only: psubst.simps; rule has_ptype.PEq[OF M N])
next
  case (PNeg \<Gamma> A)
  have "has_ptype \<Delta> (psubst s A) Prop" using PNeg.prems by (rule PNeg.IH)
  then show ?case by (simp only: psubst.simps; rule has_ptype.PNeg)
next
  case (PConj \<Gamma> A B)
  have A: "has_ptype \<Delta> (psubst s A) Prop" using PConj.prems by (rule PConj.IH(1))
  have B: "has_ptype \<Delta> (psubst s B) Prop" using PConj.prems by (rule PConj.IH(2))
  show ?case by (simp only: psubst.simps; rule has_ptype.PConj[OF A B])
next
  case (PDisj \<Gamma> A B)
  have A: "has_ptype \<Delta> (psubst s A) Prop" using PDisj.prems by (rule PDisj.IH(1))
  have B: "has_ptype \<Delta> (psubst s B) Prop" using PDisj.prems by (rule PDisj.IH(2))
  show ?case by (simp only: psubst.simps; rule has_ptype.PDisj[OF A B])
next
  case (PImp \<Gamma> A B)
  have A: "has_ptype \<Delta> (psubst s A) Prop" using PImp.prems by (rule PImp.IH(1))
  have B: "has_ptype \<Delta> (psubst s B) Prop" using PImp.prems by (rule PImp.IH(2))
  show ?case by (simp only: psubst.simps; rule has_ptype.PImp[OF A B])
next
  case (PForall \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      has_ptype (\<sigma> # \<Delta>) (plift_subst s n) \<rho>"
    by (rule plift_subst_preserves_typing[OF PForall.prems])
  have "has_ptype (\<sigma> # \<Delta>) (psubst (plift_subst s) A) Prop"
    using lifted by (rule PForall.IH)
  then show ?case by (simp only: psubst.simps; rule has_ptype.PForall)
next
  case (PExists \<sigma> \<Gamma> A)
  have lifted: "\<And>n \<rho>. lookup (\<sigma> # \<Gamma>) n = Some \<rho> \<Longrightarrow>
      has_ptype (\<sigma> # \<Delta>) (plift_subst s n) \<rho>"
    by (rule plift_subst_preserves_typing[OF PExists.prems])
  have "has_ptype (\<sigma> # \<Delta>) (psubst (plift_subst s) A) Prop"
    using lifted by (rule PExists.IH)
  then show ?case by (simp only: psubst.simps; rule has_ptype.PExists)
qed

lemma psubst0_preserves_typing:
  assumes "has_ptype (\<sigma> # \<Gamma>) A \<tau>" and "has_ptype \<Gamma> T \<sigma>"
  shows "has_ptype \<Gamma> (psubst0 T A) \<tau>"
  unfolding psubst0_def
proof (rule psubst_preserves_typing[OF assms(1)])
  fix n \<rho>
  assume look: "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
  show "has_ptype \<Gamma> (case_nat T PVar n) \<rho>"
    using look assms(2) by (cases n) (auto intro: has_ptype.PVar)
qed

section \<open>Signature preservation\<close>

text \<open>
  A ∈ ℒ(Σ) and every Bᵢ ∈ ℒ(Σ) imply A[Bᵢ/vᵢ] ∈ ℒ(Σ).

  Isabelle representation: prename_signature leaves constants unchanged;
  plift_subst_signature and psubst_signature check inserted terms.

  Status: substitution introduces no undeclared constant when the displayed
  membership hypotheses hold.
\<close>

lemma prename_signature[simp]:
  "pterm_in_signature \<Sigma> (prename r M) = pterm_in_signature \<Sigma> M"
  by (induction M arbitrary: r) simp_all

lemma plift_subst_signature:
  assumes "\<And>n. pterm_in_signature \<Sigma> (s n)"
  shows "pterm_in_signature \<Sigma> (plift_subst s n)"
  using assms by (cases n) simp_all

lemma psubst_signature:
  assumes "pterm_in_signature \<Sigma> M" and "\<And>n. pterm_in_signature \<Sigma> (s n)"
  shows "pterm_in_signature \<Sigma> (psubst s M)"
  using assms
proof (induction M arbitrary: s)
  case (PLam \<sigma> M)
  have "pterm_in_signature \<Sigma> (psubst (plift_subst s) M)"
    using PLam.prems by (intro PLam.IH plift_subst_signature) simp_all
  then show ?case by simp
next
  case (PForall \<sigma> M)
  have "pterm_in_signature \<Sigma> (psubst (plift_subst s) M)"
    using PForall.prems by (intro PForall.IH plift_subst_signature) simp_all
  then show ?case by simp
next
  case (PExists \<sigma> M)
  have "pterm_in_signature \<Sigma> (psubst (plift_subst s) M)"
    using PExists.prems by (intro PExists.IH plift_subst_signature) simp_all
  then show ?case by simp
qed simp_all

section \<open>String-instance translation commutes with the operations\<close>

text \<open>
  Translation commutes with λv.A, free-variable renaming, and A[B/v].

  Isabelle representation: pterm_to_prename, pterm_to_psubst, and their inverse
  counterparts compare the parametric and existing string representations.

  Status: exact syntactic commuting equations; semantic substitution is
  proved separately in BBK_Semantics.
\<close>

lemma pterm_to_prename:
  "pterm_to_oterm (prename r M) = rename r (pterm_to_oterm M)"
  by (induction M arbitrary: r) simp_all

lemma pterm_to_plift_subst:
  "pterm_to_oterm (plift_subst s n) = lift_subst (\<lambda>n. pterm_to_oterm (s n)) n"
  by (cases n) (simp_all add: pterm_to_prename)

lemma pterm_to_psubst:
  "pterm_to_oterm (psubst s M) =
    subst (\<lambda>n. pterm_to_oterm (s n)) (pterm_to_oterm M)"
  by (induction M arbitrary: s) (simp_all add: pterm_to_plift_subst)

lemma pterm_to_pshift:
  "pterm_to_oterm (pshift M) = shift (pterm_to_oterm M)"
  by (simp add: pshift_def shift_def pterm_to_prename)

lemma pterm_to_psubst0:
  "pterm_to_oterm (psubst0 T A) = subst0 (pterm_to_oterm T) (pterm_to_oterm A)"
proof -
  have maps_eq: "(\<lambda>n. pterm_to_oterm (case_nat T PVar n)) =
      case_nat (pterm_to_oterm T) Var"
    by (rule ext) (case_tac n; simp)
  show ?thesis by (simp add: psubst0_def subst0_def pterm_to_psubst maps_eq)
qed

lemma pterm_to_injective:
  assumes "pterm_to_oterm M = pterm_to_oterm N"
  shows "M = N"
proof -
  have "pterm_of_oterm (pterm_to_oterm M) = pterm_of_oterm (pterm_to_oterm N)"
    by (rule arg_cong[OF assms])
  then show ?thesis by simp
qed

lemma pterm_of_rename:
  "pterm_of_oterm (rename r M) = prename r (pterm_of_oterm M)"
  by (rule pterm_to_injective) (simp add: pterm_to_prename)

lemma pterm_of_subst:
  "pterm_of_oterm (subst s M) = psubst (\<lambda>n. pterm_of_oterm (s n)) (pterm_of_oterm M)"
  by (rule pterm_to_injective) (simp add: pterm_to_psubst)

lemma pterm_of_shift:
  "pterm_of_oterm (shift M) = pshift (pterm_of_oterm M)"
  by (rule pterm_to_injective) (simp add: pterm_to_pshift)

lemma pterm_of_subst0:
  "pterm_of_oterm (subst0 T A) = psubst0 (pterm_of_oterm T) (pterm_of_oterm A)"
  by (rule pterm_to_injective) (simp add: pterm_to_psubst0)

end
