theory Bacon_Substitution
  imports Bacon_Typing
begin

section \<open>Renaming and substitution\<close>

text \<open>
  This theory implements the structural operations hidden by Bacon's written
  substitution notation:

  \<^item> \<open>rename \<rho> M\<close> systematically renames the free context slots of \<open>M\<close>;
  \<^item> \<open>shift M\<close> transports \<open>M\<close> beneath one new binder;
  \<^item> \<open>subst s M\<close> is simultaneous capture-avoiding substitution; and
  \<^item> \<open>subst0 N M\<close> is \<open>M[N/x]\<close> for the nearest binder slot.

  Lifting a renaming or substitution beneath a binder fixes the new variable at
  index zero and moves every older free slot past it.  In particular,
  \<open>shift (Var n) = Var (Suc n)\<close>, whereas a variable already bound inside a
  lambda remains bound.  The preservation theorems below assume that the
  renaming or substitution respects the types recorded in the source and target
  contexts; no claim is made for arbitrary replacements.
\<close>

fun lift_ren :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "lift_ren \<rho> 0 = 0"
| "lift_ren \<rho> (Suc n) = Suc (\<rho> n)"

fun rename :: "(nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> oterm" where
  "rename \<rho> (Var n) = Var (\<rho> n)"
| "rename \<rho> (Const c \<sigma>) = Const c \<sigma>"
| "rename \<rho> (App M N) = App (rename \<rho> M) (rename \<rho> N)"
| "rename \<rho> (Lam \<sigma> M) = Lam \<sigma> (rename (lift_ren \<rho>) M)"
| "rename \<rho> (Eq \<sigma> M N) = Eq \<sigma> (rename \<rho> M) (rename \<rho> N)"
| "rename \<rho> (Neg A) = Neg (rename \<rho> A)"
| "rename \<rho> (Conj A B) = Conj (rename \<rho> A) (rename \<rho> B)"
| "rename \<rho> (Disj A B) = Disj (rename \<rho> A) (rename \<rho> B)"
| "rename \<rho> (Imp A B) = Imp (rename \<rho> A) (rename \<rho> B)"
| "rename \<rho> (Forall \<sigma> A) = Forall \<sigma> (rename (lift_ren \<rho>) A)"
| "rename \<rho> (Exists \<sigma> A) = Exists \<sigma> (rename (lift_ren \<rho>) A)"

fun lift_subst :: "(nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm" where
  "lift_subst s 0 = Var 0"
| "lift_subst s (Suc n) = rename Suc (s n)"

fun subst :: "(nat \<Rightarrow> oterm) \<Rightarrow> oterm \<Rightarrow> oterm" where
  "subst s (Var n) = s n"
| "subst s (Const c \<sigma>) = Const c \<sigma>"
| "subst s (App M N) = App (subst s M) (subst s N)"
| "subst s (Lam \<sigma> M) = Lam \<sigma> (subst (lift_subst s) M)"
| "subst s (Eq \<sigma> M N) = Eq \<sigma> (subst s M) (subst s N)"
| "subst s (Neg A) = Neg (subst s A)"
| "subst s (Conj A B) = Conj (subst s A) (subst s B)"
| "subst s (Disj A B) = Disj (subst s A) (subst s B)"
| "subst s (Imp A B) = Imp (subst s A) (subst s B)"
| "subst s (Forall \<sigma> A) = Forall \<sigma> (subst (lift_subst s) A)"
| "subst s (Exists \<sigma> A) = Exists \<sigma> (subst (lift_subst s) A)"

definition shift :: "oterm \<Rightarrow> oterm" where
  "shift M = rename Suc M"

definition subst0 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "subst0 N M = subst (case_nat N Var) M"

lemma lookup_lift_ren:
  assumes "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (\<rho> n) = Some \<tau>"
  shows "lookup (\<sigma> # \<Gamma>) n = Some \<tau> \<Longrightarrow>
    lookup (\<sigma> # \<Delta>) (lift_ren \<rho> n) = Some \<tau>"
  using assms by (cases n) auto

lemma renaming_preserves_typing:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
    and "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> lookup \<Delta> (\<rho> n) = Some \<sigma>"
  shows "\<Delta> \<turnstile> rename \<rho> M : \<tau>"
  using assms
proof (induction arbitrary: \<Delta> \<rho> rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case
    by auto
next
  case (Const \<Gamma> c \<tau>)
  then show ?case
    by auto
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have "\<Delta> \<turnstile> rename \<rho> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using App.IH(1) App.prems by blast
  moreover have "\<Delta> \<turnstile> rename \<rho> N : \<sigma>"
    using App.IH(2) App.prems by blast
  ultimately show ?case
    by (simp add: has_type.App)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have "\<sigma> # \<Delta> \<turnstile> rename (lift_ren \<rho>) M : \<tau>"
    using Lam.IH Lam.prems by (metis lookup_lift_ren)
  then show ?case
    by (simp add: has_type.Lam)
next
  case (Eq \<Gamma> M \<sigma> N)
  then show ?case
    by auto
next
  case (Neg \<Gamma> A)
  then show ?case
    by auto
next
  case (Conj \<Gamma> A B)
  then show ?case
    by auto
next
  case (Disj \<Gamma> A B)
  then show ?case
    by auto
next
  case (Imp \<Gamma> A B)
  then show ?case
    by auto
next
  case (Forall \<sigma> \<Gamma> A)
  have "\<sigma> # \<Delta> \<turnstile> rename (lift_ren \<rho>) A : Prop"
    using Forall.IH Forall.prems by (metis lookup_lift_ren)
  then show ?case
    by (simp add: has_type.Forall)
next
  case (Exists \<sigma> \<Gamma> A)
  have "\<sigma> # \<Delta> \<turnstile> rename (lift_ren \<rho>) A : Prop"
    using Exists.IH Exists.prems by (metis lookup_lift_ren)
  then show ?case
    by (simp add: has_type.Exists)
qed

lemma weakening_front:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<sigma> # \<Gamma> \<turnstile> shift M : \<tau>"
  unfolding shift_def
  using assms
  by (rule renaming_preserves_typing) auto

lemma lift_subst_preserves_typing:
  assumes "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> \<Delta> \<turnstile> s n : \<sigma>"
    and "lookup (\<rho> # \<Gamma>) n = Some \<sigma>"
  shows "\<rho> # \<Delta> \<turnstile> lift_subst s n : \<sigma>"
  using assms(2)
proof (cases n)
  case 0
  then have "\<rho> = \<sigma>"
    using assms(2) by simp
  then show ?thesis
    using 0 by auto
next
  case (Suc m)
  then have "\<Delta> \<turnstile> s m : \<sigma>"
    using assms by auto
  then have "\<rho> # \<Delta> \<turnstile> rename Suc (s m) : \<sigma>"
    by (rule renaming_preserves_typing) auto
  with Suc show ?thesis
    by auto
qed

lemma substitution_preserves_typing:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
    and "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> \<Delta> \<turnstile> s n : \<sigma>"
  shows "\<Delta> \<turnstile> subst s M : \<tau>"
  using assms
proof (induction arbitrary: \<Delta> s rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case
    by auto
next
  case (Const \<Gamma> c \<tau>)
  then show ?case
    by auto
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have "\<Delta> \<turnstile> subst s M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using App.IH(1) App.prems by blast
  moreover have "\<Delta> \<turnstile> subst s N : \<sigma>"
    using App.IH(2) App.prems by blast
  ultimately show ?case
    by (simp add: has_type.App)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have "\<sigma> # \<Delta> \<turnstile> subst (lift_subst s) M : \<tau>"
    using Lam.IH Lam.prems by (metis lift_subst_preserves_typing)
  then show ?case
    by (simp add: has_type.Lam)
next
  case (Eq \<Gamma> M \<sigma> N)
  then show ?case
    by auto
next
  case (Neg \<Gamma> A)
  then show ?case
    by auto
next
  case (Conj \<Gamma> A B)
  then show ?case
    by auto
next
  case (Disj \<Gamma> A B)
  then show ?case
    by auto
next
  case (Imp \<Gamma> A B)
  then show ?case
    by auto
next
  case (Forall \<sigma> \<Gamma> A)
  have "\<sigma> # \<Delta> \<turnstile> subst (lift_subst s) A : Prop"
    using Forall.IH Forall.prems by (metis lift_subst_preserves_typing)
  then show ?case
    by (simp add: has_type.Forall)
next
  case (Exists \<sigma> \<Gamma> A)
  have "\<sigma> # \<Delta> \<turnstile> subst (lift_subst s) A : Prop"
    using Exists.IH Exists.prems by (metis lift_subst_preserves_typing)
  then show ?case
    by (simp add: has_type.Exists)
qed

lemma subst0_preserves_typing:
  assumes "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    and "\<Gamma> \<turnstile> N : \<sigma>"
  shows "\<Gamma> \<turnstile> subst0 N M : \<tau>"
  unfolding subst0_def
  using assms(1)
proof (rule substitution_preserves_typing)
  fix n \<rho>
  assume "lookup (\<sigma> # \<Gamma>) n = Some \<rho>"
  then show "\<Gamma> \<turnstile> case_nat N Var n : \<rho>"
    using assms(2) by (cases n) auto
qed

end
