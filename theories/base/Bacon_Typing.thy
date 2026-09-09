theory Bacon_Typing
  imports Bacon_Syntax
begin

section \<open>Typing\<close>

text \<open>
  A context \<open>\<Gamma> = [\<sigma>\<^sub>0, \<sigma>\<^sub>1, \<dots>]\<close> records the types of free de
  Bruijn slots, so \<open>Var n\<close> has the nth listed type.  Extending the context
  to \<open>\<sigma> # \<Gamma>\<close> corresponds to entering a binder for a variable of type
  \<open>\<sigma>\<close>.

  The judgment \<open>\<Gamma> \<turnstile> M : \<tau>\<close> is only a well-formedness assertion.  It
  must not be confused with theoremhood or consequence.  The executable
  function \<open>infer_type\<close> is proved sound and complete for this judgment, and
  \<open>typing_unique\<close> proves uniqueness of types.  A result of \<open>None\<close> means
  that the encoded term is ill-typed in the supplied context.
\<close>

type_synonym ctx = "otype list"

definition lookup :: "ctx \<Rightarrow> nat \<Rightarrow> otype option" where
  "lookup \<Gamma> n = (if n < length \<Gamma> then Some (\<Gamma> ! n) else None)"

inductive has_type :: "ctx \<Rightarrow> oterm \<Rightarrow> otype \<Rightarrow> bool"
    ("_ \<turnstile> _ : _" [50, 50, 50] 50) where
  Var[intro]: "lookup \<Gamma> n = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var n : \<tau>"
| Const[intro]: "\<Gamma> \<turnstile> Const c \<tau> : \<tau>"
| App[intro]: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> App M N : \<tau>"
| Lam[intro]: "\<sigma> # \<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Lam \<sigma> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
| Eq[intro]: "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Eq \<sigma> M N : Prop"
| Neg[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> Neg A : Prop"
| Conj[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow> \<Gamma> \<turnstile> Conj A B : Prop"
| Disj[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow> \<Gamma> \<turnstile> Disj A B : Prop"
| Imp[intro]: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow> \<Gamma> \<turnstile> Imp A B : Prop"
| Forall[intro]: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> Forall \<sigma> A : Prop"
| Exists[intro]: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> Exists \<sigma> A : Prop"

lemma lookup_Cons_0[simp]:
  "lookup (\<sigma> # \<Gamma>) 0 = Some \<sigma>"
  by (simp add: lookup_def)

lemma lookup_Cons_Suc[simp]:
  "lookup (\<sigma> # \<Gamma>) (Suc n) = lookup \<Gamma> n"
  by (simp add: lookup_def)

lemma Var_typed_iff[simp]:
  "\<Gamma> \<turnstile> Var n : \<tau> \<longleftrightarrow> lookup \<Gamma> n = Some \<tau>"
  by (auto elim: has_type.cases)

fun infer_type :: "ctx \<Rightarrow> oterm \<Rightarrow> otype option" where
  "infer_type \<Gamma> (Var n) = lookup \<Gamma> n"
| "infer_type \<Gamma> (Const c \<sigma>) = Some \<sigma>"
| "infer_type \<Gamma> (App M N) =
    (case infer_type \<Gamma> M of
      Some (\<sigma> \<rightarrow>\<^sub>o \<tau>) =>
        (case infer_type \<Gamma> N of
          Some \<rho> => (if \<rho> = \<sigma> then Some \<tau> else None)
        | None => None)
    | Some Ind => None
    | Some Prop => None
    | None => None)"
| "infer_type \<Gamma> (Lam \<sigma> M) =
    map_option (Arr \<sigma>) (infer_type (\<sigma> # \<Gamma>) M)"
| "infer_type \<Gamma> (Eq \<sigma> M N) =
    (case (infer_type \<Gamma> M, infer_type \<Gamma> N) of
      (Some \<rho>, Some \<tau>) => (if \<rho> = \<sigma> \<and> \<tau> = \<sigma> then Some Prop else None)
    | _ => None)"
| "infer_type \<Gamma> (Neg A) =
    (case infer_type \<Gamma> A of Some Prop => Some Prop | _ => None)"
| "infer_type \<Gamma> (Conj A B) =
    (case (infer_type \<Gamma> A, infer_type \<Gamma> B) of
      (Some Prop, Some Prop) => Some Prop
    | _ => None)"
| "infer_type \<Gamma> (Disj A B) =
    (case (infer_type \<Gamma> A, infer_type \<Gamma> B) of
      (Some Prop, Some Prop) => Some Prop
    | _ => None)"
| "infer_type \<Gamma> (Imp A B) =
    (case (infer_type \<Gamma> A, infer_type \<Gamma> B) of
      (Some Prop, Some Prop) => Some Prop
    | _ => None)"
| "infer_type \<Gamma> (Forall \<sigma> A) =
    (case infer_type (\<sigma> # \<Gamma>) A of Some Prop => Some Prop | _ => None)"
| "infer_type \<Gamma> (Exists \<sigma> A) =
    (case infer_type (\<sigma> # \<Gamma>) A of Some Prop => Some Prop | _ => None)"

lemma infer_type_sound:
  "infer_type \<Gamma> M = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> M : \<tau>"
proof (induction M arbitrary: \<Gamma> \<tau>)
  case (Var x)
  then show ?case
    by auto
next
  case (Const x1 x2)
  then show ?case
    by auto
next
  case (App M N)
  then obtain \<sigma> where
    M_type: "infer_type \<Gamma> M = Some (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and N_type: "infer_type \<Gamma> N = Some \<sigma>"
    by (auto split: option.splits otype.splits if_splits)
  from App.IH(1)[OF M_type] App.IH(2)[OF N_type] show ?case
    by (rule has_type.App)
next
  case (Lam \<sigma> M)
  then show ?case
    by (auto split: option.splits)
next
  case (Eq \<sigma> M N)
  then show ?case
    by (auto split: option.splits if_splits)
next
  case (Neg M)
  then show ?case
    by (auto split: option.splits otype.splits)
next
  case (Conj M1 M2)
  then show ?case
    by (auto split: option.splits otype.splits)
next
  case (Disj M1 M2)
  then show ?case
    by (auto split: option.splits otype.splits)
next
  case (Imp M1 M2)
  then show ?case
    by (auto split: option.splits otype.splits)
next
  case (Forall \<sigma> M)
  then show ?case
    by (auto split: option.splits otype.splits)
next
  case (Exists \<sigma> M)
  then show ?case
    by (auto split: option.splits otype.splits)
qed

lemma infer_type_complete:
  "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> infer_type \<Gamma> M = Some \<tau>"
  by (induction rule: has_type.induct) auto

lemma typing_unique:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<sigma> = \<tau>"
proof -
  have "infer_type \<Gamma> M = Some \<sigma>"
    using assms(1) by (rule infer_type_complete)
  moreover have "infer_type \<Gamma> M = Some \<tau>"
    using assms(2) by (rule infer_type_complete)
  ultimately show ?thesis
    by simp
qed

lemma typed_identity:
  "\<Gamma> \<turnstile> Lam \<sigma> (Var 0) : \<sigma> \<rightarrow>\<^sub>o \<sigma>"
  by auto

lemma typed_object_universal_identity:
  "\<Gamma> \<turnstile> Forall \<sigma> (Eq \<sigma> (Var 0) (Var 0)) : Prop"
  by (intro has_type.Forall has_type.Eq has_type.Var) simp_all

end
