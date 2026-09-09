theory Bacon_Source_Relational_Naming_Replacement
  imports Bacon_Source_Relational_Naming_Charts
begin

section \<open>Replacing the finitely many new names by chart variables\<close>

text \<open>
  Old Inl(c) constants return to the original name carrier. A new typed
  constant Inr(a):σ becomes the variable x(σ,a); binders and logical
  symbols remain literal. The replacement function is not traversed as
  syntax, and no recursively assigned payload is involved.

  Avoiding all original variable names ensures every introduced marker
  remains free. The typing and signature lemmas themselves require no
  semantic model, closed representative, or globally fresh variable map.
\<close>

fun paper_R_naming_replace ::
  "((otype \<times> 'v) \<Rightarrow> nat) \<Rightarrow> ('c + 'v, 'l) named_term \<Rightarrow> ('c, 'l) named_term" where
  "paper_R_naming_replace x (NVar n) = NVar n"
| "paper_R_naming_replace x (NConst c \<sigma>) =
    (case c of Inl b \<Rightarrow> NConst b \<sigma> | Inr a \<Rightarrow> NVar (x (\<sigma>,a)))"
| "paper_R_naming_replace x (NLogical l) = NLogical l"
| "paper_R_naming_replace x (NApp F A) = NApp (paper_R_naming_replace x F) (paper_R_naming_replace x A)"
| "paper_R_naming_replace x (NLam n A) = NLam n (paper_R_naming_replace x A)"

lemma paper_R_naming_replace_old:
  "paper_R_naming_replace x (map_named_term Inl id A) = A"
  by (induction A) simp_all

lemma paper_R_naming_replace_chart_agreement:
  assumes same: "\<And>k. k \<in> paper_R_naming_support A \<Longrightarrow> x k = y k"
  shows "paper_R_naming_replace x A = paper_R_naming_replace y A"
  using same by (induction A) (auto split: sum.splits)

lemma paper_R_naming_replace_signature:
  assumes names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
  shows "named_in_signature \<Sigma> (paper_R_naming_replace x A)"
  using names by (induction A) (auto split: sum.splits)

lemma paper_R_naming_replace_type:
  assumes typed: "paper_R_has_type G A \<tau>"
    and chart_types: "\<forall>k\<in>paper_R_naming_support A. G (x k) = fst k"
  shows "paper_R_has_type G (paper_R_naming_replace x A) \<tau>"
  using typed chart_types
proof (induction rule: paper_R_has_type.induct)
  case (Var n)
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule paper_R_has_type.Var[where G=G and n=n, OF Var.hyps])
next
  case (Const \<sigma> c)
  show ?case
  proof (cases c)
    case (Inl b)
    show ?thesis by (simp only: Inl paper_R_naming_replace.simps sum.case;
      rule paper_R_has_type.Const[OF Const.hyps])
  next
    case (Inr a)
    have nt: "G (x (\<sigma>,a)) = \<sigma>" using Const.prems by (simp add: Inr)
    have rt: "paper_R_type (G (x (\<sigma>,a)))" by (simp only: nt; rule Const.hyps)
    have variable: "paper_R_has_type G (NVar (x (\<sigma>,a))) (G (x (\<sigma>,a)))"
      by (rule paper_R_has_type.Var[where G=G and n="x (\<sigma>,a)", OF rt])
    show ?thesis using variable by (simp only: Inr paper_R_naming_replace.simps sum.case nt)
  qed
next
  case (Logical l)
  show ?case by (simp only: paper_R_naming_replace.simps; rule paper_R_has_type.Logical[OF Logical.hyps])
next
  case (App F \<sigma> \<tau> A)
  have ft: "\<forall>k\<in>paper_R_naming_support F. G (x k) = fst k"
    and at: "\<forall>k\<in>paper_R_naming_support A. G (x k) = fst k" using App.prems by auto
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule paper_R_has_type.App[OF App.IH(1)[OF ft] App.IH(2)[OF at]])
next
  case (Lam A \<tau> n)
  have body: "\<forall>k\<in>paper_R_naming_support A. G (x k) = fst k" using Lam.prems by simp
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule paper_R_has_type.Lam[OF Lam.IH[OF body] Lam.hyps(2,3)])
qed

theorem paper_R_naming_replace_language:
  assumes language: "paper_R_in_language (paper_R_naming_signature \<Sigma> D) G A \<tau>"
    and chart: "paper_R_naming_chart G K N x" and support: "paper_R_naming_support A \<subseteq> K"
  shows "paper_R_in_language \<Sigma> G (paper_R_naming_replace x A) \<tau>"
proof -
  have typed: "paper_R_has_type G A \<tau>"
    and names: "named_in_signature (paper_R_naming_signature \<Sigma> D) A"
    using language unfolding paper_R_in_language_def by blast+
  have chart_types: "\<forall>k\<in>paper_R_naming_support A. G (x k) = fst k"
    using chart support unfolding paper_R_naming_chart_def by blast
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_naming_replace_type[OF typed chart_types]
      paper_R_naming_replace_signature[OF names]])
qed

section \<open>Free variables and the no-capture guard\<close>

lemma paper_R_naming_replace_vars:
  "named_vars (paper_R_naming_replace x A) = named_vars A \<union> x ` paper_R_naming_support A"
  by (induction A) (auto split: sum.splits)

lemma paper_R_naming_replace_fv_bound:
  "named_fv (paper_R_naming_replace x A) \<subseteq> named_fv A \<union> x ` paper_R_naming_support A"
  by (induction A) (auto split: sum.splits)

lemma paper_R_naming_replace_fv:
  assumes fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_fv (paper_R_naming_replace x A) = named_fv A \<union> x ` paper_R_naming_support A"
  using fresh
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  show ?case by (cases c) simp_all
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have ff: "x ` paper_R_naming_support F \<inter> named_vars F = {}"
    and af: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
    using NApp.prems by auto
  show ?case using NApp.IH(1)[OF ff] NApp.IH(2)[OF af] by auto
next
  case (NLam n A)
  have body_fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
    and binder_fresh: "n \<notin> x ` paper_R_naming_support A"
    using NLam.prems by auto
  show ?case using NLam.IH[OF body_fresh] binder_fresh by auto
qed

theorem paper_R_naming_replace_chart_fv:
  assumes chart: "paper_R_naming_chart G K N x"
    and support: "paper_R_naming_support A \<subseteq> K" and avoid: "named_vars A \<subseteq> N"
  shows "named_fv (paper_R_naming_replace x A) = named_fv A \<union> x ` paper_R_naming_support A"
proof (rule paper_R_naming_replace_fv)
  show "x ` paper_R_naming_support A \<inter> named_vars A = {}"
    using chart support avoid unfolding paper_R_naming_chart_def by blast
qed

corollary paper_R_naming_replace_marker_free:
  assumes chart: "paper_R_naming_chart G K N x"
    and support: "paper_R_naming_support A \<subseteq> K" and avoid: "named_vars A \<subseteq> N"
    and member: "k \<in> paper_R_naming_support A"
  shows "x k \<in> named_fv (paper_R_naming_replace x A)"
  using paper_R_naming_replace_chart_fv[OF chart support avoid] member by blast

end
