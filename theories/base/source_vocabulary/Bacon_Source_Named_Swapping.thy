theory Bacon_Source_Named_Swapping
  imports Bacon_Source_Named_Syntax
begin

section \<open>Finite swaps of variable and binder names\<close>

text \<open>
  Exchanging names x and y everywhere in a named term is an involution.
  When G x = G y, this operation preserves the fixed typing stock.
  Source role: capture-safe bound-name change for the named λ syntax of
  Bacon–Dorr §1.1, p.5, and the capture proviso in Figure 2, p.8.

  Isabelle representation.  named_swap exchanges both NVar occurrences
  and NLam binder names, including shadowed binders.  Constants and logical
  symbols are unchanged.  This is a total finite permutation, not a
  capture-avoiding substitution operation.  The following leaf restricts
  its use as a bound-name-change generator by an explicit freshness guard.
  No α quotient, representation equality, theoremhood, or model claim is
  assumed here.
\<close>

definition named_swap_index :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "named_swap_index x y n = (if n = x then y else if n = y then x else n)"

lemma named_swap_index_left[simp]: "named_swap_index x y x = y"
  by (simp add: named_swap_index_def)

lemma named_swap_index_right[simp]: "named_swap_index x y y = x"
  by (simp add: named_swap_index_def)

lemma named_swap_index_involution[simp]: "named_swap_index x y (named_swap_index x y n) = n"
  by (auto simp: named_swap_index_def split: if_splits)

lemma named_swap_index_inj: "inj (named_swap_index x y)"
proof (rule injI)
  fix m n
  assume eq: "named_swap_index x y m = named_swap_index x y n"
  have twice: "named_swap_index x y (named_swap_index x y m) = named_swap_index x y (named_swap_index x y n)"
    by (rule arg_cong[where f="named_swap_index x y", OF eq])
  show "m = n" using twice by (simp only: named_swap_index_involution)
qed

lemma named_swap_index_type:
  "G x = G y \<Longrightarrow> G (named_swap_index x y n) = G n"
  by (auto simp: named_swap_index_def split: if_splits)

fun named_swap :: "nat \<Rightarrow> nat \<Rightarrow> ('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term" where
  "named_swap x y (NVar n) = NVar (named_swap_index x y n)"
| "named_swap x y (NConst c \<sigma>) = NConst c \<sigma>"
| "named_swap x y (NLogical l) = NLogical l"
| "named_swap x y (NApp F A) = NApp (named_swap x y F) (named_swap x y A)"
| "named_swap x y (NLam n A) = NLam (named_swap_index x y n) (named_swap x y A)"

lemma named_swap_involution: "named_swap x y (named_swap x y A) = A"
  by (induction A) simp_all

lemma named_swap_signature:
  "named_in_signature \<Sigma> (named_swap x y A) = named_in_signature \<Sigma> A"
  by (induction A) simp_all

lemma named_swap_image_remove:
  "named_swap_index x y ` (X - {n}) = named_swap_index x y ` X - {named_swap_index x y n}"
  using named_swap_index_inj[where x=x and y=y]
  by (auto simp: image_iff dest: injD)

lemma named_swap_fv:
  "named_fv (named_swap x y A) = named_swap_index x y ` named_fv A"
  by (induction A) (simp_all add: image_Un named_swap_image_remove)

lemma named_swap_vars:
  "named_vars (named_swap x y A) = named_swap_index x y ` named_vars A"
  by (induction A) (simp_all add: image_Un)

lemma named_swap_type:
  assumes same_type: "G x = G y" and typed: "has_ntype L G A \<tau>"
  shows "has_ntype L G (named_swap x y A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case (Var n)
  have variable: "has_ntype L G (NVar (named_swap_index x y n)) (G (named_swap_index x y n))"
    by (rule has_ntype.Var)
  show ?case using variable by (simp only: named_swap.simps named_swap_index_type[OF same_type])
next
  case (Const c \<sigma>)
  show ?case by (simp only: named_swap.simps) (rule has_ntype.Const)
next
  case (Logical l)
  show ?case by (simp only: named_swap.simps) (rule has_ntype.Logical)
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: named_swap.simps) (rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  have abstraction: "has_ntype L G (NLam (named_swap_index x y n) (named_swap x y A))
    (Arr (G (named_swap_index x y n)) \<tau>)" by (rule has_ntype.Lam[OF Lam.IH])
  show ?case using abstraction by (simp only: named_swap.simps named_swap_index_type[OF same_type])
qed

lemma named_swap_type_iff:
  assumes same_type: "G x = G y"
  shows "has_ntype L G (named_swap x y A) \<tau> \<longleftrightarrow> has_ntype L G A \<tau>"
proof
  assume typed: "has_ntype L G (named_swap x y A) \<tau>"
  show "has_ntype L G A \<tau>" using named_swap_type[OF same_type typed] by (simp only: named_swap_involution)
next
  assume typed: "has_ntype L G A \<tau>"
  show "has_ntype L G (named_swap x y A) \<tau>" by (rule named_swap_type[OF same_type typed])
qed

lemma named_app_type_iff:
  "has_ntype L G (NApp F A) \<tau> \<longleftrightarrow>
    (\<exists>\<sigma>. has_ntype L G F (Arr \<sigma> \<tau>) \<and> has_ntype L G A \<sigma>)"
  by (auto elim: named_app_type_obtain intro: has_ntype.App)

lemma named_lam_type_iff:
  "has_ntype L G (NLam n A) \<tau> \<longleftrightarrow>
    (\<exists>\<rho>. \<tau> = Arr (G n) \<rho> \<and> has_ntype L G A \<rho>)"
  by (auto elim: named_lam_type_obtain intro: has_ntype.Lam)

lemma named_fresh_binder_type_iff:
  assumes same_type: "G x = G y"
  shows "has_ntype L G (NLam x A) \<tau> \<longleftrightarrow> has_ntype L G (NLam y (named_swap x y A)) \<tau>"
  by (simp only: named_lam_type_iff named_swap_type_iff[OF same_type] same_type)

lemma named_fresh_binder_fv:
  assumes fresh: "y \<notin> named_vars A"
  shows "named_fv (NLam x A) = named_fv (NLam y (named_swap x y A))"
proof -
  have not_free: "y \<notin> named_fv A" using fresh named_fv_subset_vars[where A=A] by blast
  show ?thesis using not_free
    by (auto simp: named_fv.simps named_swap_fv image_iff named_swap_index_def split: if_splits)
qed

end
