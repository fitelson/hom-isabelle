theory Bacon_C_Church_Selectors
  imports Bacon_C_Vector_Contexts
begin

section \<open>Typed selectors for tuples of propositions\<close>

text \<open>
  Put Rₙ := t → ⋯ → t → t, with n argument positions.
  The i-th selector πᵢⁿ := λp₁…pₙ.pᵢ has type Rₙ when 0 ≤ i < n.
  All tuple components are propositions; the original abstraction vector
  may therefore contain variables of different types.
  Source obligation: Bacon--Dorr Appendix A.2(i), p.65.

  Isabelle representation.  Indices are zero-based.  C_Church_constant
  implements a repeated constant abstraction, and the recursive selector
  either retains the first argument or ignores it and selects from the tail.
  Status.  This leaf establishes syntax, types, and closedness only.
  Church encoding is proof-engineering, not a new object-language axiom.
\<close>

lemma C_Church_lift_ren_comp:
  "lift_ren r \<circ> lift_ren s = lift_ren (r \<circ> s)"
  by (rule ext, rename_tac i, case_tac i; simp add: comp_def)

lemma C_Church_rename_comp:
  "rename r (rename s M) = rename (r \<circ> s) M"
  by (induction M arbitrary: r s) (simp_all add: C_Church_lift_ren_comp)

lemma C_Church_rename_lift_shift:
  "rename (lift_ren r) (shift M) = shift (rename r M)"
  by (simp add: shift_def C_Church_rename_comp comp_def)

lemma C_Church_lift_subst_rename:
  "lift_subst s \<circ> lift_ren r = lift_subst (s \<circ> r)"
  by (rule ext, rename_tac i, case_tac i; simp add: comp_def)

lemma C_Church_subst_rename:
  "subst s (rename r M) = subst (s \<circ> r) M"
  by (induction M arbitrary: s r) (simp_all add: C_Church_lift_subst_rename)

lemma C_Church_rename_lift_subst:
  "(\<lambda>n. rename (lift_ren r) (lift_subst s n)) =
    lift_subst (\<lambda>n. rename r (s n))"
  by (rule ext, rename_tac i, case_tac i;
    simp add: C_Church_rename_lift_shift shift_def[symmetric])

lemma C_Church_rename_subst:
  "rename r (subst s M) = subst (\<lambda>n. rename r (s n)) M"
  by (induction M arbitrary: r s) (simp_all add: C_Church_rename_lift_subst)

lemma C_Church_subst_lift_shift:
  "subst (lift_subst s) (shift M) = shift (subst s M)"
  by (simp add: shift_def C_Church_subst_rename C_Church_rename_subst comp_def)

definition C_Church_argument_type :: "nat \<Rightarrow> otype" where
  "C_Church_argument_type n = arrow_type (replicate n Prop) Prop"

lemma C_Church_argument_type_simps[simp]:
  "C_Church_argument_type 0 = Prop"
  "C_Church_argument_type (Suc n) = Prop \<rightarrow>\<^sub>o C_Church_argument_type n"
  by (simp_all add: C_Church_argument_type_def)

fun C_Church_constant :: "nat \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_Church_constant 0 A = A"
| "C_Church_constant (Suc n) A = Lam Prop (shift (C_Church_constant n A))"

lemma C_Church_constant_type:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> C_Church_constant n A : C_Church_argument_type n"
proof (induction n)
  case 0
  show ?case using A by simp
next
  case (Suc n)
  have body: "Prop # \<Gamma> \<turnstile> shift (C_Church_constant n A) : C_Church_argument_type n"
    by (rule weakening_front[OF Suc.IH])
  show ?case using has_type.Lam[OF body] by simp
qed

lemma C_Church_constant_rename:
  "rename r (C_Church_constant n A) = C_Church_constant n (rename r A)"
  by (induction n arbitrary: r A) (simp_all add: C_Church_rename_lift_shift)

lemma C_Church_constant_subst:
  "subst s (C_Church_constant n A) = C_Church_constant n (subst s A)"
  by (induction n arbitrary: s A) (simp_all add: C_Church_subst_lift_shift)

fun C_Church_selector :: "nat \<Rightarrow> nat \<Rightarrow> oterm" where
  "C_Church_selector 0 i = ObjTrue"
| "C_Church_selector (Suc n) 0 = Lam Prop (C_Church_constant n (Var 0))"
| "C_Church_selector (Suc n) (Suc i) = Lam Prop (shift (C_Church_selector n i))"

lemma C_Church_selector_type:
  assumes index: "i < n"
  shows "\<Gamma> \<turnstile> C_Church_selector n i : C_Church_argument_type n"
  using index
proof (induction n arbitrary: i \<Gamma>)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note selector_IH = Suc.IH
  note selector_bound = Suc.prems
  show ?case
  proof (cases i)
    case 0
    have variable: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
    have body: "Prop # \<Gamma> \<turnstile> C_Church_constant n (Var 0) : C_Church_argument_type n"
      by (rule C_Church_constant_type[OF variable])
    show ?thesis using has_type.Lam[OF body] by (simp add: 0)
  next
    case (Suc j)
    have index_j: "j < n" using selector_bound Suc by simp
    have selected: "\<Gamma> \<turnstile> C_Church_selector n j : C_Church_argument_type n"
      by (rule selector_IH[OF index_j])
    have body: "Prop # \<Gamma> \<turnstile> shift (C_Church_selector n j) : C_Church_argument_type n"
      by (rule weakening_front[OF selected])
    show ?thesis using has_type.Lam[OF body] by (simp add: Suc)
  qed
qed

lemma C_Church_selector_closed:
  "rename r (C_Church_selector n i) = C_Church_selector n i"
proof (induction n arbitrary: i r)
  case 0
  show ?case by (simp add: ObjTrue_def)
next
  case (Suc n)
  show ?case by (cases i) (simp_all add: C_Church_constant_rename
    C_Church_rename_lift_shift Suc.IH)
qed

lemma C_Church_selector_raise:
  "C_vector_raise k (C_Church_selector n i) = C_Church_selector n i"
  by (induction k) (simp_all add: C_Church_selector_closed)

lemma C_Church_selector_subst:
  "subst s (C_Church_selector n i) = C_Church_selector n i"
proof (induction n arbitrary: i s)
  case 0
  show ?case by (simp add: ObjTrue_def)
next
  case (Suc n)
  show ?case by (cases i) (simp_all add: C_Church_constant_subst
    C_Church_subst_lift_shift Suc.IH)
qed

lemma C_Church_prop_arguments:
  assumes args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "list_all2 (\<lambda>A \<tau>. \<Gamma> \<turnstile> A : \<tau>) xs (replicate (length xs) Prop)"
  using args by (induction xs) auto

lemma C_Church_apply_type:
  assumes F: "\<Gamma> \<turnstile> F : C_Church_argument_type (length xs)"
    and args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> app_vec F xs : Prop"
  by (rule typed_app_vec[OF F[unfolded C_Church_argument_type_def] C_Church_prop_arguments[OF args]])

end
