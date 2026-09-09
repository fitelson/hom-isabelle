theory Bacon_C_Church_Tuples
  imports Bacon_C_Church_Selectors
begin

section \<open>Church tuples and their typed β projections\<close>

text \<open>
  For xs = [A₁,…,Aₙ], put ⟨xs⟩ := λf.f A₁ … Aₙ, of type
  Tₙ := (t → ⋯ → t → t) → t.  For i < n, ⟨xs⟩ πᵢⁿ ≡β Aᵢ.
  Source obligation: the arbitrary-vector PC case of Bacon--Dorr A.2(i),
  p.65.  This is an explicit encoding of propositional atoms, not of
  heterogeneous values of the original variables.

  Isabelle representation.  Tuple components are shifted beneath f.
  Projection uses typed compatible β steps and beta_eta_equiv; it does
  not use C Equivalence.  The n = 0 case supplies no valid projection.
  Status.  These lemmas supply the encoding bridge, not yet full vector PC.
\<close>

lemma C_Church_compatible_app_vec:
  assumes step: "compatible_step R F G"
  shows "compatible_step R (app_vec F xs) (app_vec G xs)"
  using step
proof (induction xs arbitrary: F G)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons x xs)
  show ?case using Cons.IH[OF compatible_step.App_left[OF Cons.prems]] by simp
qed

lemma C_Church_subst_app_vec:
  "subst s (app_vec F xs) = app_vec (subst s F) (map (subst s) xs)"
  by (induction xs arbitrary: F) simp_all

lemma C_Church_constant_apply:
  assumes X: "\<Gamma> \<turnstile> X : Prop"
    and args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (app_vec (C_Church_constant (length xs) X) xs) X"
  using args
proof (induction xs)
  case Nil
  show ?case using beta_eta_equiv.Refl[OF X] by simp
next
  case (Cons a xs)
  have a: "\<Gamma> \<turnstile> a : Prop" by (rule Cons.prems) simp
  have tail: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop" by (rule Cons.prems) simp
  have source: "\<Gamma> \<turnstile> app_vec (C_Church_constant (length (a # xs)) X) (a # xs) : Prop"
    by (rule C_Church_apply_type[OF C_Church_constant_type[OF X] Cons.prems])
  have middle: "\<Gamma> \<turnstile> app_vec (C_Church_constant (length xs) X) xs : Prop"
    by (rule C_Church_apply_type[OF C_Church_constant_type[OF X] tail])
  have root_step: "compatible_step beta_contract
    (App (C_Church_constant (Suc (length xs)) X) a) (C_Church_constant (length xs) X)"
  proof -
    have "compatible_step beta_contract
      (App (Lam Prop (shift (C_Church_constant (length xs) X))) a)
      (subst0 a (shift (C_Church_constant (length xs) X)))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: subst0_shift)
  qed
  have step: "compatible_step beta_contract
    (app_vec (C_Church_constant (length (a # xs)) X) (a # xs))
    (app_vec (C_Church_constant (length xs) X) xs)"
    using C_Church_compatible_app_vec[OF root_step, where xs=xs] by simp
  show ?case by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle step]
    Cons.IH[OF tail]])
qed

lemma C_Church_selector_apply:
  assumes args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and index: "i < length xs"
  shows "beta_eta_equiv \<Gamma> Prop (app_vec (C_Church_selector (length xs) i) xs) (xs ! i)"
  using args index
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have a: "\<Gamma> \<turnstile> a : Prop" by (rule Cons.prems(1)) simp
  have tail: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop" by (rule Cons.prems(1)) simp
  have source: "\<Gamma> \<turnstile> app_vec (C_Church_selector (length (a # xs)) i) (a # xs) : Prop"
    by (rule C_Church_apply_type[OF C_Church_selector_type[OF Cons.prems(2)] Cons.prems(1)])
  show ?case
  proof (cases i)
    case 0
    have middle: "\<Gamma> \<turnstile> app_vec (C_Church_constant (length xs) a) xs : Prop"
      by (rule C_Church_apply_type[OF C_Church_constant_type[OF a] tail])
    have root_step: "compatible_step beta_contract
      (App (C_Church_selector (Suc (length xs)) 0) a) (C_Church_constant (length xs) a)"
    proof -
      have "compatible_step beta_contract
        (App (Lam Prop (C_Church_constant (length xs) (Var 0))) a)
        (subst0 a (C_Church_constant (length xs) (Var 0)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis by (simp add: subst0_def C_Church_constant_subst)
    qed
    have step: "compatible_step beta_contract
      (app_vec (C_Church_selector (length (a # xs)) i) (a # xs))
      (app_vec (C_Church_constant (length xs) a) xs)"
      using C_Church_compatible_app_vec[OF root_step, where xs=xs] by (simp add: 0)
    have reduction: "beta_eta_equiv \<Gamma> Prop
      (app_vec (C_Church_selector (length (a # xs)) i) (a # xs)) a"
      by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle step]
        C_Church_constant_apply[OF a tail]])
    show ?thesis using reduction by (simp add: 0)
  next
    case (Suc j)
    have index_j: "j < length xs" using Cons.prems(2) Suc by simp
    have middle: "\<Gamma> \<turnstile> app_vec (C_Church_selector (length xs) j) xs : Prop"
      by (rule C_Church_apply_type[OF C_Church_selector_type[OF index_j] tail])
    have root_step: "compatible_step beta_contract
      (App (C_Church_selector (Suc (length xs)) (Suc j)) a) (C_Church_selector (length xs) j)"
    proof -
      have "compatible_step beta_contract
        (App (Lam Prop (shift (C_Church_selector (length xs) j))) a)
        (subst0 a (shift (C_Church_selector (length xs) j)))"
        by (intro compatible_step.root beta_contract.beta)
      then show ?thesis by (simp add: subst0_shift)
    qed
    have step: "compatible_step beta_contract
      (app_vec (C_Church_selector (length (a # xs)) i) (a # xs))
      (app_vec (C_Church_selector (length xs) j) xs)"
      using C_Church_compatible_app_vec[OF root_step, where xs=xs] by (simp add: Suc)
    have reduction: "beta_eta_equiv \<Gamma> Prop
      (app_vec (C_Church_selector (length (a # xs)) i) (a # xs)) (xs ! j)"
      by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle step]
        Cons.IH[OF tail index_j]])
    show ?thesis using reduction by (simp add: Suc)
  qed
qed

definition C_Church_tuple_type :: "nat \<Rightarrow> otype" where
  "C_Church_tuple_type n = C_Church_argument_type n \<rightarrow>\<^sub>o Prop"

definition C_Church_tuple :: "oterm list \<Rightarrow> oterm" where
  "C_Church_tuple xs = Lam (C_Church_argument_type (length xs))
    (app_vec (Var 0) (map shift xs))"

lemma C_Church_tuple_type:
  assumes args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> C_Church_tuple xs : C_Church_tuple_type (length xs)"
proof -
  let ?R = "C_Church_argument_type (length xs)"
  have variable: "?R # \<Gamma> \<turnstile> Var 0 : C_Church_argument_type (length (map shift xs))"
    by (rule has_type.Var) simp
  have shifted: "\<And>A. A \<in> set (map shift xs) \<Longrightarrow> ?R # \<Gamma> \<turnstile> A : Prop"
  proof -
    fix A
    assume member: "A \<in> set (map shift xs)"
    obtain B where B: "B \<in> set xs" and AB: "A = shift B" using member by auto
    have B_type: "\<Gamma> \<turnstile> B : Prop" by (rule args[OF B])
    show "?R # \<Gamma> \<turnstile> A : Prop" using weakening_front[OF B_type] by (simp only: AB)
  qed
  have body: "?R # \<Gamma> \<turnstile> app_vec (Var 0) (map shift xs) : Prop"
    by (rule C_Church_apply_type[OF variable shifted])
  show ?thesis using has_type.Lam[OF body]
    by (simp only: C_Church_tuple_def C_Church_tuple_type_def)
qed

lemma C_Church_tuple_beta:
  "compatible_step beta_contract (App (C_Church_tuple xs) F) (app_vec F xs)"
proof -
  have "compatible_step beta_contract (App (C_Church_tuple xs) F)
    (subst0 F (app_vec (Var 0) (map shift xs)))"
    unfolding C_Church_tuple_def by (intro compatible_step.root beta_contract.beta)
  then show ?thesis
    by (simp add: subst0_def C_Church_subst_app_vec map_map comp_def shift_def C_subst_raised)
qed

theorem C_Church_tuple_projection:
  assumes args: "\<And>A. A \<in> set xs \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and index: "i < length xs"
  shows "beta_eta_equiv \<Gamma> Prop
    (App (C_Church_tuple xs) (C_Church_selector (length xs) i)) (xs ! i)"
proof -
  have tuple_type: "\<Gamma> \<turnstile> C_Church_tuple xs :
    C_Church_argument_type (length xs) \<rightarrow>\<^sub>o Prop"
    using C_Church_tuple_type[OF args] by (simp only: C_Church_tuple_type_def)
  have selector_type: "\<Gamma> \<turnstile> C_Church_selector (length xs) i : C_Church_argument_type (length xs)"
    by (rule C_Church_selector_type[OF index])
  have source: "\<Gamma> \<turnstile> App (C_Church_tuple xs) (C_Church_selector (length xs) i) : Prop"
    by (rule has_type.App[OF tuple_type selector_type])
  have middle: "\<Gamma> \<turnstile> app_vec (C_Church_selector (length xs) i) xs : Prop"
    by (rule C_Church_apply_type[OF selector_type args])
  show ?thesis by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle C_Church_tuple_beta]
    C_Church_selector_apply[OF args index]])
qed

end
