theory Bacon_Source_Named_Vectors
  imports Bacon_Source_Named_Conversion_Contexts Bacon_Source_Vector_Syntax
begin

section \<open>Finite named abstraction and application vectors\<close>

text \<open>
  Write λx₁…xₙ.A and F A₁…Aₙ with names in their displayed order.
  The abstraction has type G(x₁) → … → G(xₙ) → τ when A:τ.
  Applying it to x₁,…,xₙ β-reduces to A. Each root substitutes a
  variable for itself, so the free-for guard holds even with repeated names.
  Source: Bacon–Dorr §1.1 and Figure 2, pp.5–8.

  Representation: named_lam_vec folds NLam from the right; named_app_vec
  accumulates NApp from the left. There is no reversal of the name vector.
  Status: typed signature-relative syntax and conversion only. No H rule,
  semantic premise, or pointwise abstraction-extensionality is used.
\<close>

fun named_lam_vec :: "nat list \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "named_lam_vec [] A = A"
| "named_lam_vec (n # ns) A = NLam n (named_lam_vec ns A)"

fun named_app_vec :: "('c,'l) named_term \<Rightarrow> ('c,'l) named_term list \<Rightarrow> ('c,'l) named_term" where
  "named_app_vec F [] = F"
| "named_app_vec F (A # As) = named_app_vec (NApp F A) As"

lemma named_lam_vec_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_ntype L G (named_lam_vec ns A) (sarrow_type (map G ns) \<tau>)"
proof (induction ns)
  case Nil
  show ?case using typed by simp
next
  case (Cons n ns)
  have abstraction: "has_ntype L G (NLam n (named_lam_vec ns A))
    (Arr (G n) (sarrow_type (map G ns) \<tau>))"
    by (rule has_ntype.Lam[OF Cons.IH])
  show ?case using abstraction by simp
qed

lemma named_lam_vec_language:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_in_language L \<Sigma> G (named_lam_vec ns A) (sarrow_type (map G ns) \<tau>)"
proof (induction ns)
  case Nil
  show ?case using language by simp
next
  case (Cons n ns)
  show ?case using named_language_Lam[OF Cons.IH, where n=n] by simp
qed

lemma named_lam_vec_fv:
  "named_fv (named_lam_vec ns A) = named_fv A - set ns"
  by (induction ns) auto

lemma named_lam_vec_closed:
  "named_fv A \<subseteq> set ns \<Longrightarrow> named_fv (named_lam_vec ns A) = {}"
  by (simp only: named_lam_vec_fv) blast

lemma named_app_vec_language:
  assumes arguments: "list_all2 (\<lambda>A \<sigma>. named_in_language L \<Sigma> G A \<sigma>) As \<sigma>s"
    and head: "named_in_language L \<Sigma> G F (sarrow_type \<sigma>s \<tau>)"
  shows "named_in_language L \<Sigma> G (named_app_vec F As) \<tau>"
  using arguments head
proof (induction As arbitrary: \<sigma>s F)
  case Nil
  have types: "\<sigma>s = []" using Nil.prems(1) by simp
  show ?case using Nil.prems(2) by (simp add: types)
next
  case (Cons A As)
  obtain \<sigma> \<rho>s where types: "\<sigma>s = \<sigma> # \<rho>s"
    using Cons.prems(1) by (cases \<sigma>s) auto
  have argument: "named_in_language L \<Sigma> G A \<sigma>"
    and rest: "list_all2 (\<lambda>A \<sigma>. named_in_language L \<Sigma> G A \<sigma>) As \<rho>s"
    using Cons.prems(1) by (simp_all add: types)
  have f_type: "named_in_language L \<Sigma> G F (Arr \<sigma> (sarrow_type \<rho>s \<tau>))"
    using Cons.prems(2) by (simp add: types)
  have next_head: "named_in_language L \<Sigma> G (NApp F A) (sarrow_type \<rho>s \<tau>)"
    by (rule named_language_App[OF f_type argument])
  show ?case using Cons.IH[OF rest next_head] by simp
qed

lemma named_app_vec_conversion:
  assumes arguments: "list_all2 (\<lambda>A \<sigma>. named_in_language L \<Sigma> G A \<sigma>) As \<sigma>s"
    and head: "named_beta_eta_in_language L \<Sigma> G (sarrow_type \<sigma>s \<tau>) F H"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (named_app_vec F As) (named_app_vec H As)"
  using arguments head
proof (induction As arbitrary: \<sigma>s F H)
  case Nil
  have types: "\<sigma>s = []" using Nil.prems(1) by simp
  show ?case using Nil.prems(2) by (simp add: types)
next
  case (Cons A As)
  obtain \<sigma> \<rho>s where types: "\<sigma>s = \<sigma> # \<rho>s"
    using Cons.prems(1) by (cases \<sigma>s) auto
  have argument: "named_in_language L \<Sigma> G A \<sigma>"
    and rest: "list_all2 (\<lambda>A \<sigma>. named_in_language L \<Sigma> G A \<sigma>) As \<rho>s"
    using Cons.prems(1) by (simp_all add: types)
  have heads: "named_beta_eta_in_language L \<Sigma> G (Arr \<sigma> (sarrow_type \<rho>s \<tau>)) F H"
    using Cons.prems(2) by (simp add: types)
  have next_heads: "named_beta_eta_in_language L \<Sigma> G (sarrow_type \<rho>s \<tau>) (NApp F A) (NApp H A)"
    by (rule named_conversion_App_left[OF heads argument])
  show ?case using Cons.IH[OF rest next_heads] by simp
qed

lemma named_vector_variable_language:
  "named_in_language L \<Sigma> G (NVar n) (G n)"
  unfolding named_in_language_def by (rule conjI) (rule has_ntype.Var, simp)

lemma named_vector_variables_language:
  "list_all2 (\<lambda>A \<sigma>. named_in_language L \<Sigma> G A \<sigma>) (map NVar ns) (map G ns)"
  by (induction ns) (simp_all add: named_vector_variable_language)

lemma named_self_beta:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp (NLam n A) (NVar n)) A"
proof -
  have redex: "named_in_language L \<Sigma> G (NApp (NLam n A) (NVar n)) \<tau>"
    by (rule named_language_App[OF named_language_Lam[OF language]
      named_vector_variable_language])
  have root: "named_beta_contract (NApp (NLam n A) (NVar n)) (named_subst n (NVar n) A)"
    by (rule named_beta_contract.beta[OF named_free_for_same_variable])
  have step: "named_compatible_step named_beta_contract (NApp (NLam n A) (NVar n)) A"
    using named_compatible_step.root[where R=named_beta_contract, OF root]
    by (simp only: named_subst_same_variable)
  show ?thesis by (rule named_beta_eta_in_language.Beta[OF redex language step])
qed

theorem named_lam_vec_self_application:
  assumes language: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau>
    (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
proof (induction ns)
  case Nil
  show ?case using named_beta_eta_in_language.Refl[OF language] by simp
next
  case (Cons n ns)
  have tail_language: "named_in_language L \<Sigma> G (named_lam_vec ns A)
    (sarrow_type (map G ns) \<tau>)"
    by (rule named_lam_vec_language[OF language])
  have first: "named_beta_eta_in_language L \<Sigma> G (sarrow_type (map G ns) \<tau>)
    (NApp (NLam n (named_lam_vec ns A)) (NVar n)) (named_lam_vec ns A)"
    by (rule named_self_beta[OF tail_language])
  have applied: "named_beta_eta_in_language L \<Sigma> G \<tau>
    (named_app_vec (NApp (NLam n (named_lam_vec ns A)) (NVar n)) (map NVar ns))
    (named_app_vec (named_lam_vec ns A) (map NVar ns))"
    by (rule named_app_vec_conversion[OF named_vector_variables_language first])
  show ?case using named_beta_eta_in_language.Trans[OF applied Cons.IH] by simp
qed

end
