theory Bacon_C_Vector_Contexts
  imports Bacon_C_PC_Single_Abstraction
begin

section \<open>Operation replacement and conversion under arbitrary vectors\<close>

text \<open>
  From ⊢C F = G we may derive ⊢C (λv̄.F A) = (λv̄.G A).
  Here F and G are terms in the ambient context, whereas A may depend on
  every variable in v̄.  Syntactic βη conversion may then normalize both
  sides beneath the entire vector.
  Source use: Bacon--Dorr Appendix A.2, pp.65–66, with Ref, LL, β, and η.

  Isabelle representation.  C_abstract_prefix Δ reverses the de Bruijn
  context prefix before constructing the abstraction vector.  The three
  recursive operations below lift renamings/substitutions through that
  prefix and shift an ambient term beneath it.
  Status.  Only identities of the supplied operations are replaced.
  An arbitrary open C identity is not abstracted.
\<close>

fun C_vector_lift_ren :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "C_vector_lift_ren 0 r = r"
| "C_vector_lift_ren (Suc n) r = lift_ren (C_vector_lift_ren n r)"

fun C_vector_lift_subst :: "nat \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> nat \<Rightarrow> oterm" where
  "C_vector_lift_subst 0 s = s"
| "C_vector_lift_subst (Suc n) s = lift_subst (C_vector_lift_subst n s)"

fun C_vector_raise :: "nat \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_vector_raise 0 F = F"
| "C_vector_raise (Suc n) F = rename Suc (C_vector_raise n F)"

lemma C_vector_lift_subst_slot:
  "C_vector_lift_subst n (case_nat F Var) n = C_vector_raise n F"
  by (induction n) simp_all

lemma C_vector_lift_inverse:
  assumes inverse: "\<And>i. s (r i) = Var i"
  shows "C_vector_lift_subst n s (C_vector_lift_ren n r i) = Var i"
proof (induction n arbitrary: i)
  case 0
  show ?case by (simp add: inverse)
next
  case (Suc n)
  show ?case by (cases i) (simp_all add: Suc.IH)
qed

lemma C_vector_remove_inserted_parameter:
  "subst (C_vector_lift_subst n (case_nat F Var))
    (rename (C_vector_lift_ren n Suc) A) = A"
proof (rule subst_rename_inverse)
  fix i
  show "C_vector_lift_subst n (case_nat F Var) (C_vector_lift_ren n Suc i) = Var i"
    by (rule C_vector_lift_inverse) simp
qed

lemma C_vector_lookup_insert:
  assumes index: "lookup (\<Delta> @ \<Gamma>) i = Some \<rho>"
  shows "lookup (\<Delta> @ (\<nu> # \<Gamma>)) (C_vector_lift_ren (length \<Delta>) Suc i) = Some \<rho>"
  using index
proof (induction \<Delta> arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons \<tau> \<Delta>)
  show ?case using Cons.prems Cons.IH by (cases i) auto
qed

lemma C_vector_insert_parameter_type:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : \<rho>"
  shows "\<Delta> @ (\<nu> # \<Gamma>) \<turnstile> rename (C_vector_lift_ren (length \<Delta>) Suc) A : \<rho>"
proof (rule renaming_preserves_typing[OF A])
  fix i \<tau>
  assume index: "lookup (\<Delta> @ \<Gamma>) i = Some \<tau>"
  show "lookup (\<Delta> @ (\<nu> # \<Gamma>)) (C_vector_lift_ren (length \<Delta>) Suc i) = Some \<tau>"
    by (rule C_vector_lookup_insert[OF index])
qed

lemma C_vector_raise_type:
  assumes F: "\<Gamma> \<turnstile> F : \<rho>"
  shows "\<Delta> @ \<Gamma> \<turnstile> C_vector_raise (length \<Delta>) F : \<rho>"
proof (induction \<Delta>)
  case Nil
  show ?case using F by simp
next
  case (Cons \<tau> \<Delta>)
  have shifted: "\<tau> # (\<Delta> @ \<Gamma>) \<turnstile> shift (C_vector_raise (length \<Delta>) F) : \<rho>"
    by (rule weakening_front[OF Cons.IH])
  show ?case using shifted by (simp add: shift_def)
qed

lemma C_abstract_prefix_subst:
  "subst s (C_abstract_prefix \<Delta> A) =
    C_abstract_prefix \<Delta> (subst (C_vector_lift_subst (length \<Delta>) s) A)"
  by (induction \<Delta> arbitrary: A) (simp_all add: C_abstract_prefix_cons)

lemma C_abstract_prefix_rename:
  "rename r (C_abstract_prefix \<Delta> A) =
    C_abstract_prefix \<Delta> (rename (C_vector_lift_ren (length \<Delta>) r) A)"
  by (induction \<Delta> arbitrary: A) (simp_all add: C_abstract_prefix_cons)

subsection \<open>Syntactic conversion beneath the whole vector\<close>

lemma C_beta_eta_abstract_prefix:
  assumes conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho> A B"
  shows "beta_eta_equiv \<Gamma> (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
  using conversion
proof (induction \<Delta> arbitrary: A B \<rho>)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons \<sigma> \<Delta>)
  have body: "beta_eta_equiv (\<sigma> # (\<Delta> @ \<Gamma>)) \<rho> A B"
    using Cons.prems by simp
  have inner: "beta_eta_equiv (\<Delta> @ \<Gamma>) (\<sigma> \<rightarrow>\<^sub>o \<rho>) (Lam \<sigma> A) (Lam \<sigma> B)"
    by (rule C_beta_eta_Lam[OF body])
  have outer: "beta_eta_equiv \<Gamma> (arrow_type (rev \<Delta>) (\<sigma> \<rightarrow>\<^sub>o \<rho>))
    (C_abstract_prefix \<Delta> (Lam \<sigma> A)) (C_abstract_prefix \<Delta> (Lam \<sigma> B))"
    by (rule Cons.IH[OF inner])
  show ?case using outer by (simp add: C_abstract_prefix_cons C_arrow_type_append)
qed

lemma C_vector_conversion_identity:
  assumes conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho> A B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
  by (rule C_closure_beta_eta_identity[OF C_beta_eta_abstract_prefix[OF conversion]])

subsection \<open>Normalized operation-slot replacement\<close>

lemma C_vector_identity_context:
  assumes F: "\<Gamma> \<turnstile> F : \<nu>" and G: "\<Gamma> \<turnstile> G : \<nu>"
    and body: "\<Delta> @ (\<nu> # \<Gamma>) \<turnstile> M : \<rho>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq \<nu> F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> (subst (C_vector_lift_subst (length \<Delta>) (case_nat F Var)) M))
    (C_abstract_prefix \<Delta> (subst (C_vector_lift_subst (length \<Delta>) (case_nat G Var)) M))"
  using C_identity_under_abstraction[OF F G body identity]
  by (simp only: subst0_def C_abstract_prefix_subst)

theorem C_vector_function_congruence:
  assumes F: "\<Gamma> \<turnstile> F : \<nu> \<rightarrow>\<^sub>o \<rho>"
    and G: "\<Gamma> \<turnstile> G : \<nu> \<rightarrow>\<^sub>o \<rho>"
    and A: "\<Delta> @ \<Gamma> \<turnstile> A : \<nu>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<nu> \<rightarrow>\<^sub>o \<rho>) F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> (App (C_vector_raise (length \<Delta>) F) A))
    (C_abstract_prefix \<Delta> (App (C_vector_raise (length \<Delta>) G) A))"
proof -
  let ?n = "length \<Delta>"
  let ?A = "rename (C_vector_lift_ren ?n Suc) A"
  let ?M = "App (Var ?n) ?A"
  have argument: "\<Delta> @ ((\<nu> \<rightarrow>\<^sub>o \<rho>) # \<Gamma>) \<turnstile> ?A : \<nu>"
    by (rule C_vector_insert_parameter_type[OF A])
  have index: "lookup ((\<nu> \<rightarrow>\<^sub>o \<rho>) # \<Gamma>) 0 = Some (\<nu> \<rightarrow>\<^sub>o \<rho>)" by simp
  have inserted: "lookup (\<Delta> @ ((\<nu> \<rightarrow>\<^sub>o \<rho>) # \<Gamma>)) ?n = Some (\<nu> \<rightarrow>\<^sub>o \<rho>)"
    using lookup_append_shift[OF index, where \<Delta>=\<Delta>] by simp
  have operator: "\<Delta> @ ((\<nu> \<rightarrow>\<^sub>o \<rho>) # \<Gamma>) \<turnstile> Var ?n : \<nu> \<rightarrow>\<^sub>o \<rho>"
    by (rule has_type.Var[OF inserted])
  have body: "\<Delta> @ ((\<nu> \<rightarrow>\<^sub>o \<rho>) # \<Gamma>) \<turnstile> ?M : \<rho>"
    by (rule has_type.App[OF operator argument])
  show ?thesis using C_vector_identity_context[OF F G body identity]
    by (simp add: C_vector_lift_subst_slot C_vector_remove_inserted_parameter)
qed

theorem C_vector_function_congruence_beta:
  assumes F: "\<Gamma> \<turnstile> F : \<nu> \<rightarrow>\<^sub>o \<rho>"
    and G: "\<Gamma> \<turnstile> G : \<nu> \<rightarrow>\<^sub>o \<rho>"
    and A: "\<Delta> @ \<Gamma> \<turnstile> A : \<nu>"
    and identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<nu> \<rightarrow>\<^sub>o \<rho>) F G"
    and left_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho>
      (App (C_vector_raise (length \<Delta>) F) A) B"
    and right_conversion: "beta_eta_equiv (\<Delta> @ \<Gamma>) \<rho>
      (App (C_vector_raise (length \<Delta>) G) A) D"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) \<rho>)
    (C_abstract_prefix \<Delta> B) (C_abstract_prefix \<Delta> D)"
  by (rule C_A1_transport[OF C_vector_function_congruence[OF F G A identity]
    C_vector_conversion_identity[OF left_conversion] C_vector_conversion_identity[OF right_conversion]])

text \<open>
  For the full PC vector case, one can Church-encode the finitely many
  propositional atoms as a single tuple variable: all selectors return t,
  even when v̄ contains mixed types.  The established single-abstraction
  PC theorem yields identity of two operations on that tuple.  The last
  theorem places that operation identity inside λv̄ and normalizes the
  tuple applications.  Typed tuple/selector construction and its projection
  β equations remain to be supplied; no full vector PC theorem is claimed.
\<close>

end
