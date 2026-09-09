theory Bacon_C_Vector_Beta_Evaluation
  imports Bacon_C_Church_Tuples
begin

section \<open>Evaluating an abstraction vector at its own variables\<close>

text \<open>
  In context Δ,Γ, apply the raised operation λv̄.A to v̄ in
  outer-to-inner order.  The result β-reduces to A.  Source role:
  syntactic evaluation needed for the rule cases of Bacon–Dorr
  Appendix A.2, pp.65–66, using contextual β from Figure 2, p.8.

  Isabelle representation.  Δ lists de Bruijn slots from innermost to
  outermost.  Thus C_abstract_prefix Δ reverses Δ, and its arguments
  must be rev(fresh_vars(length Δ)) = [vₙ₋₁,…,v₀].  The ascending
  fresh_vars list alone is not the required argument order.  Type and
  substitution lemmas below allow mixed types and the empty prefix.

  Status.  The conclusion is typed beta_eta_equiv, proved using β only.
  No C identity is inferred here, no open equation is abstracted, and no
  C/CEV Equivalence rule or semantic theorem is used.
\<close>

lemma C_vector_raise_as_rename:
  "C_vector_raise n M = rename (\<lambda>i. n + i) M"
  by (induction n) (simp_all add: C_Church_rename_comp comp_def)

lemma C_vector_subst_renamed:
  assumes maps: "\<And>i. s (r i) = Var (q i)"
  shows "subst s (rename r M) = rename q M"
proof -
  have twice: "subst s (rename r (rename id M)) = rename q M"
    by (rule C_subst_two_renamings[where s=s and r=r and t=id and q=q])
      (simp only: id_apply maps)
  show ?thesis using twice by (simp only: rename_id)
qed

lemma C_vector_outer_substitution:
  "subst0 (Var n) (rename (lift_ren (\<lambda>i. Suc n + i)) M) = C_vector_raise n M"
proof -
  have maps: "case_nat (Var n) Var (lift_ren (\<lambda>j. Suc n + j) i) = Var (n + i)" for i
    by (cases i) simp_all
  show ?thesis unfolding subst0_def C_vector_raise_as_rename
    by (rule C_vector_subst_renamed[where s="case_nat (Var n) Var"
      and r="lift_ren (\<lambda>i. Suc n + i)" and q="\<lambda>i. n + i", OF maps])
qed

lemma C_vector_outer_beta:
  "compatible_step beta_contract
    (App (C_vector_raise (Suc n) (Lam \<sigma> M)) (Var n)) (C_vector_raise n M)"
proof -
  have root_step: "compatible_step beta_contract
    (App (Lam \<sigma> (rename (lift_ren (\<lambda>i. Suc n + i)) M)) (Var n))
    (subst0 (Var n) (rename (lift_ren (\<lambda>i. Suc n + i)) M))"
    by (rule compatible_step.root[where R=beta_contract]) (rule beta_contract.beta)
  have raised: "C_vector_raise (Suc n) (Lam \<sigma> M) =
    Lam \<sigma> (rename (lift_ren (\<lambda>i. Suc n + i)) M)"
    by (simp only: C_vector_raise_as_rename rename.simps)
  show ?thesis using root_step by (simp only: raised C_vector_outer_substitution)
qed

subsection \<open>The argument order matches the reversed arrow vector\<close>

lemma C_vector_reverse_fresh_vars_Suc:
  "rev (fresh_vars (Suc n)) = Var n # rev (fresh_vars n)"
  by (simp add: fresh_vars_def upt_Suc)

lemma C_vector_reverse_fresh_vars_type:
  "list_all2 (\<lambda>V \<sigma>. \<Delta> @ \<Gamma> \<turnstile> V : \<sigma>)
    (rev (fresh_vars (length \<Delta>))) (rev \<Delta>)"
  using typed_fresh_vars[where \<sigma>s=\<Delta> and \<Gamma>=\<Gamma>] by (simp only: list_all2_rev)

lemma C_vector_deabstract_type:
  assumes body: "\<Delta> @ \<Gamma> \<turnstile> A : \<tau>"
  shows "\<Delta> @ \<Gamma> \<turnstile>
    app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> A))
      (rev (fresh_vars (length \<Delta>))) : \<tau>"
proof -
  have abstract_type: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> A : arrow_type (rev \<Delta>) \<tau>"
    by (rule C_abstract_prefix_type[OF body])
  have raised: "\<Delta> @ \<Gamma> \<turnstile> C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> A) :
    arrow_type (rev \<Delta>) \<tau>"
    by (rule C_vector_raise_type[OF abstract_type])
  show ?thesis by (rule typed_app_vec[OF raised C_vector_reverse_fresh_vars_type])
qed

lemma C_vector_abstract_snoc:
  "C_abstract_prefix (\<Delta> @ [\<sigma>]) A = Lam \<sigma> (C_abstract_prefix \<Delta> A)"
  by (simp add: C_abstract_prefix_def)

subsection \<open>Typed deabstraction by reverse induction on the prefix\<close>

theorem C_vector_deabstract_beta_eta:
  assumes body: "\<Delta> @ \<Gamma> \<turnstile> A : \<tau>"
  shows "beta_eta_equiv (\<Delta> @ \<Gamma>) \<tau>
    (app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> A))
      (rev (fresh_vars (length \<Delta>)))) A"
  using body
proof (induction \<Delta> arbitrary: \<Gamma> rule: rev_induct)
  case Nil
  have A: "\<Gamma> \<turnstile> A : \<tau>" using Nil.prems by simp
  show ?case using beta_eta_equiv.Refl[OF A]
    by (simp add: fresh_vars_def C_abstract_prefix_def)
next
  case (snoc \<sigma> \<Delta>)
  let ?n = "length \<Delta>"
  let ?M = "C_abstract_prefix \<Delta> A"
  let ?vars = "rev (fresh_vars ?n)"
  have tail_body: "\<Delta> @ (\<sigma> # \<Gamma>) \<turnstile> A : \<tau>"
    using snoc.prems by (simp only: append_assoc append_Cons append_Nil)
  have source: "(\<Delta> @ [\<sigma>]) @ \<Gamma> \<turnstile>
    app_vec (C_vector_raise (length (\<Delta> @ [\<sigma>])) (C_abstract_prefix (\<Delta> @ [\<sigma>]) A))
      (rev (fresh_vars (length (\<Delta> @ [\<sigma>])))) : \<tau>"
    by (rule C_vector_deabstract_type[OF snoc.prems])
  have middle_tail: "\<Delta> @ (\<sigma> # \<Gamma>) \<turnstile>
    app_vec (C_vector_raise ?n ?M) ?vars : \<tau>"
    by (rule C_vector_deabstract_type[OF tail_body])
  have middle: "(\<Delta> @ [\<sigma>]) @ \<Gamma> \<turnstile> app_vec (C_vector_raise ?n ?M) ?vars : \<tau>"
    using middle_tail by (simp only: append_assoc append_Cons append_Nil)
  have root_step: "compatible_step beta_contract
    (App (C_vector_raise (Suc ?n) (Lam \<sigma> ?M)) (Var ?n)) (C_vector_raise ?n ?M)"
    by (rule C_vector_outer_beta)
  have contextual_step: "compatible_step beta_contract
    (app_vec (App (C_vector_raise (Suc ?n) (Lam \<sigma> ?M)) (Var ?n)) ?vars)
    (app_vec (C_vector_raise ?n ?M) ?vars)"
    by (rule C_Church_compatible_app_vec[OF root_step])
  have step: "compatible_step beta_contract
    (app_vec (C_vector_raise (length (\<Delta> @ [\<sigma>])) (C_abstract_prefix (\<Delta> @ [\<sigma>]) A))
      (rev (fresh_vars (length (\<Delta> @ [\<sigma>])))))
    (app_vec (C_vector_raise ?n ?M) ?vars)"
    using contextual_step by (simp add: C_vector_abstract_snoc C_vector_reverse_fresh_vars_Suc)
  have tail_conversion: "beta_eta_equiv (\<Delta> @ (\<sigma> # \<Gamma>)) \<tau>
    (app_vec (C_vector_raise ?n ?M) ?vars) A"
    by (rule snoc.IH[where \<Gamma>="\<sigma> # \<Gamma>", OF tail_body])
  have tail_conversion': "beta_eta_equiv ((\<Delta> @ [\<sigma>]) @ \<Gamma>) \<tau>
    (app_vec (C_vector_raise ?n ?M) ?vars) A"
    using tail_conversion by (simp only: append_assoc append_Cons append_Nil)
  show ?case by (rule beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF source middle step] tail_conversion'])
qed

end
