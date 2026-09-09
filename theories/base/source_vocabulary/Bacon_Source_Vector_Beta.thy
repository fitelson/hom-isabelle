theory Bacon_Source_Vector_Beta
  imports Bacon_Source_Vector_Syntax
begin

section \<open>Guarded β evaluation of source abstraction vectors\<close>

text \<open>
  Raising λv̄.A beneath its own finite frame and applying it to
  [vₙ₋₁,…,v₀] β-reduces to A.  Source role: the closed-abstraction
  argument associated with Definition 3.1(ii.a–d), using the contextual
  β rule of Bacon–Dorr Figure 2, pp.7–8.

  Isabelle representation.  Reverse induction on Δ first removes its
  outermost binder.  Its argument is slot |Δ|; substitution changes the
  raise from |Δ|+1 to |Δ|.  The induction then continues in the remaining
  frame.  Every conversion node retains its type and nonlogical signature.
  Status: source syntax only, using β rather than any Equivalence rule or
  semantic principle.  Empty and mixed-type F vectors are included.
\<close>

lemma ssubst_variables_as_rename:
  assumes maps: "\<And>i. s i = SVar (q i)"
  shows "ssubst s A = srename q A"
  using maps
proof (induction A arbitrary: s q)
  case (SVar n)
  show ?case by (simp only: ssubst.simps srename.simps SVar.prems)
next
  case SConst
  show ?case by (simp only: ssubst.simps srename.simps)
next
  case SLogical
  show ?case by (simp only: ssubst.simps srename.simps)
next
  case (SApp M N)
  show ?case by (simp only: ssubst.simps srename.simps
    SApp.IH(1)[where s=s and q=q, OF SApp.prems] SApp.IH(2)[where s=s and q=q, OF SApp.prems])
next
  case (SLam \<sigma> A)
  have lifts: "slift_subst s i = SVar (lift_ren q i)" for i
    by (cases i) (simp_all add: SLam.prems)
  show ?case by (simp only: ssubst.simps srename.simps
    SLam.IH[where s="slift_subst s" and q="lift_ren q", OF lifts])
qed

lemma svector_subst_renamed:
  assumes maps: "\<And>i. s (r i) = SVar (q i)"
  shows "ssubst s (srename r A) = srename q A"
  unfolding ssubst_srename
  by (rule ssubst_variables_as_rename[where s="s \<circ> r" and q=q]) (simp only: comp_def maps)

lemma svector_outer_substitution:
  "ssubst0 (SVar n) (srename (lift_ren (\<lambda>i. Suc n + i)) A) = sraise n A"
proof -
  have maps: "case_nat (SVar n) SVar (lift_ren (\<lambda>j. Suc n + j) i) = SVar (n + i)" for i
    by (cases i) simp_all
  show ?thesis unfolding ssubst0_def sraise_as_rename
    by (rule svector_subst_renamed[where s="case_nat (SVar n) SVar"
      and r="lift_ren (\<lambda>i. Suc n + i)" and q="\<lambda>i. n + i", OF maps])
qed

lemma svector_outer_beta:
  "scompatible_step sbeta_contract
    (SApp (sraise (Suc n) (SLam \<sigma> A)) (SVar n)) (sraise n A)"
proof -
  have root_step: "scompatible_step sbeta_contract
    (SApp (SLam \<sigma> (srename (lift_ren (\<lambda>i. Suc n + i)) A)) (SVar n))
    (ssubst0 (SVar n) (srename (lift_ren (\<lambda>i. Suc n + i)) A))"
    by (rule scompatible_step.root[where R=sbeta_contract]) (rule sbeta_contract.beta)
  have raised: "sraise (Suc n) (SLam \<sigma> A) = SLam \<sigma> (srename (lift_ren (\<lambda>i. Suc n + i)) A)"
    by (simp only: sraise_as_rename srename.simps)
  show ?thesis using root_step by (simp only: raised svector_outer_substitution)
qed

lemma scompatible_app_vec:
  assumes step: "scompatible_step R F G"
  shows "scompatible_step R (sapp_vec F As) (sapp_vec G As)"
  using step
proof (induction As arbitrary: F G)
  case Nil
  show ?case using Nil.prems by simp
next
  case (Cons A As)
  have first: "scompatible_step R (SApp F A) (SApp G A)"
    by (rule scompatible_step.App_left[where R=R and M=F and M'=G and N=A, OF Cons.prems])
  show ?case using Cons.IH[where F="SApp F A" and G="SApp G A", OF first] by simp
qed

theorem sdeabstract_beta:
  assumes language: "sterm_in_language L \<Sigma> (\<Delta> @ \<Gamma>) A \<tau>"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> (\<Delta> @ \<Gamma>) \<tau>
    (sapp_vec (sraise (length \<Delta>) (sabstract_prefix \<Delta> A)) (rev (sfresh_vars (length \<Delta>)))) A"
  using language
proof (induction \<Delta> arbitrary: \<Gamma> rule: rev_induct)
  case Nil
  have typed: "has_stype L \<Gamma> A \<tau>" and sig: "sterm_in_signature \<Sigma> A"
    using Nil.prems unfolding sterm_in_language_def by simp_all
  show ?case using sbeta_eta_equiv_in_signature.Refl[OF typed sig]
    by (simp add: sfresh_vars_def)
next
  case (snoc \<sigma> \<Delta>)
  let ?n = "length \<Delta>"
  let ?K = "sabstract_prefix \<Delta> A"
  let ?vars = "rev (sfresh_vars ?n)"
  have body: "has_stype L ((\<Delta> @ [\<sigma>]) @ \<Gamma>) A \<tau>" and sig: "sterm_in_signature \<Sigma> A"
    using snoc.prems unfolding sterm_in_language_def by blast+
  have tail_language: "sterm_in_language L \<Sigma> (\<Delta> @ (\<sigma> # \<Gamma>)) A \<tau>"
    using snoc.prems by (simp only: append_assoc append_Cons append_Nil)
  have tail_body: "has_stype L (\<Delta> @ (\<sigma> # \<Gamma>)) A \<tau>"
    using tail_language unfolding sterm_in_language_def by (rule conjunct1)
  have source_type: "has_stype L ((\<Delta> @ [\<sigma>]) @ \<Gamma>)
    (sapp_vec (sraise (length (\<Delta> @ [\<sigma>])) (sabstract_prefix (\<Delta> @ [\<sigma>]) A))
      (rev (sfresh_vars (length (\<Delta> @ [\<sigma>]))))) \<tau>"
    by (rule sdeabstract_type[OF body])
  have source_sig: "sterm_in_signature \<Sigma>
    (sapp_vec (sraise (length (\<Delta> @ [\<sigma>])) (sabstract_prefix (\<Delta> @ [\<sigma>]) A))
      (rev (sfresh_vars (length (\<Delta> @ [\<sigma>])))))"
    by (rule sdeabstract_signature[OF sig])
  have middle_type: "has_stype L ((\<Delta> @ [\<sigma>]) @ \<Gamma>) (sapp_vec (sraise ?n ?K) ?vars) \<tau>"
    using sdeabstract_type[OF tail_body] by (simp only: append_assoc append_Cons append_Nil)
  have middle_sig: "sterm_in_signature \<Sigma> (sapp_vec (sraise ?n ?K) ?vars)"
    by (rule sdeabstract_signature[OF sig])
  have root_step: "scompatible_step sbeta_contract
    (SApp (sraise (Suc ?n) (SLam \<sigma> ?K)) (SVar ?n)) (sraise ?n ?K)" by (rule svector_outer_beta)
  have contextual_step: "scompatible_step sbeta_contract
    (sapp_vec (SApp (sraise (Suc ?n) (SLam \<sigma> ?K)) (SVar ?n)) ?vars) (sapp_vec (sraise ?n ?K) ?vars)"
    by (rule scompatible_app_vec[OF root_step])
  have step: "scompatible_step sbeta_contract
    (sapp_vec (sraise (length (\<Delta> @ [\<sigma>])) (sabstract_prefix (\<Delta> @ [\<sigma>]) A))
      (rev (sfresh_vars (length (\<Delta> @ [\<sigma>]))))) (sapp_vec (sraise ?n ?K) ?vars)"
    using contextual_step by (simp add: sabstract_prefix_snoc sreverse_fresh_vars_Suc)
  have tail: "sbeta_eta_equiv_in_signature L \<Sigma> (\<Delta> @ (\<sigma> # \<Gamma>)) \<tau>
    (sapp_vec (sraise ?n ?K) ?vars) A"
    by (rule snoc.IH[where \<Gamma>="\<sigma> # \<Gamma>", OF tail_language])
  have tail': "sbeta_eta_equiv_in_signature L \<Sigma> ((\<Delta> @ [\<sigma>]) @ \<Gamma>) \<tau>
    (sapp_vec (sraise ?n ?K) ?vars) A"
    using tail by (simp only: append_assoc append_Cons append_Nil)
  show ?case by (rule sbeta_eta_equiv_in_signature.Trans[
    OF sbeta_eta_equiv_in_signature.Beta[OF source_type middle_type source_sig middle_sig step] tail'])
qed

end
