theory Bacon_Parametric_Canonical_Model_Support
  imports Bacon_Parametric_Canonical_Quantifiers
begin

section \<open>Interpretation respects free variables and language-relative conversion\<close>

text \<open>
  If g and h agree on the free variables of A, then ⟦A⟧g = ⟦A⟧h.
  Also A =βη B within ℒ(Σ) implies equality of their denotations.
  Source: Bacon–Dorr Definition 3.1(ii.c–d), pp.43–44.

  The conversion relation guards every node of the chain by Σ.  This
  matters because β contraction can discard a foreign constant; endpoint
  guards alone do not constrain an arbitrary raw conversion chain.
  All canonical conclusions below remain conditional on pH_closed_Henkin.
\<close>

lemma pHcm_lift_free_agreement:
  assumes agree: "\<And>n. Suc n \<in> pbbk_fv M \<Longrightarrow> s n = r n"
    and member: "n \<in> pbbk_fv M"
  shows "plift_subst s n = plift_subst r n"
proof (cases n)
  case 0
  show ?thesis by (simp add: 0)
next
  case (Suc m)
  have in_body: "Suc m \<in> pbbk_fv M" using member by (simp only: Suc)
  have eq: "s m = r m" by (rule agree[OF in_body])
  show ?thesis by (simp only: Suc plift_subst.simps eq)
qed

lemma pHcm_subst_free_agreement:
  assumes agree: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> s n = r n"
  shows "psubst s M = psubst r M"
  using agree
proof (induction M arbitrary: s r)
  case (PVar n)
  have eq: "s n = r n" by (rule PVar.prems) simp
  show ?case by (simp only: psubst.simps eq)
next
  case (PConst c \<sigma>)
  show ?case by (simp only: psubst.simps)
next
  case (PApp M N)
  have left: "psubst s M = psubst r M"
    by (rule PApp.IH(1)[where s=s and r=r]) (rule PApp.prems, simp)
  have right: "psubst s N = psubst r N"
    by (rule PApp.IH(2)[where s=s and r=r]) (rule PApp.prems, simp)
  show ?case by (simp only: psubst.simps left right)
next
  case (PLam \<sigma> M)
  have tail: "\<And>n. Suc n \<in> pbbk_fv M \<Longrightarrow> s n = r n"
    using PLam.prems by (simp only: pbbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> plift_subst s n = plift_subst r n"
    by (rule pHcm_lift_free_agreement[OF tail])
  have body: "psubst (plift_subst s) M = psubst (plift_subst r) M"
    by (rule PLam.IH[where s="plift_subst s" and r="plift_subst r", OF lifted])
  show ?case by (simp only: psubst.simps body)
next
  case (PEq \<sigma> M N)
  have left: "psubst s M = psubst r M"
    by (rule PEq.IH(1)[where s=s and r=r]) (rule PEq.prems, simp)
  have right: "psubst s N = psubst r N"
    by (rule PEq.IH(2)[where s=s and r=r]) (rule PEq.prems, simp)
  show ?case by (simp only: psubst.simps left right)
next
  case (PNeg M)
  have body: "psubst s M = psubst r M"
    by (rule PNeg.IH[where s=s and r=r]) (rule PNeg.prems, simp)
  show ?case by (simp only: psubst.simps body)
next
  case (PConj M N)
  have left: "psubst s M = psubst r M"
    by (rule PConj.IH(1)[where s=s and r=r]) (rule PConj.prems, simp)
  have right: "psubst s N = psubst r N"
    by (rule PConj.IH(2)[where s=s and r=r]) (rule PConj.prems, simp)
  show ?case by (simp only: psubst.simps left right)
next
  case (PDisj M N)
  have left: "psubst s M = psubst r M"
    by (rule PDisj.IH(1)[where s=s and r=r]) (rule PDisj.prems, simp)
  have right: "psubst s N = psubst r N"
    by (rule PDisj.IH(2)[where s=s and r=r]) (rule PDisj.prems, simp)
  show ?case by (simp only: psubst.simps left right)
next
  case (PImp M N)
  have left: "psubst s M = psubst r M"
    by (rule PImp.IH(1)[where s=s and r=r]) (rule PImp.prems, simp)
  have right: "psubst s N = psubst r N"
    by (rule PImp.IH(2)[where s=s and r=r]) (rule PImp.prems, simp)
  show ?case by (simp only: psubst.simps left right)
next
  case (PForall \<sigma> M)
  have tail: "\<And>n. Suc n \<in> pbbk_fv M \<Longrightarrow> s n = r n"
    using PForall.prems by (simp only: pbbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> plift_subst s n = plift_subst r n"
    by (rule pHcm_lift_free_agreement[OF tail])
  have body: "psubst (plift_subst s) M = psubst (plift_subst r) M"
    by (rule PForall.IH[where s="plift_subst s" and r="plift_subst r", OF lifted])
  show ?case by (simp only: psubst.simps body)
next
  case (PExists \<sigma> M)
  have tail: "\<And>n. Suc n \<in> pbbk_fv M \<Longrightarrow> s n = r n"
    using PExists.prems by (simp only: pbbk_fv.simps mem_Collect_eq)
  have lifted: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> plift_subst s n = plift_subst r n"
    by (rule pHcm_lift_free_agreement[OF tail])
  have body: "psubst (plift_subst s) M = psubst (plift_subst r) M"
    by (rule PExists.IH[where s="plift_subst s" and r="plift_subst r", OF lifted])
  show ?case by (simp only: psubst.simps body)
qed

lemma pHcm_subst_subst0:
  "psubst s (psubst0 W A) = psubst0 (psubst s W) (psubst (plift_subst s) A)"
proof -
  have maps: "(\<lambda>n. psubst s (case_nat W PVar n)) = case_nat (psubst s W) s"
  proof (rule ext)
    fix n :: nat
    show "psubst s (case_nat W PVar n) = case_nat (psubst s W) s n" by (cases n; simp)
  qed
  have lhs: "psubst s (psubst0 W A) = psubst (case_nat (psubst s W) s) A"
    by (simp only: psubst0_def pHcs_subst_comp maps)
  have rhs: "psubst0 (psubst s W) (psubst (plift_subst s) A) =
      psubst (case_nat (psubst s W) s) A"
    using pHcs_head_tail[where s="case_nat (psubst s W) s" and M=A] by simp
  show ?thesis by (rule trans[OF lhs sym[OF rhs]])
qed

lemma pHcm_beta_subst:
  assumes step: "pbeta_contract A B"
  shows "pbeta_contract (psubst s A) (psubst s B)"
  using step
proof cases
  case (beta \<sigma> M N)
  have redex: "pbeta_contract (PApp (PLam \<sigma> (psubst (plift_subst s) M)) (psubst s N))
      (psubst0 (psubst s N) (psubst (plift_subst s) M))" by (rule pbeta_contract.beta)
  show ?thesis using beta redex by (simp add: pHcm_subst_subst0)
qed

lemma pHcm_eta_subst:
  assumes step: "peta_contract A B"
  shows "peta_contract (psubst s A) (psubst s B)"
  using step
proof cases
  case (eta \<sigma>)
  have redex: "peta_contract (PLam \<sigma> (PApp (pshift (psubst s B)) (PVar 0))) (psubst s B)"
    by (rule peta_contract.eta)
  show ?thesis using eta redex by (simp add: pproof_psubst_lift_shift)
qed

lemma pHcm_compatible_subst:
  assumes step: "pcompatible_step R A B"
    and roots: "\<And>s X Y. R X Y \<Longrightarrow> R (psubst s X) (psubst s Y)"
  shows "pcompatible_step R (psubst s A) (psubst s B)"
  using step
proof (induction arbitrary: s rule: pcompatible_step.induct)
  case (root X Y)
  show ?case by (rule pcompatible_step.root[where R=R and M="psubst s X" and N="psubst s Y",
    OF roots[where s=s and X=X and Y=Y, OF root.hyps]])
next
  case (App_left X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.App_left[where R=R and M="psubst s X" and M'="psubst s Y" and N="psubst s Z",
      OF App_left.IH[where s="s"]])
next
  case (App_right X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.App_right[where R=R and N="psubst s X" and N'="psubst s Y" and M="psubst s Z",
      OF App_right.IH[where s="s"]])
next
  case (Lam_body X Y \<tau>)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Lam_body[where R=R and M="psubst (plift_subst s) X" and M'="psubst (plift_subst s) Y" and \<sigma>="\<tau>",
      OF Lam_body.IH[where s="plift_subst s"]])
next
  case (Eq_left X Y \<tau> Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Eq_left[where R=R and M="psubst s X" and M'="psubst s Y" and \<sigma>="\<tau>" and N="psubst s Z",
      OF Eq_left.IH[where s="s"]])
next
  case (Eq_right X Y \<tau> Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Eq_right[where R=R and N="psubst s X" and N'="psubst s Y" and \<sigma>="\<tau>" and M="psubst s Z",
      OF Eq_right.IH[where s="s"]])
next
  case (Neg_body X Y)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Neg_body[where R=R and A="psubst s X" and A'="psubst s Y",
      OF Neg_body.IH[where s="s"]])
next
  case (Conj_left X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Conj_left[where R=R and A="psubst s X" and A'="psubst s Y" and B="psubst s Z",
      OF Conj_left.IH[where s="s"]])
next
  case (Conj_right X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Conj_right[where R=R and B="psubst s X" and B'="psubst s Y" and A="psubst s Z",
      OF Conj_right.IH[where s="s"]])
next
  case (Disj_left X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Disj_left[where R=R and A="psubst s X" and A'="psubst s Y" and B="psubst s Z",
      OF Disj_left.IH[where s="s"]])
next
  case (Disj_right X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Disj_right[where R=R and B="psubst s X" and B'="psubst s Y" and A="psubst s Z",
      OF Disj_right.IH[where s="s"]])
next
  case (Imp_left X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Imp_left[where R=R and A="psubst s X" and A'="psubst s Y" and B="psubst s Z",
      OF Imp_left.IH[where s="s"]])
next
  case (Imp_right X Y Z)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Imp_right[where R=R and B="psubst s X" and B'="psubst s Y" and A="psubst s Z",
      OF Imp_right.IH[where s="s"]])
next
  case (Forall_body X Y \<tau>)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Forall_body[where R=R and A="psubst (plift_subst s) X" and A'="psubst (plift_subst s) Y" and \<sigma>="\<tau>",
      OF Forall_body.IH[where s="plift_subst s"]])
next
  case (Exists_body X Y \<tau>)
  show ?case by (simp only: psubst.simps)
    (rule pcompatible_step.Exists_body[where R=R and A="psubst (plift_subst s) X" and A'="psubst (plift_subst s) Y" and \<sigma>="\<tau>",
      OF Exists_body.IH[where s="plift_subst s"]])
qed

context pH_closed_Henkin
begin

lemma pHcm_denote_locality:
  assumes same: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> g n = h n"
  shows "pHc_denote g M = pHc_denote h M"
proof -
  have representatives: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> pHc_rep (g n) = pHc_rep (h n)"
    by (simp only: same)
  have terms: "psubst (\<lambda>n. pHc_rep (g n)) M = psubst (\<lambda>n. pHc_rep (h n)) M"
    by (rule pHcm_subst_free_agreement[where M=M and s="\<lambda>n. pHc_rep (g n)"
      and r="\<lambda>n. pHc_rep (h n)", OF representatives])
  show ?thesis by (simp only: pHc_denote_def terms)
qed

lemma pHcm_denote_rename:
  "pHc_denote g (prename r M) = pHc_denote (\<lambda>n. g (r n)) M"
  by (simp add: pHc_denote_def pproof_psubst_prename comp_def)

lemma pHcm_eta_identity:
  assumes lm: "pterm_in_language signature [] M \<tau>" and ln: "pterm_in_language signature [] N \<tau>"
    and step: "pcompatible_step peta_contract M N"
  shows "pH_term_eq \<tau> M N"
proof -
  have mt: "has_ptype [] M \<tau>" and ms: "pterm_in_signature signature M"
    using lm unfolding pterm_in_language_def by simp_all
  have nt: "has_ptype [] N \<tau>" and ns: "pterm_in_signature signature N"
    using ln unfolding pterm_in_language_def by simp_all
  have rt: "has_ptype [] (PEq \<tau> M M) Prop" by (rule has_ptype.PEq[OF mt mt])
  have it: "has_ptype [] (PEq \<tau> M N) Prop" by (rule has_ptype.PEq[OF mt nt])
  have rs: "pterm_in_signature signature (PEq \<tau> M M)" and ids: "pterm_in_signature signature (PEq \<tau> M N)"
    using ms ns by simp_all
  have contextual: "pcompatible_step peta_contract (PEq \<tau> M M) (PEq \<tau> M N)"
    by (rule pcompatible_step.Eq_right[where R=peta_contract and M=M and N=M and N'=N and \<sigma>=\<tau>, OF step])
  have theorem_eq: "pH_proves signature [] (PObjIff (PEq \<tau> M M) (PEq \<tau> M N))"
    by (rule pH_proves.Eta[OF rt it contextual rs ids])
  have reference: "PEq \<tau> M M \<in> T" by (rule pH_term_eq_member[OF pH_term_eq_refl[OF lm]])
  have identity: "PEq \<tau> M N \<in> T"
    by (rule iffD1[OF pH_biconditional_membership[OF rt it rs ids theorem_eq] reference])
  show ?thesis unfolding pH_term_eq_def by (intro conjI lm ln identity)
qed

lemma pHcm_denote_beta:
  assumes mt: "has_ptype \<Gamma> M \<tau>" and nt: "has_ptype \<Gamma> N \<tau>"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and step: "pcompatible_step pbeta_contract M N" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M = pHc_denote g N"
proof -
  let ?s = "\<lambda>n. pHc_rep (g n)"
  have ml: "pterm_in_language signature [] (psubst ?s M) \<tau>" by (rule pHc_closed_instance_language[OF mt ms env])
  have nl: "pterm_in_language signature [] (psubst ?s N) \<tau>" by (rule pHc_closed_instance_language[OF nt ns env])
  have converted: "pcompatible_step pbeta_contract (psubst ?s M) (psubst ?s N)"
    by (rule pHcm_compatible_subst[where R=pbeta_contract and A=M and B=N and s="?s", OF step]) (rule pHcm_beta_subst)
  have eq: "pH_term_eq \<tau> (psubst ?s M) (psubst ?s N)" by (rule pHcs_beta_identity[OF ml nl converted])
  have classes: "pHc_class \<tau> (psubst ?s M) = pHc_class \<tau> (psubst ?s N)"
    by (rule iffD2[OF pHc_class_eq_iff[OF ml nl] eq])
  show ?thesis by (simp only: pHc_denote_typed_form[OF mt ms env] pHc_denote_typed_form[OF nt ns env] classes)
qed

lemma pHcm_denote_eta:
  assumes mt: "has_ptype \<Gamma> M \<tau>" and nt: "has_ptype \<Gamma> N \<tau>"
    and ms: "pterm_in_signature signature M" and ns: "pterm_in_signature signature N"
    and step: "pcompatible_step peta_contract M N" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M = pHc_denote g N"
proof -
  let ?s = "\<lambda>n. pHc_rep (g n)"
  have ml: "pterm_in_language signature [] (psubst ?s M) \<tau>" by (rule pHc_closed_instance_language[OF mt ms env])
  have nl: "pterm_in_language signature [] (psubst ?s N) \<tau>" by (rule pHc_closed_instance_language[OF nt ns env])
  have converted: "pcompatible_step peta_contract (psubst ?s M) (psubst ?s N)"
    by (rule pHcm_compatible_subst[where R=peta_contract and A=M and B=N and s="?s", OF step]) (rule pHcm_eta_subst)
  have eq: "pH_term_eq \<tau> (psubst ?s M) (psubst ?s N)" by (rule pHcm_eta_identity[OF ml nl converted])
  have classes: "pHc_class \<tau> (psubst ?s M) = pHc_class \<tau> (psubst ?s N)"
    by (rule iffD2[OF pHc_class_eq_iff[OF ml nl] eq])
  show ?thesis by (simp only: pHc_denote_typed_form[OF mt ms env] pHc_denote_typed_form[OF nt ns env] classes)
qed

lemma pHcm_denote_beta_eta:
  assumes conversion: "pbeta_eta_equiv_in_signature signature \<Gamma> \<tau> M N"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M = pHc_denote g N"
  using conversion env
proof (induction arbitrary: g rule: pbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule refl)
next
  case (Beta \<Gamma> M \<tau> N)
  show ?case by (rule pHcm_denote_beta[OF Beta.hyps(1,2,3,4,5) Beta.prems])
next
  case (Eta \<Gamma> M \<tau> N)
  show ?case by (rule pHcm_denote_eta[OF Eta.hyps(1,2,3,4,5) Eta.prems])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule sym[OF Sym.IH[where g=g, OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule trans[OF Trans.IH(1)[where g=g, OF Trans.prems] Trans.IH(2)[where g=g, OF Trans.prems]])
qed

end
end
