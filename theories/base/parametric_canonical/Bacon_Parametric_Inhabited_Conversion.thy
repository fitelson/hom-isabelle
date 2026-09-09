theory Bacon_Parametric_Inhabited_Conversion
  imports Bacon_Parametric_Canonical_Domain
begin

section \<open>Raw and language-relative conversion in inhabited signatures\<close>

text \<open>
  Suppose every type σ has a closed Wσ ∈ ℒ(Σ).  For M,N ∈ ℒ(Σ),
  M ≡βη N in the unrestricted syntax iff there is a βη conversion
  between them wholly inside ℒ(Σ).  Replace each foreign c:σ in a
  conversion by Wσ, keeping declared constants unchanged.  This fixes
  M and N and preserves every conversion step.

  Source role: clarifies the language qualification in Bacon–Dorr
  Definition 3.1(ii.d), pp.43–44, for the inhabited Henkin signatures used
  in Theorem 3.2 and p.45 n.64.  It is a syntactic support result, not a
  new semantic axiom.  The signature-indexed BBK interface is unchanged.

  Isabelle representation: a single retraction replaces all foreign
  typed constants simultaneously.  Its replacements are closed, so the
  same map works under λ, ∀, and ∃.  No finite enumeration, countability,
  Functionality, or preservation of the raw constant-name set is assumed.
  In particular, β contraction can erase foreign constants.
\<close>

locale pH_signature_retraction =
  fixes signature :: "'c psignature" and inhabitant :: "otype \<Rightarrow> 'c pterm"
  assumes inhabited: "\<And>\<sigma>. pterm_in_language signature [] (inhabitant \<sigma>) \<sigma>"
begin

lemma pHsr_inhabitant_type: "has_ptype [] (inhabitant \<sigma>) \<sigma>"
  using inhabited[of \<sigma>] unfolding pterm_in_language_def by (rule conjunct1)

lemma pHsr_inhabitant_signature: "pterm_in_signature signature (inhabitant \<sigma>)"
  using inhabited[of \<sigma>] unfolding pterm_in_language_def by (rule conjunct2)

lemma pHsr_inhabitant_subst: "psubst s (inhabitant \<sigma>) = inhabitant \<sigma>"
  by (rule pHcs_closed_subst[OF pHsr_inhabitant_type])

lemma pHsr_inhabitant_rename: "prename r (inhabitant \<sigma>) = inhabitant \<sigma>"
proof -
  have equation: "prename r (inhabitant \<sigma>) = psubst (\<lambda>n. PVar (r n)) (inhabitant \<sigma>)"
    using pproof_prename_psubst[where r=r and s=PVar and M="inhabitant \<sigma>"]
    by (simp only: pHcs_subst_ident prename.simps)
  show ?thesis by (simp only: equation pHsr_inhabitant_subst)
qed

lemma pHsr_inhabitant_type_any: "has_ptype \<Gamma> (inhabitant \<sigma>) \<sigma>"
proof -
  have renamed: "has_ptype \<Gamma> (prename id (inhabitant \<sigma>)) \<sigma>"
    by (rule prename_preserves_typing[OF pHsr_inhabitant_type]) (simp add: lookup_def)
  show ?thesis using renamed by (simp only: pHsr_inhabitant_rename)
qed

fun pHsr :: "'c pterm \<Rightarrow> 'c pterm" where
  "pHsr (PVar n) = PVar n"
| "pHsr (PConst c \<sigma>) = (if c \<in> signature \<sigma> then PConst c \<sigma> else inhabitant \<sigma>)"
| "pHsr (PApp M N) = PApp (pHsr M) (pHsr N)"
| "pHsr (PLam \<sigma> M) = PLam \<sigma> (pHsr M)"
| "pHsr (PEq \<sigma> M N) = PEq \<sigma> (pHsr M) (pHsr N)"
| "pHsr (PNeg A) = PNeg (pHsr A)"
| "pHsr (PConj A B) = PConj (pHsr A) (pHsr B)"
| "pHsr (PDisj A B) = PDisj (pHsr A) (pHsr B)"
| "pHsr (PImp A B) = PImp (pHsr A) (pHsr B)"
| "pHsr (PForall \<sigma> A) = PForall \<sigma> (pHsr A)"
| "pHsr (PExists \<sigma> A) = PExists \<sigma> (pHsr A)"

lemma pHsr_signature: "pterm_in_signature signature (pHsr M)"
  by (induction M) (simp_all add: pHsr_inhabitant_signature)

lemma pHsr_fixes: "pterm_in_signature signature M \<Longrightarrow> pHsr M = M"
  by (induction M) simp_all

lemma pHsr_type:
  "has_ptype \<Gamma> M \<tau> \<Longrightarrow> has_ptype \<Gamma> (pHsr M) \<tau>"
proof (induction rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PVar[OF PVar.hyps])
next
  case (PConst \<Gamma> c \<tau>)
  show ?case
  proof (cases "c \<in> signature \<tau>")
    case True
    show ?thesis by (simp only: pHsr.simps True if_True) (rule has_ptype.PConst)
  next
    case False
    show ?thesis by (simp only: pHsr.simps False if_False) (rule pHsr_inhabitant_type_any)
  qed
next
  case (PApp \<Gamma> M \<sigma> \<tau> N)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PApp[OF PApp.IH])
next
  case (PLam \<sigma> \<Gamma> M \<tau>)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PLam[OF PLam.IH])
next
  case (PEq \<Gamma> M \<sigma> N)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PEq[OF PEq.IH])
next
  case (PNeg \<Gamma> A)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PNeg[OF PNeg.IH])
next
  case (PConj \<Gamma> A B)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PConj[OF PConj.IH])
next
  case (PDisj \<Gamma> A B)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PDisj[OF PDisj.IH])
next
  case (PImp \<Gamma> A B)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PImp[OF PImp.IH])
next
  case (PForall \<sigma> \<Gamma> A)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PForall[OF PForall.IH])
next
  case (PExists \<sigma> \<Gamma> A)
  show ?case by (simp only: pHsr.simps) (rule has_ptype.PExists[OF PExists.IH])
qed

subsection \<open>The retraction commutes with binder operations\<close>

text \<open>
  r(M[s]) = r(M)[v ↦ r(s(v))] and r(λv.M) = λv.r(M).
  Closed replacements prevent capture; this is why the inhabitation
  hypothesis is stated with the empty variable context.
\<close>

lemma pHsr_prename: "pHsr (prename r M) = prename r (pHsr M)"
  by (induction M arbitrary: r) (simp_all add: pHsr_inhabitant_rename split: if_splits)

lemma pHsr_shift: "pHsr (pshift M) = pshift (pHsr M)"
  by (simp only: pshift_def pHsr_prename)

lemma pHsr_lift:
  "(\<lambda>n. pHsr (plift_subst s n)) = plift_subst (\<lambda>n. pHsr (s n))"
  by (rule ext, rename_tac n, case_tac n) (simp_all only: plift_subst.simps pHsr.simps pHsr_prename)

lemma pHsr_subst:
  "pHsr (psubst s M) = psubst (\<lambda>n. pHsr (s n)) (pHsr M)"
  by (induction M arbitrary: s)
    (simp_all add: pHsr_lift pHsr_inhabitant_subst split: if_splits)

lemma pHsr_subst0:
  "pHsr (psubst0 W M) = psubst0 (pHsr W) (pHsr M)"
proof -
  have maps: "(\<lambda>n. pHsr (case_nat W PVar n)) = case_nat (pHsr W) PVar"
    by (rule ext, rename_tac n, case_tac n) simp_all
  show ?thesis by (simp only: psubst0_def pHsr_subst maps)
qed

lemma pHsr_beta: "pbeta_contract A B \<Longrightarrow> pbeta_contract (pHsr A) (pHsr B)"
proof (erule pbeta_contract.cases)
  fix \<sigma> M W
  assume source: "A = PApp (PLam \<sigma> M) W" and target: "B = psubst0 W M"
  show "pbeta_contract (pHsr A) (pHsr B)"
    by (simp only: source target pHsr.simps pHsr_subst0) (rule pbeta_contract.beta)
qed

lemma pHsr_eta: "peta_contract A B \<Longrightarrow> peta_contract (pHsr A) (pHsr B)"
proof (erule peta_contract.cases)
  fix \<sigma> M
  assume source: "A = PLam \<sigma> (PApp (pshift M) (PVar 0))" and target: "B = M"
  show "peta_contract (pHsr A) (pHsr B)"
    by (simp only: source target pHsr.simps pHsr_shift) (rule peta_contract.eta)
qed

lemma pHsr_compatible:
  assumes step: "pcompatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> R (pHsr X) (pHsr Y)"
  shows "pcompatible_step R (pHsr A) (pHsr B)"
  using step
proof (induction rule: pcompatible_step.induct)
  case (root X Y)
  show ?case by (rule pcompatible_step.root[where R=R and M="pHsr X" and N="pHsr Y"])
    (rule roots[OF root.hyps])
next
  case (App_left X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.App_left[where R=R and M="pHsr X" and M'="pHsr Y" and N="pHsr Z", OF App_left.IH])
next
  case (App_right X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.App_right[where R=R and N="pHsr X" and N'="pHsr Y" and M="pHsr Z", OF App_right.IH])
next
  case (Lam_body X Y \<sigma>)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Lam_body[where R=R and M="pHsr X" and M'="pHsr Y" and \<sigma>=\<sigma>, OF Lam_body.IH])
next
  case (Eq_left X Y \<sigma> Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Eq_left[where R=R and M="pHsr X" and M'="pHsr Y" and \<sigma>=\<sigma> and N="pHsr Z", OF Eq_left.IH])
next
  case (Eq_right X Y \<sigma> Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Eq_right[where R=R and N="pHsr X" and N'="pHsr Y" and \<sigma>=\<sigma> and M="pHsr Z", OF Eq_right.IH])
next
  case (Neg_body X Y)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Neg_body[where R=R and A="pHsr X" and A'="pHsr Y", OF Neg_body.IH])
next
  case (Conj_left X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Conj_left[where R=R and A="pHsr X" and A'="pHsr Y" and B="pHsr Z", OF Conj_left.IH])
next
  case (Conj_right X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Conj_right[where R=R and B="pHsr X" and B'="pHsr Y" and A="pHsr Z", OF Conj_right.IH])
next
  case (Disj_left X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Disj_left[where R=R and A="pHsr X" and A'="pHsr Y" and B="pHsr Z", OF Disj_left.IH])
next
  case (Disj_right X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Disj_right[where R=R and B="pHsr X" and B'="pHsr Y" and A="pHsr Z", OF Disj_right.IH])
next
  case (Imp_left X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Imp_left[where R=R and A="pHsr X" and A'="pHsr Y" and B="pHsr Z", OF Imp_left.IH])
next
  case (Imp_right X Y Z)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Imp_right[where R=R and B="pHsr X" and B'="pHsr Y" and A="pHsr Z", OF Imp_right.IH])
next
  case (Forall_body X Y \<sigma>)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Forall_body[where R=R and A="pHsr X" and A'="pHsr Y" and \<sigma>=\<sigma>, OF Forall_body.IH])
next
  case (Exists_body X Y \<sigma>)
  show ?case by (simp only: pHsr.simps)
    (rule pcompatible_step.Exists_body[where R=R and A="pHsr X" and A'="pHsr Y" and \<sigma>=\<sigma>, OF Exists_body.IH])
qed

lemma pHsr_conversion:
  "pbeta_eta_equiv \<Gamma> \<tau> M N \<Longrightarrow>
    pbeta_eta_equiv_in_signature signature \<Gamma> \<tau> (pHsr M) (pHsr N)"
proof (induction rule: pbeta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule pbeta_eta_equiv_in_signature.Refl[OF pHsr_type[OF Refl.hyps] pHsr_signature])
next
  case (Beta \<Gamma> M \<tau> N)
  have step: "pcompatible_step pbeta_contract (pHsr M) (pHsr N)"
    by (rule pHsr_compatible[where R=pbeta_contract, OF Beta.hyps(3) pHsr_beta])
  show ?case by (rule pbeta_eta_equiv_in_signature.Beta[OF
    pHsr_type[OF Beta.hyps(1)] pHsr_type[OF Beta.hyps(2)] pHsr_signature pHsr_signature step])
next
  case (Eta \<Gamma> M \<tau> N)
  have step: "pcompatible_step peta_contract (pHsr M) (pHsr N)"
    by (rule pHsr_compatible[where R=peta_contract, OF Eta.hyps(3) pHsr_eta])
  show ?case by (rule pbeta_eta_equiv_in_signature.Eta[OF
    pHsr_type[OF Eta.hyps(1)] pHsr_type[OF Eta.hyps(2)] pHsr_signature pHsr_signature step])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule pbeta_eta_equiv_in_signature.Sym[OF Sym.IH])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule pbeta_eta_equiv_in_signature.Trans[OF Trans.IH])
qed

end

theorem pbeta_eta_raw_to_inhabited_signature:
  assumes inhabitants: "\<And>\<sigma>. \<exists>W. pterm_in_language \<Sigma> [] W \<sigma>"
    and conversion: "pbeta_eta_equiv \<Gamma> \<tau> M N"
    and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
proof -
  let ?W = "\<lambda>\<sigma>. SOME W. pterm_in_language \<Sigma> [] W \<sigma>"
  interpret R: pH_signature_retraction \<Sigma> ?W
    by (unfold_locales) (rule someI_ex[OF inhabitants])
  let ?r = "pH_signature_retraction.pHsr \<Sigma> ?W"
  have converted: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> (?r M) (?r N)"
    by (rule R.pHsr_conversion[OF conversion])
  show ?thesis using converted by (simp only: R.pHsr_fixes[OF ms] R.pHsr_fixes[OF ns])
qed

corollary pbeta_eta_inhabited_signature_iff:
  assumes inhabitants: "\<And>\<sigma>. \<exists>W. pterm_in_language \<Sigma> [] W \<sigma>"
    and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N \<longleftrightarrow> pbeta_eta_equiv \<Gamma> \<tau> M N"
proof
  assume "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
  then show "pbeta_eta_equiv \<Gamma> \<tau> M N" by (rule pbeta_eta_equiv_in_signature_raw)
next
  assume raw: "pbeta_eta_equiv \<Gamma> \<tau> M N"
  show "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
    by (rule pbeta_eta_raw_to_inhabited_signature[OF inhabitants raw ms ns])
qed

context pH_closed_Henkin
begin

corollary pH_Henkin_raw_conversion_iff:
  assumes "pterm_in_signature signature M" and "pterm_in_signature signature N"
  shows "pbeta_eta_equiv_in_signature signature \<Gamma> \<tau> M N \<longleftrightarrow> pbeta_eta_equiv \<Gamma> \<tau> M N"
  by (rule pbeta_eta_inhabited_signature_iff[OF pHc_closed_inhabited assms])

end
end
