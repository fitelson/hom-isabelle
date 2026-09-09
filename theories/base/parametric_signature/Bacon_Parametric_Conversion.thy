theory Bacon_Parametric_Conversion
  imports Bacon_Parametric_Contraction
begin

section \<open>Compatible contraction and its string representation\<close>

text \<open>
  A →βη B may contract one occurrence inside a larger term, including λv.A.

  Isabelle representation: pcompatible_step closes a supplied root relation
  under each syntax constructor.  Its typing proof reconstructs the same
  context after applying subject reduction to the changed subterm.

  Status: one contextual step and its string translation.  BBK_Semantics
  introduces both the typed raw closure pbeta_eta_equiv and the separate
  signature-indexed closure used in the model interface.
\<close>

inductive pcompatible_step ::
    "('c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool) \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool"
  for R :: "'c pterm \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  root: "R M N \<Longrightarrow> pcompatible_step R M N"
| App_left: "pcompatible_step R M M' \<Longrightarrow>
    pcompatible_step R (PApp M N) (PApp M' N)"
| App_right: "pcompatible_step R N N' \<Longrightarrow>
    pcompatible_step R (PApp M N) (PApp M N')"
| Lam_body: "pcompatible_step R M M' \<Longrightarrow>
    pcompatible_step R (PLam \<sigma> M) (PLam \<sigma> M')"
| Eq_left: "pcompatible_step R M M' \<Longrightarrow>
    pcompatible_step R (PEq \<sigma> M N) (PEq \<sigma> M' N)"
| Eq_right: "pcompatible_step R N N' \<Longrightarrow>
    pcompatible_step R (PEq \<sigma> M N) (PEq \<sigma> M N')"
| Neg_body: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PNeg A) (PNeg A')"
| Conj_left: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PConj A B) (PConj A' B)"
| Conj_right: "pcompatible_step R B B' \<Longrightarrow>
    pcompatible_step R (PConj A B) (PConj A B')"
| Disj_left: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PDisj A B) (PDisj A' B)"
| Disj_right: "pcompatible_step R B B' \<Longrightarrow>
    pcompatible_step R (PDisj A B) (PDisj A B')"
| Imp_left: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PImp A B) (PImp A' B)"
| Imp_right: "pcompatible_step R B B' \<Longrightarrow>
    pcompatible_step R (PImp A B) (PImp A B')"
| Forall_body: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PForall \<sigma> A) (PForall \<sigma> A')"
| Exists_body: "pcompatible_step R A A' \<Longrightarrow>
    pcompatible_step R (PExists \<sigma> A) (PExists \<sigma> A')"

lemma pcompatible_preserves_typing:
  assumes step: "pcompatible_step R M N"
    and root_preserves: "\<And>A B \<Gamma> \<tau>. R A B \<Longrightarrow> has_ptype \<Gamma> A \<tau> \<Longrightarrow> has_ptype \<Gamma> B \<tau>"
    and typed: "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> N \<tau>"
  using step typed
proof (induction arbitrary: \<Gamma> \<tau> rule: pcompatible_step.induct)
  case (root M N)
  show ?case using root.hyps root.prems by (rule root_preserves)
next
  case (App_left M M' N)
  obtain \<sigma> where M: "has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and N: "has_ptype \<Gamma> N \<sigma>"
    using App_left.prems[unfolded ptype_app_iff] by (elim exE conjE)
  have changed: "has_ptype \<Gamma> M' (\<sigma> \<rightarrow>\<^sub>o \<tau>)" by (rule App_left.IH[OF M])
  show ?case by (rule has_ptype.PApp[OF changed N])
next
  case (App_right N N' M)
  obtain \<sigma> where M: "has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and N: "has_ptype \<Gamma> N \<sigma>"
    using App_right.prems[unfolded ptype_app_iff] by (elim exE conjE)
  have changed: "has_ptype \<Gamma> N' \<sigma>" by (rule App_right.IH[OF N])
  show ?case by (rule has_ptype.PApp[OF M changed])
next
  case (Lam_body M M' \<sigma>)
  obtain \<rho> where eq: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<rho>" and M: "has_ptype (\<sigma> # \<Gamma>) M \<rho>"
    using Lam_body.prems[unfolded ptype_lam_iff] by (elim exE conjE)
  have changed: "has_ptype (\<sigma> # \<Gamma>) M' \<rho>" by (rule Lam_body.IH[OF M])
  show ?case using has_ptype.PLam[OF changed] by (simp only: eq)
next
  case (Eq_left M M' \<sigma> N)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>"
    using Eq_left.prems by (simp only: ptype_eq_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>" by (rule conjunct2[OF parts])
  have M: "has_ptype \<Gamma> M \<sigma>" by (rule conjunct1[OF typing_pair])
  have N: "has_ptype \<Gamma> N \<sigma>" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> M' \<sigma>" by (rule Eq_left.IH[OF M])
  show ?case using has_ptype.PEq[OF changed N] by (simp only: eq)
next
  case (Eq_right N N' \<sigma> M)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>"
    using Eq_right.prems by (simp only: ptype_eq_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> M \<sigma> \<and> has_ptype \<Gamma> N \<sigma>" by (rule conjunct2[OF parts])
  have M: "has_ptype \<Gamma> M \<sigma>" by (rule conjunct1[OF typing_pair])
  have N: "has_ptype \<Gamma> N \<sigma>" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> N' \<sigma>" by (rule Eq_right.IH[OF N])
  show ?case using has_ptype.PEq[OF M changed] by (simp only: eq)
next
  case (Neg_body A A')
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop"
    using Neg_body.prems by (simp only: ptype_neg_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct2[OF parts])
  have changed: "has_ptype \<Gamma> A' Prop" by (rule Neg_body.IH[OF A])
  show ?case using has_ptype.PNeg[OF changed] by (simp only: eq)
next
  case (Conj_left A A' B)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Conj_left.prems by (simp only: ptype_conj_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> A' Prop" by (rule Conj_left.IH[OF A])
  show ?case using has_ptype.PConj[OF changed B] by (simp only: eq)
next
  case (Conj_right B B' A)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Conj_right.prems by (simp only: ptype_conj_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> B' Prop" by (rule Conj_right.IH[OF B])
  show ?case using has_ptype.PConj[OF A changed] by (simp only: eq)
next
  case (Disj_left A A' B)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Disj_left.prems by (simp only: ptype_disj_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> A' Prop" by (rule Disj_left.IH[OF A])
  show ?case using has_ptype.PDisj[OF changed B] by (simp only: eq)
next
  case (Disj_right B B' A)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Disj_right.prems by (simp only: ptype_disj_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> B' Prop" by (rule Disj_right.IH[OF B])
  show ?case using has_ptype.PDisj[OF A changed] by (simp only: eq)
next
  case (Imp_left A A' B)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Imp_left.prems by (simp only: ptype_imp_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> A' Prop" by (rule Imp_left.IH[OF A])
  show ?case using has_ptype.PImp[OF changed B] by (simp only: eq)
next
  case (Imp_right B B' A)
  have parts: "\<tau> = Prop \<and> has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop"
    using Imp_right.prems by (simp only: ptype_imp_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have typing_pair: "has_ptype \<Gamma> A Prop \<and> has_ptype \<Gamma> B Prop" by (rule conjunct2[OF parts])
  have A: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF typing_pair])
  have B: "has_ptype \<Gamma> B Prop" by (rule conjunct2[OF typing_pair])
  have changed: "has_ptype \<Gamma> B' Prop" by (rule Imp_right.IH[OF B])
  show ?case using has_ptype.PImp[OF A changed] by (simp only: eq)
next
  case (Forall_body A A' \<sigma>)
  have parts: "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
    using Forall_body.prems by (simp only: ptype_forall_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have A: "has_ptype (\<sigma> # \<Gamma>) A Prop" by (rule conjunct2[OF parts])
  have changed: "has_ptype (\<sigma> # \<Gamma>) A' Prop" by (rule Forall_body.IH[OF A])
  show ?case using has_ptype.PForall[OF changed] by (simp only: eq)
next
  case (Exists_body A A' \<sigma>)
  have parts: "\<tau> = Prop \<and> has_ptype (\<sigma> # \<Gamma>) A Prop"
    using Exists_body.prems by (simp only: ptype_exists_iff)
  have eq: "\<tau> = Prop" by (rule conjunct1[OF parts])
  have A: "has_ptype (\<sigma> # \<Gamma>) A Prop" by (rule conjunct2[OF parts])
  have changed: "has_ptype (\<sigma> # \<Gamma>) A' Prop" by (rule Exists_body.IH[OF A])
  show ?case using has_ptype.PExists[OF changed] by (simp only: eq)
qed

corollary pcompatible_beta_preserves_typing:
  assumes "pcompatible_step pbeta_contract M N" and "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> N \<tau>"
  using assms(1) pbeta_preserves_typing assms(2) by (rule pcompatible_preserves_typing)

corollary pcompatible_eta_preserves_typing:
  assumes "pcompatible_step peta_contract M N" and "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> N \<tau>"
  using assms(1) peta_preserves_typing assms(2) by (rule pcompatible_preserves_typing)

section \<open>Exact string-instance correspondence\<close>

text \<open>
  A →βη B in the arbitrary-name syntax agrees, at string names, with
  the same contraction in the existing syntax.

  Isabelle representation: pbeta_to_oterm, peta_to_oterm, and contextual
  correspondence lemmas use translations that commute with A[B/v] and pshift.

  Status: two-way correspondence for the represented steps, not a completeness
  or conservativity theorem for a logical theory.
\<close>

lemma pbeta_to_oterm:
  assumes "pbeta_contract M N"
  shows "beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  using assms by cases (simp add: pterm_to_psubst0 beta_contract.beta)

lemma pbeta_of_oterm:
  assumes "beta_contract M N"
  shows "pbeta_contract (pterm_of_oterm M) (pterm_of_oterm N)"
  using assms by cases (simp add: pterm_of_subst0 pbeta_contract.beta)

lemma peta_to_oterm:
  assumes "peta_contract M N"
  shows "eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  using assms by cases (simp add: pterm_to_pshift eta_contract.eta)

lemma peta_of_oterm:
  assumes "eta_contract M N"
  shows "peta_contract (pterm_of_oterm M) (pterm_of_oterm N)"
  using assms by cases (simp add: pterm_of_shift peta_contract.eta)

lemma pbeta_string_iff:
  "pbeta_contract M N \<longleftrightarrow> beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
proof
  assume "pbeta_contract M N"
  then show "beta_contract (pterm_to_oterm M) (pterm_to_oterm N)" by (rule pbeta_to_oterm)
next
  assume "beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  then have "pbeta_contract (pterm_of_oterm (pterm_to_oterm M)) (pterm_of_oterm (pterm_to_oterm N))"
    by (rule pbeta_of_oterm)
  then show "pbeta_contract M N" by simp
qed

lemma peta_string_iff:
  "peta_contract M N \<longleftrightarrow> eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
proof
  assume "peta_contract M N"
  then show "eta_contract (pterm_to_oterm M) (pterm_to_oterm N)" by (rule peta_to_oterm)
next
  assume "eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  then have "peta_contract (pterm_of_oterm (pterm_to_oterm M)) (pterm_of_oterm (pterm_to_oterm N))"
    by (rule peta_of_oterm)
  then show "peta_contract M N" by simp
qed

lemma pcompatible_to_oterm:
  assumes step: "pcompatible_step R M N"
    and transfer: "\<And>A B. R A B \<Longrightarrow> S (pterm_to_oterm A) (pterm_to_oterm B)"
  shows "compatible_step S (pterm_to_oterm M) (pterm_to_oterm N)"
  using step
proof (induction rule: pcompatible_step.induct)
  case (root M N)
  have mapped: "S (pterm_to_oterm M) (pterm_to_oterm N)" by (rule transfer[OF root.hyps])
  show ?case by (rule compatible_step.root[where R=S and M="pterm_to_oterm M"
    and N="pterm_to_oterm N", OF mapped])
next
  case (App_left M M' N)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.App_left[OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.App_right[OF App_right.IH])
next
  case (Lam_body M M' \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Lam_body[OF Lam_body.IH])
next
  case (Eq_left M M' \<sigma> N)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Eq_left[OF Eq_left.IH])
next
  case (Eq_right N N' \<sigma> M)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Eq_right[OF Eq_right.IH])
next
  case (Neg_body A A')
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Neg_body[OF Neg_body.IH])
next
  case (Conj_left A A' B)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Conj_left[OF Conj_left.IH])
next
  case (Conj_right B B' A)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Conj_right[OF Conj_right.IH])
next
  case (Disj_left A A' B)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Disj_left[OF Disj_left.IH])
next
  case (Disj_right B B' A)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Disj_right[OF Disj_right.IH])
next
  case (Imp_left A A' B)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Imp_left[OF Imp_left.IH])
next
  case (Imp_right B B' A)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Imp_right[OF Imp_right.IH])
next
  case (Forall_body A A' \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Forall_body[OF Forall_body.IH])
next
  case (Exists_body A A' \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps; rule compatible_step.Exists_body[OF Exists_body.IH])
qed

lemma pcompatible_of_oterm:
  assumes step: "compatible_step R M N"
    and transfer: "\<And>A B. R A B \<Longrightarrow> S (pterm_of_oterm A) (pterm_of_oterm B)"
  shows "pcompatible_step S (pterm_of_oterm M) (pterm_of_oterm N)"
  using step
proof (induction rule: compatible_step.induct)
  case (root M N)
  have mapped: "S (pterm_of_oterm M) (pterm_of_oterm N)" by (rule transfer[OF root.hyps])
  show ?case by (rule pcompatible_step.root[where R=S and M="pterm_of_oterm M"
    and N="pterm_of_oterm N", OF mapped])
next
  case (App_left M M' N)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.App_left[OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.App_right[OF App_right.IH])
next
  case (Lam_body M M' \<sigma>)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Lam_body[OF Lam_body.IH])
next
  case (Eq_left M M' \<sigma> N)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Eq_left[OF Eq_left.IH])
next
  case (Eq_right N N' \<sigma> M)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Eq_right[OF Eq_right.IH])
next
  case (Neg_body A A')
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Neg_body[OF Neg_body.IH])
next
  case (Conj_left A A' B)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Conj_left[OF Conj_left.IH])
next
  case (Conj_right B B' A)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Conj_right[OF Conj_right.IH])
next
  case (Disj_left A A' B)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Disj_left[OF Disj_left.IH])
next
  case (Disj_right B B' A)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Disj_right[OF Disj_right.IH])
next
  case (Imp_left A A' B)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Imp_left[OF Imp_left.IH])
next
  case (Imp_right B B' A)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Imp_right[OF Imp_right.IH])
next
  case (Forall_body A A' \<sigma>)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Forall_body[OF Forall_body.IH])
next
  case (Exists_body A A' \<sigma>)
  show ?case by (simp only: pterm_of_oterm.simps; rule pcompatible_step.Exists_body[OF Exists_body.IH])
qed

lemma pcompatible_beta_string_iff:
  "pcompatible_step pbeta_contract M N \<longleftrightarrow>
    compatible_step beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
proof
  assume step: "pcompatible_step pbeta_contract M N"
  show "compatible_step beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
    using step pbeta_to_oterm by (rule pcompatible_to_oterm)
next
  assume step: "compatible_step beta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  have "pcompatible_step pbeta_contract (pterm_of_oterm (pterm_to_oterm M))
      (pterm_of_oterm (pterm_to_oterm N))"
    using step pbeta_of_oterm by (rule pcompatible_of_oterm)
  then show "pcompatible_step pbeta_contract M N" by simp
qed

lemma pcompatible_eta_string_iff:
  "pcompatible_step peta_contract M N \<longleftrightarrow>
    compatible_step eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
proof
  assume step: "pcompatible_step peta_contract M N"
  show "compatible_step eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
    using step peta_to_oterm by (rule pcompatible_to_oterm)
next
  assume step: "compatible_step eta_contract (pterm_to_oterm M) (pterm_to_oterm N)"
  have "pcompatible_step peta_contract (pterm_of_oterm (pterm_to_oterm M))
      (pterm_of_oterm (pterm_to_oterm N))"
    using step peta_of_oterm by (rule pcompatible_of_oterm)
  then show "pcompatible_step peta_contract M N" by simp
qed

end
