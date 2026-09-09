theory Bacon_Source_Named_Signature_Conservativity
  imports Bacon_Source_Named_Retraction_Steps Bacon_Source_Rich_Stock
begin

section \<open>A finite set of forbidden variables for the whole conversion\<close>

text \<open>
  If A ≡βη B using typed terms, a finite set S of variable names
  suffices to retract the whole conversion into ℒ(Σ): replace foreign
  constants of type σ by vσ, where G(vσ) = σ and vσ ∉ S.
  Source role: βη equivalence in Bacon–Dorr Definition 3.1(ii.d), p.44,
  with the infinite variable stocks of §1.1 and Figure 2's literal rules.

  Isabelle representation. The support follows the conversion proof,
  not only its endpoints. A β/η step uses the union of its endpoint
  names. Transitivity takes the union of the supports of both proofs.
  No enumeration or finiteness assumption on the constant signature is
  involved. Replacement variables need not be fresh for all terms of Σ.

  Status. This proves signature conservativity of typed named βη chains.
  Fresh variables, not closed Σ-inhabitants, remove foreign constants.
  It does not add a semantic field, α rule, or H theorem.
\<close>

lemma named_retract_from_language:
  assumes language: "named_in_language L \<Xi> G A \<tau>"
    and stock: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>"
  shows "named_in_language L \<Sigma> G (named_retract \<Sigma> v A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>"
    using language unfolding named_in_language_def by (rule conjunct1)
  show ?thesis by (rule named_retract_language[OF typed stock])
qed

definition named_retraction_support where
  "named_retraction_support L \<Sigma> G \<tau> A B S \<longleftrightarrow>
    finite S \<and> (\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> S) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B))"

lemma named_retraction_support_finite:
  "named_retraction_support L \<Sigma> G \<tau> A B S \<Longrightarrow> finite S"
  unfolding named_retraction_support_def by (rule conjunct1)

lemma named_retraction_support_apply:
  assumes support: "named_retraction_support L \<Sigma> G \<tau> A B S"
    and stock: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<And>\<sigma>. v \<sigma> \<notin> S"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  using support stock fresh unfolding named_retraction_support_def by blast

theorem named_conversion_retraction_support:
  assumes conversion: "named_beta_eta_in_language L \<Xi> G \<tau> A B"
  shows "\<exists>S. named_retraction_support L \<Sigma> G \<tau> A B S"
  using conversion
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  show ?case
  proof (rule exI[where x="{}"], unfold named_retraction_support_def, rule conjI)
    show "finite ({} :: nat set)" by simp
  next
    show "\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> {}) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v A)"
    proof (intro allI impI)
      fix v
      assume stock: "\<forall>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<forall>\<sigma>. v \<sigma> \<notin> {}"
      have types: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" using stock by (rule spec)
      show "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v A)"
        by (rule named_beta_eta_in_language.Refl[OF named_retract_from_language[OF Refl.hyps types]])
    qed
  qed
next
  case (Beta A \<tau> B)
  let ?S = "named_vars A \<union> named_vars B"
  show ?case
  proof (rule exI[where x="?S"], unfold named_retraction_support_def, rule conjI)
    show "finite ?S" by (rule finite_UnI; rule named_vars_finite)
  next
    show "\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> ?S) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
    proof (intro allI impI)
      fix v
      assume stock: "\<forall>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<forall>\<sigma>. v \<sigma> \<notin> ?S"
      have types: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" using stock by (rule spec)
      have avoids: "\<And>\<sigma>. v \<sigma> \<notin> ?S" using fresh by (rule spec)
      have step: "named_compatible_step named_beta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
        by (rule named_retract_beta_step[OF Beta.hyps(3) avoids])
      show "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
        by (rule named_beta_eta_in_language.Beta[OF
          named_retract_from_language[OF Beta.hyps(1) types] named_retract_from_language[OF Beta.hyps(2) types] step])
    qed
  qed
next
  case (Eta A \<tau> B)
  let ?S = "named_vars A \<union> named_vars B"
  show ?case
  proof (rule exI[where x="?S"], unfold named_retraction_support_def, rule conjI)
    show "finite ?S" by (rule finite_UnI; rule named_vars_finite)
  next
    show "\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> ?S) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
    proof (intro allI impI)
      fix v
      assume stock: "\<forall>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<forall>\<sigma>. v \<sigma> \<notin> ?S"
      have types: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" using stock by (rule spec)
      have avoids: "\<And>\<sigma>. v \<sigma> \<notin> ?S" using fresh by (rule spec)
      have step: "named_compatible_step named_eta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
        by (rule named_retract_eta_step[OF Eta.hyps(3) avoids])
      show "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
        by (rule named_beta_eta_in_language.Eta[OF
          named_retract_from_language[OF Eta.hyps(1) types] named_retract_from_language[OF Eta.hyps(2) types] step])
    qed
  qed
next
  case (Sym \<tau> A B)
  obtain S where support: "named_retraction_support L \<Sigma> G \<tau> A B S"
    using Sym.IH by (elim exE)
  have finiteS: "finite S" by (rule named_retraction_support_finite[OF support])
  show ?case
  proof (rule exI[where x=S], unfold named_retraction_support_def, rule conjI[OF finiteS])
    show "\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> S) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v B) (named_retract \<Sigma> v A)"
    proof (intro allI impI)
      fix v
      assume stock: "\<forall>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<forall>\<sigma>. v \<sigma> \<notin> S"
      have types: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" using stock by (rule spec)
      have avoids: "\<And>\<sigma>. v \<sigma> \<notin> S" using fresh by (rule spec)
      show "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v B) (named_retract \<Sigma> v A)"
        by (rule named_beta_eta_in_language.Sym[OF named_retraction_support_apply[OF support types avoids]])
    qed
  qed
next
  case (Trans \<tau> A B C)
  obtain S where first: "named_retraction_support L \<Sigma> G \<tau> A B S" using Trans.IH(1) by (elim exE)
  obtain T where second: "named_retraction_support L \<Sigma> G \<tau> B C T" using Trans.IH(2) by (elim exE)
  have finite_union: "finite (S \<union> T)"
    by (rule finite_UnI[OF named_retraction_support_finite[OF first] named_retraction_support_finite[OF second]])
  show ?case
  proof (rule exI[where x="S \<union> T"], unfold named_retraction_support_def, rule conjI[OF finite_union])
    show "\<forall>v. (\<forall>\<sigma>. G (v \<sigma>) = \<sigma>) \<longrightarrow> (\<forall>\<sigma>. v \<sigma> \<notin> S \<union> T) \<longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v C)"
    proof (intro allI impI)
      fix v
      assume stock: "\<forall>\<sigma>. G (v \<sigma>) = \<sigma>" and fresh: "\<forall>\<sigma>. v \<sigma> \<notin> S \<union> T"
      have types: "\<And>\<sigma>. G (v \<sigma>) = \<sigma>" using stock by (rule spec)
      have avoidsS: "\<And>\<sigma>. v \<sigma> \<notin> S" using fresh by blast
      have avoidsT: "\<And>\<sigma>. v \<sigma> \<notin> T" using fresh by blast
      show "named_beta_eta_in_language L \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v C)"
        by (rule named_beta_eta_in_language.Trans[OF
          named_retraction_support_apply[OF first types avoidsS]
          named_retraction_support_apply[OF second types avoidsT]])
    qed
  qed
qed

section \<open>Fresh typed variables remove foreign constants from a conversion\<close>

theorem named_conversion_to_signature:
  assumes rich: "sg_rich G"
    and conversion: "named_beta_eta_in_language L \<Xi> G \<tau> A B"
    and left: "named_in_signature \<Sigma> A" and right: "named_in_signature \<Sigma> B"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
proof -
  obtain S where support: "named_retraction_support L \<Sigma> G \<tau> A B S"
    using named_conversion_retraction_support[where \<Sigma>=\<Sigma>, OF conversion] by (elim exE)
  have finiteS: "finite S" by (rule named_retraction_support_finite[OF support])
  let ?v = "\<lambda>\<sigma>. SOME n. G n = \<sigma> \<and> n \<notin> S"
  have chosen: "G (?v \<sigma>) = \<sigma> \<and> ?v \<sigma> \<notin> S" for \<sigma>
  proof (rule someI_ex)
    show "\<exists>n. G n = \<sigma> \<and> n \<notin> S" by (rule sg_rich_fresh[OF rich finiteS])
  qed
  have types: "\<And>\<sigma>. G (?v \<sigma>) = \<sigma>" by (rule conjunct1[OF chosen])
  have avoids: "\<And>\<sigma>. ?v \<sigma> \<notin> S" by (rule conjunct2[OF chosen])
  have retracted: "named_beta_eta_in_language L \<Sigma> G \<tau>
    (named_retract \<Sigma> ?v A) (named_retract \<Sigma> ?v B)"
    by (rule named_retraction_support_apply[OF support types avoids])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF left] named_retract_fixed[OF right])
qed

corollary named_raw_to_signature:
  assumes rich: "sg_rich G"
    and raw: "named_beta_eta_in_language L (\<lambda>_. UNIV) G \<tau> A B"
    and left: "named_in_language L \<Sigma> G A \<tau>" and right: "named_in_language L \<Sigma> G B \<tau>"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
proof -
  have ls: "named_in_signature \<Sigma> A" using left unfolding named_in_language_def by (rule conjunct2)
  have rs: "named_in_signature \<Sigma> B" using right unfolding named_in_language_def by (rule conjunct2)
  show ?thesis by (rule named_conversion_to_signature[OF rich raw ls rs])
qed

end
