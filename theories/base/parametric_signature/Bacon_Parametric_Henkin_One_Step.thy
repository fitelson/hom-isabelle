theory Bacon_Parametric_Henkin_One_Step
  imports Bacon_Parametric_Deduction
begin

section \<open>One disjoint witness expansion of an arbitrary signature\<close>

text \<open>
  For each closed ∃v:σ.A in ℒ(Σ), add a new cσ,A and the witness axiom
  (∃v:σ.A) → A[cσ,A/v], after embedding every old constant into a disjoint stock.

  Isabelle representation: PHOriginal c retains c; PHWitness σ A indexes a
  new name by its current-language body.  The signature requires A: t in
  context [σ].  No natural-number enumeration or old-language fresh name
  is assumed.

  Status: one witness expansion for closed existential formulas.  Additional
  free parameters are not assigned one uniform constant witness; that would
  require a separate parameterized construction.
\<close>

subsection \<open>Changing the constant-name carrier\<close>

text \<open>
  A map k:Σσ → Δσ induces a translation k(A) of ℒ(Σ) into ℒ(Δ),
  commuting with λv.A, variable renaming, and A[B/v].

  Isabelle representation: phenkin_map changes constants only.  The typing,
  signature, substitution, conversion, and tautology lemmas expose the
  exact commuting equations needed by proof translation.

  Status: forward structural preservation; k need not be injective for these
  lemmas, and they do not establish conservativity.
\<close>

fun phenkin_map :: "('c \<Rightarrow> 'd) \<Rightarrow> 'c pterm \<Rightarrow> 'd pterm" where
  "phenkin_map k (PVar n) = PVar n"
| "phenkin_map k (PConst c \<sigma>) = PConst (k c) \<sigma>"
| "phenkin_map k (PApp M N) = PApp (phenkin_map k M) (phenkin_map k N)"
| "phenkin_map k (PLam \<sigma> M) = PLam \<sigma> (phenkin_map k M)"
| "phenkin_map k (PEq \<sigma> M N) = PEq \<sigma> (phenkin_map k M) (phenkin_map k N)"
| "phenkin_map k (PNeg A) = PNeg (phenkin_map k A)"
| "phenkin_map k (PConj A B) = PConj (phenkin_map k A) (phenkin_map k B)"
| "phenkin_map k (PDisj A B) = PDisj (phenkin_map k A) (phenkin_map k B)"
| "phenkin_map k (PImp A B) = PImp (phenkin_map k A) (phenkin_map k B)"
| "phenkin_map k (PForall \<sigma> A) = PForall \<sigma> (phenkin_map k A)"
| "phenkin_map k (PExists \<sigma> A) = PExists \<sigma> (phenkin_map k A)"

lemma phenkin_map_type:
  assumes "has_ptype \<Gamma> M \<tau>"
  shows "has_ptype \<Gamma> (phenkin_map k M) \<tau>"
  using assms
proof (induction rule: has_ptype.induct)
  case (PVar \<Gamma> n \<tau>)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PVar[OF PVar.hyps])
next
  case (PConst \<Gamma> c \<tau>)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PConst)
next
  case (PApp \<Gamma> M \<sigma> \<tau> N)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PApp[OF PApp.IH])
next
  case (PLam \<sigma> \<Gamma> M \<tau>)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PLam[OF PLam.IH])
next
  case (PEq \<Gamma> M \<sigma> N)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PEq[OF PEq.IH])
next
  case (PNeg \<Gamma> A)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PNeg[OF PNeg.IH])
next
  case (PConj \<Gamma> A B)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PConj[OF PConj.IH])
next
  case (PDisj \<Gamma> A B)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PDisj[OF PDisj.IH])
next
  case (PImp \<Gamma> A B)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PImp[OF PImp.IH])
next
  case (PForall \<sigma> \<Gamma> A)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PForall[OF PForall.IH])
next
  case (PExists \<sigma> \<Gamma> A)
  show ?case by (simp only: phenkin_map.simps) (rule has_ptype.PExists[OF PExists.IH])
qed

lemma phenkin_map_signature:
  assumes "pterm_in_signature \<Sigma> M"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pterm_in_signature \<Delta> (phenkin_map k M)"
  using assms by (induction M) (simp_all add: names)

lemma phenkin_map_prename:
  "phenkin_map k (prename r M) = prename r (phenkin_map k M)"
  by (induction M arbitrary: r) simp_all

lemma phenkin_map_pshift:
  "phenkin_map k (pshift M) = pshift (phenkin_map k M)"
  by (simp only: pshift_def phenkin_map_prename)

lemma phenkin_map_lift:
  "phenkin_map k (plift_subst s n) = plift_subst (\<lambda>j. phenkin_map k (s j)) n"
  by (cases n) (simp_all add: phenkin_map_prename)

lemma phenkin_map_psubst:
  "phenkin_map k (psubst s M) = psubst (\<lambda>n. phenkin_map k (s n)) (phenkin_map k M)"
proof (induction M arbitrary: s)
  case (PLam \<sigma> M)
  have lifts: "(\<lambda>n. phenkin_map k (plift_subst s n)) =
    plift_subst (\<lambda>n. phenkin_map k (s n))"
    by (rule ext) (rule phenkin_map_lift)
  show ?case by (simp only: psubst.simps phenkin_map.simps PLam.IH lifts)
next
  case (PForall \<sigma> M)
  have lifts: "(\<lambda>n. phenkin_map k (plift_subst s n)) =
    plift_subst (\<lambda>n. phenkin_map k (s n))"
    by (rule ext) (rule phenkin_map_lift)
  show ?case by (simp only: psubst.simps phenkin_map.simps PForall.IH lifts)
next
  case (PExists \<sigma> M)
  have lifts: "(\<lambda>n. phenkin_map k (plift_subst s n)) =
    plift_subst (\<lambda>n. phenkin_map k (s n))"
    by (rule ext) (rule phenkin_map_lift)
  show ?case by (simp only: psubst.simps phenkin_map.simps PExists.IH lifts)
qed simp_all

lemma phenkin_map_psubst0:
  "phenkin_map k (psubst0 T A) = psubst0 (phenkin_map k T) (phenkin_map k A)"
proof -
  have case_map: "(\<lambda>n. phenkin_map k (case_nat T PVar n)) = case_nat (phenkin_map k T) PVar"
    by (rule ext) (case_tac n; simp)
  show ?thesis by (simp only: psubst0_def phenkin_map_psubst case_map)
qed

lemma phenkin_map_beta:
  assumes "pbeta_contract M N"
  shows "pbeta_contract (phenkin_map k M) (phenkin_map k N)"
  using assms by cases (simp only: phenkin_map.simps phenkin_map_psubst0; rule pbeta_contract.beta)

lemma phenkin_map_eta:
  assumes "peta_contract M N"
  shows "peta_contract (phenkin_map k M) (phenkin_map k N)"
  using assms by cases (simp only: phenkin_map.simps phenkin_map_pshift; rule peta_contract.eta)

lemma phenkin_map_compatible:
  assumes step: "pcompatible_step R M N"
    and roots: "\<And>A B. R A B \<Longrightarrow> S (phenkin_map k A) (phenkin_map k B)"
  shows "pcompatible_step S (phenkin_map k M) (phenkin_map k N)"
  using step
proof (induction rule: pcompatible_step.induct)
  case (root M N)
  have mapped_root: "S (phenkin_map k M) (phenkin_map k N)"
    by (rule roots[OF root.hyps])
  show ?case
    by (rule pcompatible_step.root[where R=S and M="phenkin_map k M"
          and N="phenkin_map k N", OF mapped_root])
next case (App_left M M' N)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.App_left[OF App_left.IH])
next case (App_right N N' M)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.App_right[OF App_right.IH])
next case (Lam_body M M' \<sigma>)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Lam_body[OF Lam_body.IH])
next case (Eq_left M M' \<sigma> N)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Eq_left[OF Eq_left.IH])
next case (Eq_right N N' \<sigma> M)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Eq_right[OF Eq_right.IH])
next case (Neg_body A A')
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Neg_body[OF Neg_body.IH])
next case (Conj_left A A' B)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Conj_left[OF Conj_left.IH])
next case (Conj_right B B' A)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Conj_right[OF Conj_right.IH])
next case (Disj_left A A' B)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Disj_left[OF Disj_left.IH])
next case (Disj_right B B' A)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Disj_right[OF Disj_right.IH])
next case (Imp_left A A' B)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Imp_left[OF Imp_left.IH])
next case (Imp_right B B' A)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Imp_right[OF Imp_right.IH])
next case (Forall_body A A' \<sigma>)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Forall_body[OF Forall_body.IH])
next case (Exists_body A A' \<sigma>)
  show ?case by (simp only: phenkin_map.simps) (rule pcompatible_step.Exists_body[OF Exists_body.IH])
qed

lemma phenkin_map_prop_eval:
  "pprop_eval v (phenkin_map k A) = pprop_eval (\<lambda>B. v (phenkin_map k B)) A"
  by (induction A) simp_all

lemma phenkin_map_tautology:
  assumes taut: "pprop_tautology \<Gamma> A"
  shows "pprop_tautology \<Gamma> (phenkin_map k A)"
proof -
  note both = taut[unfolded pprop_tautology_def]
  have typed: "has_ptype \<Gamma> A Prop" by (rule conjunct1[OF both])
  have all: "\<forall>v. pprop_eval v A" by (rule conjunct2[OF both])
  show ?thesis unfolding pprop_tautology_def
  proof (rule conjI)
    show "has_ptype \<Gamma> (phenkin_map k A) Prop" by (rule phenkin_map_type[OF typed])
    show "\<forall>v. pprop_eval v (phenkin_map k A)"
    proof (rule allI)
      fix v
      have pulled_evaluation: "pprop_eval (\<lambda>B. v (phenkin_map k B)) A"
        by (rule spec[OF all])
      show "pprop_eval v (phenkin_map k A)"
        by (rule iffD2[OF phenkin_map_prop_eval pulled_evaluation])
    qed
  qed
qed

subsection \<open>Signature-respecting proof preservation\<close>

text \<open>
  Σ; Γ ⊢H A and k(Σσ) ⊆ Δσ imply Δ; Γ ⊢H k(A).

  Isabelle representation: phenkin_map_proves is an induction over all pH_proves
  constructors, retaining the guards on every mapped intermediate term.

  Status: forward proof preservation, not reflection or preservation of
  consistency after adjoining witness axioms.
\<close>

theorem phenkin_map_proves:
  assumes derivation: "pH_proves \<Sigma> \<Gamma> A"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pH_proves \<Delta> \<Gamma> (phenkin_map k A)"
  using derivation
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule pH_proves.PC[OF phenkin_map_tautology[OF PC.hyps(1)]
    phenkin_map_signature[OF PC.hyps(2) names]])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (simp only: phenkin_map.simps) (rule pH_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case by (simp only: phenkin_map.simps phenkin_map_psubst0)
    (rule pH_proves.UI[OF phenkin_map_type[OF UI.hyps(1)] phenkin_map_type[OF UI.hyps(2)]
      phenkin_map_signature[OF UI.hyps(3) names] phenkin_map_signature[OF UI.hyps(4) names]])
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case by (simp only: phenkin_map.simps phenkin_map_psubst0)
    (rule pH_proves.EG[OF phenkin_map_type[OF EG.hyps(1)] phenkin_map_type[OF EG.hyps(2)]
      phenkin_map_signature[OF EG.hyps(3) names] phenkin_map_signature[OF EG.hyps(4) names]])
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.Ref[OF phenkin_map_type[OF Ref.hyps(1)] phenkin_map_signature[OF Ref.hyps(2) names]])
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.LL[OF phenkin_map_type[OF LL.hyps(1)] phenkin_map_type[OF LL.hyps(2)]
      phenkin_map_type[OF LL.hyps(3)] phenkin_map_signature[OF LL.hyps(4) names]
      phenkin_map_signature[OF LL.hyps(5) names] phenkin_map_signature[OF LL.hyps(6) names]])
next
  case (Beta \<Gamma> A B)
  have step: "pcompatible_step pbeta_contract (phenkin_map k A) (phenkin_map k B)"
    by (rule phenkin_map_compatible[OF Beta.hyps(3)]) (rule phenkin_map_beta)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.Beta[OF phenkin_map_type[OF Beta.hyps(1)] phenkin_map_type[OF Beta.hyps(2)]
      step phenkin_map_signature[OF Beta.hyps(4) names] phenkin_map_signature[OF Beta.hyps(5) names]])
next
  case (Eta \<Gamma> A B)
  have step: "pcompatible_step peta_contract (phenkin_map k A) (phenkin_map k B)"
    by (rule phenkin_map_compatible[OF Eta.hyps(3)]) (rule phenkin_map_eta)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.Eta[OF phenkin_map_type[OF Eta.hyps(1)] phenkin_map_type[OF Eta.hyps(2)]
      step phenkin_map_signature[OF Eta.hyps(4) names] phenkin_map_signature[OF Eta.hyps(5) names]])
next
  case (MP \<Gamma> A B)
  have implication: "pH_proves \<Delta> \<Gamma> (PImp (phenkin_map k A) (phenkin_map k B))"
    using MP.IH(2) by (simp only: phenkin_map.simps)
  show ?case by (rule pH_proves.MP[OF MP.IH(1) implication
    phenkin_map_signature[OF MP.hyps(3) names] phenkin_map_signature[OF MP.hyps(4) names]])
next
  case (Gen \<Gamma> P \<sigma> Q)
  have premise: "pH_proves \<Delta> (\<sigma> # \<Gamma>) (PImp (pshift (phenkin_map k P)) (phenkin_map k Q))"
    using Gen.IH by (simp only: phenkin_map.simps phenkin_map_pshift)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.Gen[OF phenkin_map_type[OF Gen.hyps(1)] phenkin_map_type[OF Gen.hyps(2)]
      phenkin_map_signature[OF Gen.hyps(3) names] phenkin_map_signature[OF Gen.hyps(4) names] premise])
next
  case (Inst \<sigma> \<Gamma> P Q)
  have premise: "pH_proves \<Delta> (\<sigma> # \<Gamma>) (PImp (phenkin_map k P) (pshift (phenkin_map k Q)))"
    using Inst.IH by (simp only: phenkin_map.simps phenkin_map_pshift)
  show ?case by (simp only: phenkin_map.simps)
    (rule pH_proves.Inst[OF phenkin_map_type[OF Inst.hyps(1)] phenkin_map_type[OF Inst.hyps(2)]
      phenkin_map_signature[OF Inst.hyps(3) names] phenkin_map_signature[OF Inst.hyps(4) names] premise])
qed

subsection \<open>Disjoint old names and typed existential witnesses\<close>

text \<open>
  Σ⁺ contains distinct old names ι(c) and witnesses cσ,A for each
  closed ∃v:σ.A of ℒ(Σ).

  Isabelle representation: phenkin_name uses disjoint PHOriginal/PHWitness
  constructors.  phenkin_signature checks the body’s type and old-signature
  membership; phenkin_embed has a proved projection inverse on old terms.

  Status: injective old-language embedding and genuinely fresh witness
  labels, without a cardinality or same-language freshness premise.
\<close>

datatype 'c phenkin_name = PHOriginal 'c | PHWitness otype "'c pterm"

definition phenkin_embed :: "'c pterm \<Rightarrow> 'c phenkin_name pterm" where
  "phenkin_embed A = phenkin_map PHOriginal A"

definition phenkin_signature :: "'c psignature \<Rightarrow> 'c phenkin_name psignature" where
  "phenkin_signature \<Sigma> \<tau> = {n. case n of
      PHOriginal c \<Rightarrow> c \<in> \<Sigma> \<tau>
    | PHWitness \<sigma> A \<Rightarrow>
        \<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and> pterm_in_signature \<Sigma> A}"

lemma phenkin_old_name[simp]:
  "PHOriginal c \<in> phenkin_signature \<Sigma> \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
  by (simp add: phenkin_signature_def)

lemma phenkin_witness_name[simp]:
  "PHWitness \<sigma> A \<in> phenkin_signature \<Sigma> \<tau> \<longleftrightarrow>
    \<sigma> = \<tau> \<and> has_ptype [\<sigma>] A Prop \<and> pterm_in_signature \<Sigma> A"
  by (simp add: phenkin_signature_def)

lemma phenkin_embed_signature:
  "pterm_in_signature (phenkin_signature \<Sigma>) (phenkin_embed A) =
    pterm_in_signature \<Sigma> A"
  unfolding phenkin_embed_def by (induction A) simp_all

lemma phenkin_embed_type:
  "has_ptype \<Gamma> A \<tau> \<Longrightarrow> has_ptype \<Gamma> (phenkin_embed A) \<tau>"
  unfolding phenkin_embed_def by (rule phenkin_map_type)

lemma phenkin_embed_language:
  "pterm_in_language \<Sigma> \<Gamma> A \<tau> \<Longrightarrow>
    pterm_in_language (phenkin_signature \<Sigma>) \<Gamma> (phenkin_embed A) \<tau>"
  unfolding pterm_in_language_def
  by (elim conjE) (rule conjI, rule phenkin_embed_type, assumption, simp only: phenkin_embed_signature)

lemma phenkin_embed_proves:
  "pH_proves \<Sigma> \<Gamma> A \<Longrightarrow>
    pH_proves (phenkin_signature \<Sigma>) \<Gamma> (phenkin_embed A)"
  unfolding phenkin_embed_def
  by (rule phenkin_map_proves) (assumption, simp)

fun phenkin_project :: "'c \<Rightarrow> 'c phenkin_name \<Rightarrow> 'c" where
  "phenkin_project d (PHOriginal c) = c"
| "phenkin_project d (PHWitness \<sigma> A) = d"

lemma phenkin_embed_left_inverse:
  "phenkin_map (phenkin_project d) (phenkin_embed A) = A"
  unfolding phenkin_embed_def by (induction A) simp_all

lemma phenkin_embed_injective:
  fixes d :: 'c
  assumes eq: "phenkin_embed (A :: 'c pterm) = phenkin_embed B"
  shows "A = B"
proof -
  have mapped: "phenkin_map (phenkin_project d) (phenkin_embed A) =
    phenkin_map (phenkin_project d) (phenkin_embed B)"
    by (rule arg_cong[where f="phenkin_map (phenkin_project d)", OF eq])
  show ?thesis using mapped by (simp only: phenkin_embed_left_inverse)
qed

fun phenkin_names :: "'c pterm \<Rightarrow> 'c set" where
  "phenkin_names (PVar n) = {}"
| "phenkin_names (PConst c \<sigma>) = {c}"
| "phenkin_names (PApp M N) = phenkin_names M \<union> phenkin_names N"
| "phenkin_names (PLam \<sigma> M) = phenkin_names M"
| "phenkin_names (PEq \<sigma> M N) = phenkin_names M \<union> phenkin_names N"
| "phenkin_names (PNeg A) = phenkin_names A"
| "phenkin_names (PConj A B) = phenkin_names A \<union> phenkin_names B"
| "phenkin_names (PDisj A B) = phenkin_names A \<union> phenkin_names B"
| "phenkin_names (PImp A B) = phenkin_names A \<union> phenkin_names B"
| "phenkin_names (PForall \<sigma> A) = phenkin_names A"
| "phenkin_names (PExists \<sigma> A) = phenkin_names A"

lemma phenkin_witness_fresh:
  "PHWitness \<sigma> A \<notin> phenkin_names (phenkin_embed B)"
  unfolding phenkin_embed_def by (induction B) simp_all

text \<open>
  The witness condition is (∃v:σ.A) → A[cσ,A/v].

  Isabelle representation: phenkin_witness is the typed new constant;
  phenkin_witness_axiom builds the condition after embedding A.  The final
  lemma verifies that this formula belongs to the expanded language.

  Status: witness axioms are well-formed formulas, not asserted pH_proves
  conclusions and not yet a consistency-preserving theory extension.
\<close>

definition phenkin_witness :: "otype \<Rightarrow> 'c pterm \<Rightarrow> 'c phenkin_name pterm" where
  "phenkin_witness \<sigma> A = PConst (PHWitness \<sigma> A) \<sigma>"

definition phenkin_witness_axiom :: "otype \<Rightarrow> 'c pterm \<Rightarrow> 'c phenkin_name pterm" where
  "phenkin_witness_axiom \<sigma> A =
    PImp (PExists \<sigma> (phenkin_embed A)) (psubst0 (phenkin_witness \<sigma> A) (phenkin_embed A))"

lemma phenkin_witness_type:
  "has_ptype \<Gamma> (phenkin_witness \<sigma> A) \<sigma>"
  unfolding phenkin_witness_def by (rule has_ptype.PConst)

lemma phenkin_witness_signature:
  assumes "has_ptype [\<sigma>] A Prop" and "pterm_in_signature \<Sigma> A"
  shows "pterm_in_signature (phenkin_signature \<Sigma>) (phenkin_witness \<sigma> A)"
  using assms by (simp add: phenkin_witness_def)

lemma phenkin_witness_axiom_language:
  assumes body: "has_ptype [\<sigma>] A Prop" and sig: "pterm_in_signature \<Sigma> A"
  shows "pterm_in_language (phenkin_signature \<Sigma>) [] (phenkin_witness_axiom \<sigma> A) Prop"
proof -
  have embedded_type: "has_ptype [\<sigma>] (phenkin_embed A) Prop" by (rule phenkin_embed_type[OF body])
  have embedded_sig: "pterm_in_signature (phenkin_signature \<Sigma>) (phenkin_embed A)"
    using sig by (simp only: phenkin_embed_signature)
  have witness_sig: "pterm_in_signature (phenkin_signature \<Sigma>) (phenkin_witness \<sigma> A)"
    by (rule phenkin_witness_signature[OF body sig])
  have instance_type: "has_ptype [] (psubst0 (phenkin_witness \<sigma> A) (phenkin_embed A)) Prop"
    by (rule psubst0_preserves_typing[OF embedded_type phenkin_witness_type])
  have typed: "has_ptype [] (phenkin_witness_axiom \<sigma> A) Prop"
    unfolding phenkin_witness_axiom_def
    by (rule has_ptype.PImp[OF has_ptype.PExists[OF embedded_type] instance_type])
  have instance_sig: "pterm_in_signature (phenkin_signature \<Sigma>)
    (psubst0 (phenkin_witness \<sigma> A) (phenkin_embed A))"
    by (rule psubst0_signature[OF embedded_sig witness_sig])
  have guarded: "pterm_in_signature (phenkin_signature \<Sigma>) (phenkin_witness_axiom \<sigma> A)"
    using embedded_sig instance_sig by (simp only: phenkin_witness_axiom_def pterm_in_signature.simps)
  show ?thesis unfolding pterm_in_language_def by (rule conjI[OF typed guarded])
qed

text \<open>
  The formulas (∃v:σ.A) → A[cσ,A/v] are available in ℒ(Σ⁺), but their
  availability does not imply ⊢H ((∃v:σ.A) → A[cσ,A/v]).

  Isabelle representation: phenkin_witness_axiom defines these formulas;
  typing/signature membership and witness freshness are proved.  The
  projection inverse is asserted only for embedded old terms.

  Status: no consistency theorem for adjoining witness axioms yet.  It needs
  fresh-constant elimination and derivability-from-assumptions lemmas;
  forward proof preservation is insufficient.  New formulas in ℒ(Σ⁺)
  require further witnesses, so Henkin closure needs coherent iteration
  or a direct limit and its consistency proof, not one expansion.
\<close>

end
