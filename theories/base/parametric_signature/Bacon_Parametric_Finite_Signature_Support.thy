theory Bacon_Parametric_Finite_Signature_Support
  imports Bacon_Parametric_Signature_Transport
begin

section \<open>Every finite derivation uses only finitely many constant names\<close>

text \<open>
  Although Σσ and the premise theory S may be uncountable, a derivation
  Σ; Γ; S ⊢H A has a finite set K of names sufficient for all its steps.
  This is signature support, not just finite support in S.

  Isabelle representation: pH_name_restrict Σ K retains Σσ ∩ K at each
  type.  The induction includes every signature guard and every intermediate
  theorem.  Status: syntactic finite support; no enumeration or model is used.
\<close>

definition pH_name_restrict :: "'c psignature \<Rightarrow> 'c set \<Rightarrow> 'c psignature" where
  "pH_name_restrict \<Sigma> K \<tau> = \<Sigma> \<tau> \<inter> K"

lemma phenkin_names_finite: "finite (phenkin_names A)"
  by (induction A) simp_all

lemma pH_restrict_signature:
  "pterm_in_signature (pH_name_restrict \<Sigma> K) A \<longleftrightarrow>
    pterm_in_signature \<Sigma> A \<and> phenkin_names A \<subseteq> K"
  by (induction A) (auto simp: pH_name_restrict_def)

lemma pH_restrict_mono:
  "K \<subseteq> L \<Longrightarrow> pH_name_restrict \<Sigma> K \<tau> \<subseteq> pH_name_restrict \<Sigma> L \<tau>"
  by (auto simp: pH_name_restrict_def)

theorem pH_proves_finite_signature_support:
  assumes d: "pH_proves \<Sigma> \<Gamma> A"
  shows "\<exists>K. finite K \<and> pH_proves (pH_name_restrict \<Sigma> K) \<Gamma> A"
  using d
proof (induction rule: pH_proves.induct)
  case (PC \<Gamma> A)
  have sig: "pterm_in_signature (pH_name_restrict \<Sigma> (phenkin_names A)) A"
    using PC.hyps(2) by (simp add: pH_restrict_signature)
  have proof_A: "pH_proves (pH_name_restrict \<Sigma> (phenkin_names A)) \<Gamma> A"
    by (rule pH_proves.PC[OF PC.hyps(1) sig])
  show ?case by (rule exI[where x="phenkin_names A"], rule conjI[OF phenkin_names_finite proof_A])
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule exI[where x="{}"], rule conjI) (rule finite.emptyI, rule pH_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  let ?K = "phenkin_names A \<union> phenkin_names T"
  have finite: "finite ?K"
    by (rule finite_UnI[OF phenkin_names_finite[of A] phenkin_names_finite[of T]])
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) A"
    using UI.hyps(3) by (auto simp: pH_restrict_signature)
  have sigT: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) T"
    using UI.hyps(4) by (auto simp: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> ?K) \<Gamma> (PImp (PForall \<sigma> A) (psubst0 T A))"
    by (rule pH_proves.UI[OF UI.hyps(1,2) sigA sigT])
  show ?case by (rule exI[where x="?K"], rule conjI[OF finite result])
next
  case (EG \<sigma> \<Gamma> A T)
  let ?K = "phenkin_names A \<union> phenkin_names T"
  have finite: "finite ?K"
    by (rule finite_UnI[OF phenkin_names_finite[of A] phenkin_names_finite[of T]])
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) A"
    using EG.hyps(3) by (auto simp: pH_restrict_signature)
  have sigT: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) T"
    using EG.hyps(4) by (auto simp: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> ?K) \<Gamma> (PImp (psubst0 T A) (PExists \<sigma> A))"
    by (rule pH_proves.EG[OF EG.hyps(1,2) sigA sigT])
  show ?case by (rule exI[where x="?K"], rule conjI[OF finite result])
next
  case (Ref \<Gamma> M \<sigma>)
  have sig: "pterm_in_signature (pH_name_restrict \<Sigma> (phenkin_names M)) M"
    using Ref.hyps(2) by (simp add: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> (phenkin_names M)) \<Gamma> (PEq \<sigma> M M)"
    by (rule pH_proves.Ref[OF Ref.hyps(1) sig])
  show ?case by (rule exI[where x="phenkin_names M"], rule conjI[OF phenkin_names_finite result])
next
  case (LL \<Gamma> A \<sigma> B F)
  let ?K = "phenkin_names A \<union> phenkin_names B \<union> phenkin_names F"
  have finite: "finite ?K"
    by (rule finite_UnI[OF finite_UnI[OF phenkin_names_finite[of A]
      phenkin_names_finite[of B]] phenkin_names_finite[of F]])
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) A"
    using LL.hyps(4) by (auto simp: pH_restrict_signature)
  have sigB: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) B"
    using LL.hyps(5) by (auto simp: pH_restrict_signature)
  have sigF: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) F"
    using LL.hyps(6) by (auto simp: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> ?K) \<Gamma>
    (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B)))"
    by (rule pH_proves.LL[OF LL.hyps(1,2,3) sigA sigB sigF])
  show ?case by (rule exI[where x="?K"], rule conjI[OF finite result])
next
  case (Beta \<Gamma> A B)
  let ?K = "phenkin_names A \<union> phenkin_names B"
  have finite: "finite ?K"
    by (rule finite_UnI[OF phenkin_names_finite[of A] phenkin_names_finite[of B]])
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) A"
    using Beta.hyps(4) by (auto simp: pH_restrict_signature)
  have sigB: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) B"
    using Beta.hyps(5) by (auto simp: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> ?K) \<Gamma> (PObjIff A B)"
    by (rule pH_proves.Beta[OF Beta.hyps(1,2,3) sigA sigB])
  show ?case by (rule exI[where x="?K"], rule conjI[OF finite result])
next
  case (Eta \<Gamma> A B)
  let ?K = "phenkin_names A \<union> phenkin_names B"
  have finite: "finite ?K"
    by (rule finite_UnI[OF phenkin_names_finite[of A] phenkin_names_finite[of B]])
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) A"
    using Eta.hyps(4) by (auto simp: pH_restrict_signature)
  have sigB: "pterm_in_signature (pH_name_restrict \<Sigma> ?K) B"
    using Eta.hyps(5) by (auto simp: pH_restrict_signature)
  have result: "pH_proves (pH_name_restrict \<Sigma> ?K) \<Gamma> (PObjIff A B)"
    by (rule pH_proves.Eta[OF Eta.hyps(1,2,3) sigA sigB])
  show ?case by (rule exI[where x="?K"], rule conjI[OF finite result])
next
  case (MP \<Gamma> A B)
  obtain K where K: "finite K" and left: "pH_proves (pH_name_restrict \<Sigma> K) \<Gamma> A"
    using MP.IH(1) by (elim exE conjE)
  obtain L where L: "finite L" and right: "pH_proves (pH_name_restrict \<Sigma> L) \<Gamma> (PImp A B)"
    using MP.IH(2) by (elim exE conjE)
  have left': "pH_proves (pH_name_restrict \<Sigma> (K \<union> L)) \<Gamma> A"
    by (rule pH_signature_mono[OF left], rule pH_restrict_mono) auto
  have right': "pH_proves (pH_name_restrict \<Sigma> (K \<union> L)) \<Gamma> (PImp A B)"
    by (rule pH_signature_mono[OF right], rule pH_restrict_mono) auto
  have sigA: "pterm_in_signature (pH_name_restrict \<Sigma> (K \<union> L)) A"
    by (rule pH_proves_in_signature[OF left'])
  have sigB: "pterm_in_signature (pH_name_restrict \<Sigma> (K \<union> L)) B"
    using pH_proves_in_signature[OF right'] by simp
  have result: "pH_proves (pH_name_restrict \<Sigma> (K \<union> L)) \<Gamma> B"
    by (rule pH_proves.MP[OF left' right' sigA sigB])
  show ?case by (rule exI[where x="K \<union> L"], rule conjI) (use K L in simp, rule result)
next
  case (Gen \<Gamma> P \<sigma> Q)
  obtain K where K: "finite K"
    and premise: "pH_proves (pH_name_restrict \<Sigma> K) (\<sigma> # \<Gamma>) (PImp (pshift P) Q)"
    using Gen.IH by (elim exE conjE)
  have sigP: "pterm_in_signature (pH_name_restrict \<Sigma> K) P"
    using pH_proves_in_signature[OF premise] by (simp add: pshift_def)
  have sigQ: "pterm_in_signature (pH_name_restrict \<Sigma> K) Q"
    using pH_proves_in_signature[OF premise] by simp
  have result: "pH_proves (pH_name_restrict \<Sigma> K) \<Gamma> (PImp P (PForall \<sigma> Q))"
    by (rule pH_proves.Gen[OF Gen.hyps(1,2) sigP sigQ premise])
  show ?case by (rule exI[where x=K], rule conjI[OF K result])
next
  case (Inst \<sigma> \<Gamma> P Q)
  obtain K where K: "finite K"
    and premise: "pH_proves (pH_name_restrict \<Sigma> K) (\<sigma> # \<Gamma>) (PImp P (pshift Q))"
    using Inst.IH by (elim exE conjE)
  have sigP: "pterm_in_signature (pH_name_restrict \<Sigma> K) P"
    using pH_proves_in_signature[OF premise] by simp
  have sigQ: "pterm_in_signature (pH_name_restrict \<Sigma> K) Q"
    using pH_proves_in_signature[OF premise] by (simp add: pshift_def)
  have result: "pH_proves (pH_name_restrict \<Sigma> K) \<Gamma> (PImp (PExists \<sigma> P) Q)"
    by (rule pH_proves.Inst[OF Inst.hyps(1,2) sigP sigQ premise])
  show ?case by (rule exI[where x=K], rule conjI[OF K result])
qed

theorem pH_local_finite_signature_support:
  assumes d: "pH_derivable \<Sigma> \<Gamma> L A"
  shows "\<exists>K. finite K \<and> pH_derivable (pH_name_restrict \<Sigma> K) \<Gamma> L A"
  using d
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have sig: "pterm_in_signature (pH_name_restrict \<Sigma> (phenkin_names A)) A"
    using Assumption.hyps(3) by (simp add: pH_restrict_signature)
  have result: "pH_derivable (pH_name_restrict \<Sigma> (phenkin_names A)) \<Gamma> L A"
    by (rule pH_derivable.Assumption[OF Assumption.hyps(1,2) sig])
  show ?case by (rule exI[where x="phenkin_names A"], rule conjI[OF phenkin_names_finite result])
next
  case (Theorem A)
  obtain K where K: "finite K" and theorem_A: "pH_proves (pH_name_restrict \<Sigma> K) \<Gamma> A"
    using pH_proves_finite_signature_support[OF Theorem.hyps] by (elim exE conjE)
  show ?case by (rule exI[where x=K], rule conjI[OF K pH_derivable.Theorem[OF theorem_A]])
next
  case (MP A B)
  obtain K where K: "finite K" and left: "pH_derivable (pH_name_restrict \<Sigma> K) \<Gamma> L A"
    using MP.IH(1) by (elim exE conjE)
  obtain J where J: "finite J" and right: "pH_derivable (pH_name_restrict \<Sigma> J) \<Gamma> L (PImp A B)"
    using MP.IH(2) by (elim exE conjE)
  have left': "pH_derivable (pH_name_restrict \<Sigma> (K \<union> J)) \<Gamma> L A"
    by (rule pH_local_signature_mono[OF left], rule pH_restrict_mono) auto
  have right': "pH_derivable (pH_name_restrict \<Sigma> (K \<union> J)) \<Gamma> L (PImp A B)"
    by (rule pH_local_signature_mono[OF right], rule pH_restrict_mono) auto
  have result: "pH_derivable (pH_name_restrict \<Sigma> (K \<union> J)) \<Gamma> L B"
    by (rule pH_derivable.MP[OF left' right'])
  show ?case by (rule exI[where x="K \<union> J"], rule conjI) (use K J in simp, rule result)
qed

theorem pH_set_finite_signature_support:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
  obtains K where "finite K" and "pH_set_derivable (pH_name_restrict \<Sigma> K) \<Gamma> S A"
proof -
  obtain L where subset: "set L \<subseteq> S" and local_d: "pH_derivable \<Sigma> \<Gamma> L A"
    using d unfolding pH_set_derivable_def by (elim exE conjE)
  obtain K where K: "finite K" and supported: "pH_derivable (pH_name_restrict \<Sigma> K) \<Gamma> L A"
    using pH_local_finite_signature_support[OF local_d] by (elim exE conjE)
  have result: "pH_set_derivable (pH_name_restrict \<Sigma> K) \<Gamma> S A"
    unfolding pH_set_derivable_def by (rule exI[where x=L], rule conjI[OF subset supported])
  show thesis by (rule that[OF K result])
qed

end
