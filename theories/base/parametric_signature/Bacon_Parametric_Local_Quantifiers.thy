theory Bacon_Parametric_Local_Quantifiers
  imports Bacon_Parametric_Fresh_Constant
begin

section \<open>Quantifier rules through shifted local assumptions\<close>

text \<open>
  If every premise in S is independent of v, local Gen and Inst have the
  forms S ⊢H P → Q(v) ⇒ S ⊢H P → ∀v.Q(v), and
  S ⊢H P(v) → Q ⇒ S ⊢H (∃v.P(v)) → Q, with v ∉ FV(P) or v ∉ FV(Q),
  respectively.  The finite-support proof discharges premises before
  applying the theorem-level rule.

  Isabelle representation: old premises become map pshift Δ or image pshift S
  in σ # Γ.  Language hypotheses include both typing and the exact signature.
  Implication chains package the finite premises; no quantifier rule is added
  to the local derivability relation.

  Status: local/set rule admissibility and the eigen-witness deduction link.
  Fresh-constant proof preservation and fresh-witness consistency are not
  conclusions of this file.
\<close>

fun pH_qchain :: "'c pterm list \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "pH_qchain [] A = A"
| "pH_qchain (P # \<Delta>) A = PImp P (pH_qchain \<Delta> A)"

fun pH_qconj :: "'c pterm list \<Rightarrow> 'c pterm \<Rightarrow> 'c pterm" where
  "pH_qconj [] A = A"
| "pH_qconj (P # \<Delta>) A = PConj P (pH_qconj \<Delta> A)"

lemma pH_qchain_language:
  "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>) \<Longrightarrow> pterm_in_language \<Sigma> \<Gamma> A Prop \<Longrightarrow>
    pterm_in_language \<Sigma> \<Gamma> (pH_qchain \<Delta> A) Prop"
  by (induction \<Delta>) (auto simp: pH_typed_theory_def pterm_in_language_def intro: has_ptype.intros)

lemma pH_qconj_language:
  "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>) \<Longrightarrow> pterm_in_language \<Sigma> \<Gamma> A Prop \<Longrightarrow>
    pterm_in_language \<Sigma> \<Gamma> (pH_qconj \<Delta> A) Prop"
  by (induction \<Delta>) (auto simp: pH_typed_theory_def pterm_in_language_def intro: has_ptype.intros)

lemma pH_qshift_language:
  "pterm_in_language \<Sigma> \<Gamma> A Prop \<Longrightarrow>
    pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (pshift A) Prop"
  by (auto simp: pterm_in_language_def pshift_def intro: prename_preserves_typing)

lemma pH_qshift_list_language:
  "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>) \<Longrightarrow>
    pH_typed_theory \<Sigma> (\<sigma> # \<Gamma>) (set (map pshift \<Delta>))"
  by (auto simp: pH_typed_theory_def pshift_def intro: prename_preserves_typing)

lemma pH_qchain_pull_eval:
  "pprop_eval v (pH_qchain \<Delta> (PImp P Q)) = pprop_eval v (PImp P (pH_qchain \<Delta> Q))"
  by (induction \<Delta>) auto

lemma pH_qchain_factor_eval:
  "pprop_eval v (pH_qchain \<Delta> (PImp P Q)) = pprop_eval v (PImp (pH_qconj \<Delta> P) Q)"
  by (induction \<Delta>) auto

lemma pH_qchain_shift:
  "pshift (pH_qchain \<Delta> A) = pH_qchain (map pshift \<Delta>) (pshift A)"
  by (induction \<Delta>) (simp_all add: pshift_def)

lemma pH_qconj_shift:
  "pshift (pH_qconj \<Delta> A) = pH_qconj (map pshift \<Delta>) (pshift A)"
  by (induction \<Delta>) (simp_all add: pshift_def)

lemma pH_qshift_false: "pshift PObjFalse = PObjFalse"
  by (simp add: pshift_def PObjFalse_def PObjTrue_def)

lemma pH_qPC_transport:
  assumes d: "pH_proves \<Sigma> \<Gamma> A" and B: "pterm_in_language \<Sigma> \<Gamma> B Prop"
    and equivalent: "\<And>v. pprop_eval v A = pprop_eval v B"
  shows "pH_proves \<Sigma> \<Gamma> B"
proof -
  have A_type: "has_ptype \<Gamma> A Prop" by (rule pH_proves_formula[OF d])
  have A_sig: "pterm_in_signature \<Sigma> A" by (rule pH_proves_in_signature[OF d])
  note B_parts = B[unfolded pterm_in_language_def]
  have B_type: "has_ptype \<Gamma> B Prop" by (rule conjunct1[OF B_parts])
  have B_sig: "pterm_in_signature \<Sigma> B" by (rule conjunct2[OF B_parts])
  have taut: "pprop_tautology \<Gamma> (PImp A B)"
    unfolding pprop_tautology_def
    by (rule conjI[OF has_ptype.PImp[OF A_type B_type]]) (simp add: equivalent)
  have sig: "pterm_in_signature \<Sigma> (PImp A B)" using A_sig B_sig by simp
  show ?thesis by (rule pH_proves.MP[OF d pH_proves.PC[OF taut sig] A_sig B_sig])
qed

lemma pH_local_empty_to_theorem:
  assumes d: "pH_derivable \<Sigma> \<Gamma> [] A"
  shows "pH_proves \<Sigma> \<Gamma> A"
  using d
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  then show ?case by simp
next
  case (Theorem A)
  show ?case by (rule Theorem.hyps)
next
  case (MP A B)
  have sigB: "pterm_in_signature \<Sigma> B"
    using pH_proves_in_signature[OF MP.IH(2)] by simp
  show ?case by (rule pH_proves.MP[OF MP.IH(1,2) pH_proves_in_signature[OF MP.IH(1)] sigB])
qed

lemma pH_local_to_qchain:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and d: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
  shows "pH_proves \<Sigma> \<Gamma> (pH_qchain \<Delta> A)"
  using premise_facts d
proof (induction \<Delta> arbitrary: A)
  case Nil
  show ?case using pH_local_empty_to_theorem[OF Nil.prems(2)] by simp
next
  case (Cons P \<Delta>)
  have P_type: "has_ptype \<Gamma> P Prop" and P_sig: "pterm_in_signature \<Sigma> P"
    and tail: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    using Cons.prems(1) unfolding pH_typed_theory_def by auto
  have discharged: "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp P A)"
    by (rule pH_derivable_deduction[OF P_type P_sig Cons.prems(2)])
  have encoded: "pH_proves \<Sigma> \<Gamma> (pH_qchain \<Delta> (PImp P A))"
    by (rule Cons.IH[OF tail discharged])
  have A_lang: "pterm_in_language \<Sigma> \<Gamma> A Prop"
    unfolding pterm_in_language_def
    by (rule conjI[OF pH_derivable_formula[OF Cons.prems(2)]
      pH_derivable_in_signature[OF Cons.prems(2)]])
  have target: "pterm_in_language \<Sigma> \<Gamma> (pH_qchain (P # \<Delta>) A) Prop"
    by (rule pH_qchain_language[OF Cons.prems(1) A_lang])
  show ?case by (rule pH_qPC_transport[OF encoded target]) (simp only: pH_qchain.simps pH_qchain_pull_eval)
qed

lemma pH_qchain_elim:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)" and subset: "set \<Delta> \<subseteq> set \<Pi>"
    and d: "pH_derivable \<Sigma> \<Gamma> \<Pi> (pH_qchain \<Delta> A)"
  shows "pH_derivable \<Sigma> \<Gamma> \<Pi> A"
  using premise_facts subset d
proof (induction \<Delta>)
  case Nil
  show ?case using Nil.prems(3) by simp
next
  case (Cons P \<Delta>)
  have P_type: "has_ptype \<Gamma> P Prop" and P_sig: "pterm_in_signature \<Sigma> P"
    and tail: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    using Cons.prems(1) unfolding pH_typed_theory_def by auto
  have member: "P \<in> set \<Pi>" and subset': "set \<Delta> \<subseteq> set \<Pi>" using Cons.prems(2) by auto
  have local_P: "pH_derivable \<Sigma> \<Gamma> \<Pi> P"
    by (rule pH_derivable.Assumption[OF member P_type P_sig])
  have implication: "pH_derivable \<Sigma> \<Gamma> \<Pi> (PImp P (pH_qchain \<Delta> A))"
    using Cons.prems(3) by simp
  show ?case by (rule Cons.IH[OF tail subset' pH_derivable.MP[OF local_P implication]])
qed

lemma pH_qchain_to_local:
  "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>) \<Longrightarrow> pH_proves \<Sigma> \<Gamma> (pH_qchain \<Delta> A) \<Longrightarrow>
    pH_derivable \<Sigma> \<Gamma> \<Delta> A"
  by (rule pH_qchain_elim) (assumption, rule subset_refl, rule pH_derivable.Theorem, assumption)

subsection \<open>Theorem rules after finite premise_facts have been discharged\<close>

lemma pH_qchain_Gen:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and P: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    and Q: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
    and d: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pH_qchain (map pshift \<Delta>) (PImp (pshift P) Q))"
  shows "pH_proves \<Sigma> \<Gamma> (pH_qchain \<Delta> (PImp P (PForall \<sigma> Q)))"
proof -
  let ?X = "pH_qconj \<Delta> P"
  have X: "pterm_in_language \<Sigma> \<Gamma> ?X Prop" by (rule pH_qconj_language[OF premise_facts P])
  have shifted_X: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (pshift ?X) Prop"
    by (rule pH_qshift_language[OF X])
  have premise_lang: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (PImp (pshift ?X) Q) Prop"
    using shifted_X Q by (auto simp: pterm_in_language_def)
  have factored: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp (pshift ?X) Q)"
    by (rule pH_qPC_transport[OF d premise_lang])
      (simp only: pH_qchain_factor_eval pH_qconj_shift)
  note X_parts = X[unfolded pterm_in_language_def]
  have XT: "has_ptype \<Gamma> ?X Prop" by (rule conjunct1[OF X_parts])
  have XS: "pterm_in_signature \<Sigma> ?X" by (rule conjunct2[OF X_parts])
  note Q_parts = Q[unfolded pterm_in_language_def]
  have QT: "has_ptype (\<sigma> # \<Gamma>) Q Prop" by (rule conjunct1[OF Q_parts])
  have QS: "pterm_in_signature \<Sigma> Q" by (rule conjunct2[OF Q_parts])
  have generalized: "pH_proves \<Sigma> \<Gamma> (PImp ?X (PForall \<sigma> Q))"
    by (rule pH_proves.Gen[OF XT QT XS QS factored])
  have end_lang: "pterm_in_language \<Sigma> \<Gamma> (PImp P (PForall \<sigma> Q)) Prop"
    using P Q by (auto simp: pterm_in_language_def)
  show ?thesis by (rule pH_qPC_transport[OF generalized pH_qchain_language[OF premise_facts end_lang]])
    (simp only: pH_qchain_factor_eval)
qed

lemma pH_qchain_Inst:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and P: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    and Q: "pterm_in_language \<Sigma> \<Gamma> Q Prop"
    and d: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pH_qchain (map pshift \<Delta>) (PImp P (pshift Q)))"
  shows "pH_proves \<Sigma> \<Gamma> (pH_qchain \<Delta> (PImp (PExists \<sigma> P) Q))"
proof -
  let ?X = "pH_qchain \<Delta> Q"
  have X: "pterm_in_language \<Sigma> \<Gamma> ?X Prop" by (rule pH_qchain_language[OF premise_facts Q])
  have shifted_X: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (pshift ?X) Prop"
    by (rule pH_qshift_language[OF X])
  have premise_lang: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (PImp P (pshift ?X)) Prop"
    using P shifted_X by (auto simp: pterm_in_language_def)
  have pulled: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (PImp P (pshift ?X))"
    by (rule pH_qPC_transport[OF d premise_lang])
      (simp only: pH_qchain_pull_eval pH_qchain_shift)
  note X_parts = X[unfolded pterm_in_language_def]
  have XT: "has_ptype \<Gamma> ?X Prop" by (rule conjunct1[OF X_parts])
  have XS: "pterm_in_signature \<Sigma> ?X" by (rule conjunct2[OF X_parts])
  note P_parts = P[unfolded pterm_in_language_def]
  have PT: "has_ptype (\<sigma> # \<Gamma>) P Prop" by (rule conjunct1[OF P_parts])
  have PS: "pterm_in_signature \<Sigma> P" by (rule conjunct2[OF P_parts])
  have instantiated: "pH_proves \<Sigma> \<Gamma> (PImp (PExists \<sigma> P) ?X)"
    by (rule pH_proves.Inst[OF PT XT PS XS pulled])
  have end_lang: "pterm_in_language \<Sigma> \<Gamma> (PImp (PExists \<sigma> P) Q) Prop"
    using P Q by (auto simp: pterm_in_language_def)
  show ?thesis by (rule pH_qPC_transport[OF instantiated pH_qchain_language[OF premise_facts end_lang]])
    (simp only: pH_qchain_pull_eval)
qed

lemma pH_local_Gen:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and P: "pterm_in_language \<Sigma> \<Gamma> P Prop"
    and Q: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
    and d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift \<Delta>) (PImp (pshift P) Q)"
  shows "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp P (PForall \<sigma> Q))"
proof -
  have shifted: "pH_typed_theory \<Sigma> (\<sigma> # \<Gamma>) (set (map pshift \<Delta>))"
    by (rule pH_qshift_list_language[OF premise_facts])
  have encoded: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pH_qchain (map pshift \<Delta>) (PImp (pshift P) Q))"
    by (rule pH_local_to_qchain[OF shifted d])
  show ?thesis by (rule pH_qchain_to_local[OF premise_facts pH_qchain_Gen[OF premise_facts P Q encoded]])
qed

lemma pH_local_Inst:
  assumes premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and P: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    and Q: "pterm_in_language \<Sigma> \<Gamma> Q Prop"
    and d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift \<Delta>) (PImp P (pshift Q))"
  shows "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp (PExists \<sigma> P) Q)"
proof -
  have shifted: "pH_typed_theory \<Sigma> (\<sigma> # \<Gamma>) (set (map pshift \<Delta>))"
    by (rule pH_qshift_list_language[OF premise_facts])
  have encoded: "pH_proves \<Sigma> (\<sigma> # \<Gamma>) (pH_qchain (map pshift \<Delta>) (PImp P (pshift Q)))"
    by (rule pH_local_to_qchain[OF shifted d])
  show ?thesis by (rule pH_qchain_to_local[OF premise_facts pH_qchain_Inst[OF premise_facts P Q encoded]])
qed

subsection \<open>Arbitrary sets retain finite shifted support\<close>

lemma pH_shifted_set_rule:
  assumes typed: "pH_typed_theory \<Sigma> \<Gamma> S"
    and d: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) A"
    and local_rule: "\<And>\<Delta>. pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>) \<Longrightarrow>
      pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift \<Delta>) A \<Longrightarrow> pH_derivable \<Sigma> \<Gamma> \<Delta> B"
  shows "pH_set_derivable \<Sigma> \<Gamma> S B"
proof -
  obtain \<Pi> where support: "set \<Pi> \<subseteq> image pshift S"
    and local_d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) \<Pi> A"
    using d unfolding pH_set_derivable_def by (elim exE conjE)
  let ?u = "psubst0 (PVar 0)"
  let ?D = "map ?u \<Pi>"
  have restore: "pshift (?u C) = C" if member: "C \<in> set \<Pi>" for C
  proof -
    have image: "C \<in> image pshift S" by (rule subsetD[OF support member])
    from image obtain E where eq: "C = pshift E" and E: "E \<in> S" by (elim imageE)
    show ?thesis by (simp only: eq psubst0_pshift)
  qed
  have subset: "set ?D \<subseteq> S"
  proof (rule subsetI)
    fix C assume member: "C \<in> set ?D"
    obtain E where E: "E \<in> set \<Pi>" and C: "C = ?u E" using member by (auto simp: set_map)
    have image: "E \<in> image pshift S" by (rule subsetD[OF support E])
    from image obtain F where eq: "E = pshift F" and F: "F \<in> S" by (elim imageE)
    show "C \<in> S" using F by (simp only: C eq psubst0_pshift)
  qed
  have mapped: "map pshift ?D = \<Pi>" by (simp only: map_map comp_def) (rule map_idI, rule restore)
  have premise_facts: "pH_typed_theory \<Sigma> \<Gamma> (set ?D)"
  proof (unfold pH_typed_theory_def, intro ballI)
    fix C
    assume member: "C \<in> set ?D"
    have in_S: "C \<in> S" by (rule subsetD[OF subset member])
    show "has_ptype \<Gamma> C Prop \<and> pterm_in_signature \<Sigma> C"
      by (rule bspec[OF typed[unfolded pH_typed_theory_def] in_S])
  qed
  have shifted_d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift ?D) A"
    using local_d by (simp only: mapped)
  have result: "pH_derivable \<Sigma> \<Gamma> ?D B" by (rule local_rule[OF premise_facts shifted_d])
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x="?D"], rule conjI[OF subset result])
qed

lemma pH_set_Gen:
  assumes "pH_typed_theory \<Sigma> \<Gamma> S" and "pterm_in_language \<Sigma> \<Gamma> P Prop"
    and "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) Q Prop"
    and "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (PImp (pshift P) Q)"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (PImp P (PForall \<sigma> Q))"
proof (rule pH_shifted_set_rule[OF assms(1,4)])
  fix \<Delta>
  assume typed: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and local_d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift \<Delta>) (PImp (pshift P) Q)"
  show "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp P (PForall \<sigma> Q))"
    by (rule pH_local_Gen[OF typed assms(2,3) local_d])
qed

lemma pH_set_Inst:
  assumes "pH_typed_theory \<Sigma> \<Gamma> S" and "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) P Prop"
    and "pterm_in_language \<Sigma> \<Gamma> Q Prop"
    and "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (PImp P (pshift Q))"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PExists \<sigma> P) Q)"
proof (rule pH_shifted_set_rule[OF assms(1,4)])
  fix \<Delta>
  assume typed: "pH_typed_theory \<Sigma> \<Gamma> (set \<Delta>)"
    and local_d: "pH_derivable \<Sigma> (\<sigma> # \<Gamma>) (map pshift \<Delta>) (PImp P (pshift Q))"
  show "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp (PExists \<sigma> P) Q)"
    by (rule pH_local_Inst[OF typed assms(2,3) local_d])
qed

subsection \<open>Descending the eigen-witness deduction\<close>

lemma pH_eigen_witness_descend:
  assumes S: "pH_typed_theory \<Sigma> \<Gamma> S"
    and body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sig: "pterm_in_signature \<Sigma> A"
    and d: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>)
      (insert (PImp (pshift (PExists \<sigma> A)) A) (image pshift S)) PObjFalse"
  shows "pH_set_derivable \<Sigma> \<Gamma> S
    (PImp (PExists \<sigma> (PImp (pshift (PExists \<sigma> A)) A)) PObjFalse)"
proof -
  let ?W = "PImp (pshift (PExists \<sigma> A)) A"
  have W: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) ?W Prop"
    using body sig pshift_preserves_typing[OF has_ptype.PExists[OF body]]
    by (auto simp: pterm_in_language_def pshift_def)
  have false_lang: "pterm_in_language \<Sigma> \<Gamma> PObjFalse Prop"
    unfolding pterm_in_language_def PObjFalse_def PObjTrue_def
    by (intro conjI has_ptype.PNeg has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all
  have discharged: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (PImp ?W PObjFalse)"
    by (rule pH_eigen_witness_deduction[OF body sig d])
  have premise: "pH_set_derivable \<Sigma> (\<sigma> # \<Gamma>) (image pshift S) (PImp ?W (pshift PObjFalse))"
    using discharged by (simp only: pH_qshift_false)
  show ?thesis by (rule pH_set_Inst[OF S W false_lang premise])
qed

text \<open>
  The descended conclusion still has ∃v:σ.((∃u:σ.A(u)) → A(v)) as antecedent.
  Proving that existential theorem and preserving proofs when abstracting
  the fresh witness are separate obligations before consistency follows.
\<close>

end
