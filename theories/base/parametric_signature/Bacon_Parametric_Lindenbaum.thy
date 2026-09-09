theory Bacon_Parametric_Lindenbaum
  imports Bacon_Parametric_Local_Derivability "HOL.Zorn"
begin

section \<open>Lindenbaum extension without enumerating the language\<close>

text \<open>
  Conₕ(S) ⇒ ∃T ⊇ S, T is typed, consistent, deductively closed, and
  ∀A ∈ L(Σ), A ∈ T or ¬A ∈ T.
  Source role: Bacon, Exercise 15.3 and Theorem 15.3, pp. 319–321;
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64.

  Isabelle representation: Zorn's lemma replaces formula enumeration.
  A proof from the union of a nonempty chain has finite support, contained
  in one chain member.  This gives an upper bound among typed consistent
  extensions.  Maximality then yields deductive closure and a decision
  between every formula and its negation.

  Status: arbitrary constant-name carriers and arbitrary starting sets.
  No countability, signature expansion, or existential witnesses are added.
  The separate Henkin-extension construction is still required.
\<close>

lemma pH_lindenbaum_false_type:
  "has_ptype \<Gamma> PObjFalse Prop"
  unfolding PObjFalse_def PObjTrue_def
  by (intro has_ptype.PNeg has_ptype.PForall has_ptype.PImp has_ptype.PVar) simp_all

lemma pH_lindenbaum_false_signature:
  "pterm_in_signature \<Sigma> PObjFalse"
  by (simp add: PObjFalse_def PObjTrue_def)

lemma pH_consistent_insert_derivable:
  assumes con: "pH_consistent \<Sigma> \<Gamma> S"
    and d: "pH_set_derivable \<Sigma> \<Gamma> S A"
  shows "pH_consistent \<Sigma> \<Gamma> (insert A S)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable \<Sigma> \<Gamma> (insert A S) PObjFalse"
  have at: "has_ptype \<Gamma> A Prop" by (rule pH_set_formula[OF d])
  have sa: "pterm_in_signature \<Sigma> A" by (rule pH_set_in_signature[OF d])
  have implication: "pH_set_derivable \<Sigma> \<Gamma> S (PImp A PObjFalse)"
    by (rule pH_set_deduction[OF at sa bad])
  have contradiction: "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
    by (rule pH_set_MP[OF d implication])
  show False using con contradiction unfolding pH_consistent_def by contradiction
qed

lemma pH_consistent_decision_extension:
  assumes con: "pH_consistent \<Sigma> \<Gamma> S"
    and at: "has_ptype \<Gamma> A Prop" and sa: "pterm_in_signature \<Sigma> A"
  shows "pH_consistent \<Sigma> \<Gamma> (insert A S) \<or>
    pH_consistent \<Sigma> \<Gamma> (insert (PNeg A) S)"
proof (rule ccontr)
  assume neither: "\<not> (pH_consistent \<Sigma> \<Gamma> (insert A S) \<or>
    pH_consistent \<Sigma> \<Gamma> (insert (PNeg A) S))"
  have bad_a: "pH_set_derivable \<Sigma> \<Gamma> (insert A S) PObjFalse"
    using neither unfolding pH_consistent_def by blast
  have bad_n: "pH_set_derivable \<Sigma> \<Gamma> (insert (PNeg A) S) PObjFalse"
    using neither unfolding pH_consistent_def by blast
  have nt: "has_ptype \<Gamma> (PNeg A) Prop" by (rule has_ptype.PNeg[OF at])
  have sn: "pterm_in_signature \<Sigma> (PNeg A)" using sa by simp
  have da: "pH_set_derivable \<Sigma> \<Gamma> S (PImp A PObjFalse)"
    by (rule pH_set_deduction[OF at sa bad_a])
  have dn: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PNeg A) PObjFalse)"
    by (rule pH_set_deduction[OF nt sn bad_n])
  let ?C = "PImp (PImp A PObjFalse) (PImp (PImp (PNeg A) PObjFalse) PObjFalse)"
  have ct: "has_ptype \<Gamma> ?C Prop"
    by (intro has_ptype.PImp at nt pH_lindenbaum_false_type)
  have cs: "pterm_in_signature \<Sigma> ?C"
    using sa pH_lindenbaum_false_signature[where \<Sigma>=\<Sigma>] by simp
  have eval: "\<forall>v. pprop_eval v ?C"
    by (intro allI) (simp only: pprop_eval.simps; blast)
  have taut: "pprop_tautology \<Gamma> ?C" unfolding pprop_tautology_def by (rule conjI[OF ct eval])
  have theorem_C: "pH_proves \<Sigma> \<Gamma> ?C" by (rule pH_proves.PC[OF taut cs])
  have dc: "pH_set_derivable \<Sigma> \<Gamma> S ?C" by (rule pH_set_Theorem[OF theorem_C])
  have last: "pH_set_derivable \<Sigma> \<Gamma> S (PImp (PImp (PNeg A) PObjFalse) PObjFalse)"
    by (rule pH_set_MP[OF da dc])
  have contradiction: "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
    by (rule pH_set_MP[OF dn last])
  show False using con contradiction unfolding pH_consistent_def by contradiction
qed

section \<open>Finite support makes nonempty chain unions consistent\<close>

text \<open>
  F ⊆ ⋃𝒞 and F finite ⇒ ∃U ∈ 𝒞, F ⊆ U, when 𝒞 is a nonempty
  inclusion chain.  Thus Conₕ(U) for all U ∈ 𝒞 implies Conₕ(⋃𝒞).
  This is the finite-proof step underlying the source's Lindenbaum argument.
  The proof uses finite support of derivations, not a countable stock of formulas.
\<close>

lemma pH_chain_union_consistent:
  assumes chain: "subset.chain \<A> \<C>" and nonempty: "\<C> \<noteq> {}"
    and all_con: "\<And>U. U \<in> \<C> \<Longrightarrow> pH_consistent \<Sigma> \<Gamma> U"
  shows "pH_consistent \<Sigma> \<Gamma> (\<Union>\<C>)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable \<Sigma> \<Gamma> (\<Union>\<C>) PObjFalse"
  obtain F where finite_F: "finite F" and contained: "F \<subseteq> \<Union>\<C>"
    and d: "pH_set_derivable \<Sigma> \<Gamma> F PObjFalse"
    by (rule pH_set_finite_support[OF bad])
  obtain U where member: "U \<in> \<C>" and covers: "F \<subseteq> U"
    by (rule finite_subset_Union_chain[OF finite_F contained nonempty chain])
  have bad_U: "pH_set_derivable \<Sigma> \<Gamma> U PObjFalse"
    by (rule pH_set_mono[OF d covers])
  have con_U: "pH_consistent \<Sigma> \<Gamma> U" by (rule all_con[OF member])
  show False using con_U bad_U unfolding pH_consistent_def by contradiction
qed

definition pH_maximal_extension ::
    "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_maximal_extension \<Sigma> \<Gamma> S T \<longleftrightarrow>
    S \<subseteq> T \<and> pH_typed_theory \<Sigma> \<Gamma> T \<and> pH_consistent \<Sigma> \<Gamma> T \<and>
    (\<forall>U. T \<subseteq> U \<longrightarrow> pH_typed_theory \<Sigma> \<Gamma> U \<longrightarrow>
      pH_consistent \<Sigma> \<Gamma> U \<longrightarrow> U = T)"

theorem pH_maximal_extension_exists:
  assumes typed_S: "pH_typed_theory \<Sigma> \<Gamma> S" and con_S: "pH_consistent \<Sigma> \<Gamma> S"
  obtains T where "pH_maximal_extension \<Sigma> \<Gamma> S T"
proof -
  let ?F = "{U. S \<subseteq> U \<and> pH_typed_theory \<Sigma> \<Gamma> U \<and> pH_consistent \<Sigma> \<Gamma> U}"
  have member_S: "S \<in> ?F" using typed_S con_S by simp
  have nonempty: "?F \<noteq> {}" using member_S by blast
  have unions: "\<Union>\<C> \<in> ?F" if nonempty_C: "\<C> \<noteq> {}" and chain: "subset.chain ?F \<C>" for \<C>
  proof -
    have inside: "\<C> \<subseteq> ?F" using chain unfolding subset_chain_def by (rule conjunct1)
    obtain U where U: "U \<in> \<C>" using nonempty_C by blast
    have inF: "U \<in> ?F" by (rule subsetD[OF inside U])
    have S_U: "S \<subseteq> U" using inF by simp
    have U_union: "U \<subseteq> \<Union>\<C>" by (rule Union_upper[OF U])
    have extends: "S \<subseteq> \<Union>\<C>" by (rule subset_trans[OF S_U U_union])
    have typed: "pH_typed_theory \<Sigma> \<Gamma> (\<Union>\<C>)"
    proof (unfold pH_typed_theory_def, intro ballI)
      fix A
      assume "A \<in> \<Union>\<C>"
      then obtain V where V: "V \<in> \<C>" and A: "A \<in> V" by blast
      have "V \<in> ?F" by (rule subsetD[OF inside V])
      then have vt: "pH_typed_theory \<Sigma> \<Gamma> V" by simp
      show "has_ptype \<Gamma> A Prop \<and> pterm_in_signature \<Sigma> A"
        using vt A unfolding pH_typed_theory_def by blast
    qed
    have all_con: "pH_consistent \<Sigma> \<Gamma> V" if V: "V \<in> \<C>" for V
    proof -
      have "V \<in> ?F" by (rule subsetD[OF inside V])
      then show ?thesis by simp
    qed
    have consistent: "pH_consistent \<Sigma> \<Gamma> (\<Union>\<C>)"
      by (rule pH_chain_union_consistent[OF chain nonempty_C all_con])
    show ?thesis using extends typed consistent by simp
  qed
  obtain T where member_T: "T \<in> ?F" and maximal: "\<forall>U \<in> ?F. T \<subseteq> U \<longrightarrow> U = T"
    using subset_Zorn_nonempty[OF nonempty unions] by blast
  have extends: "S \<subseteq> T" and typed_T: "pH_typed_theory \<Sigma> \<Gamma> T"
    and con_T: "pH_consistent \<Sigma> \<Gamma> T" using member_T by simp_all
  have max: "\<forall>U. T \<subseteq> U \<longrightarrow> pH_typed_theory \<Sigma> \<Gamma> U \<longrightarrow>
      pH_consistent \<Sigma> \<Gamma> U \<longrightarrow> U = T"
  proof (intro allI impI)
    fix U
    assume TU: "T \<subseteq> U" and ut: "pH_typed_theory \<Sigma> \<Gamma> U"
      and uc: "pH_consistent \<Sigma> \<Gamma> U"
    have SU: "S \<subseteq> U" by (rule subset_trans[OF extends TU])
    have uf: "U \<in> ?F" using SU ut uc by simp
    show "U = T" using maximal uf TU by blast
  qed
  have result: "pH_maximal_extension \<Sigma> \<Gamma> S T"
    unfolding pH_maximal_extension_def by (intro conjI extends typed_T con_T max)
  show thesis by (rule that[OF result])
qed

section \<open>Maximality yields closure and negation completeness\<close>

text \<open>
  T ⊢ₕ A ⇒ A ∈ T; and A ∈ L(Σ) ⇒ A ∈ T ∨ ¬A ∈ T.
  Source: Bacon, Exercise 15.3, pp. 319–320.
  A derivable formula can be added consistently.  At least one of A and
  ¬A can be added consistently, by deduction and a PC cases tautology.
  Maximality therefore forces the required membership.  No witnesses are added.
\<close>

lemma pH_maximal_extension_closed:
  assumes max: "pH_maximal_extension \<Sigma> \<Gamma> S T"
    and d: "pH_set_derivable \<Sigma> \<Gamma> T A"
  shows "A \<in> T"
proof -
  have typed: "pH_typed_theory \<Sigma> \<Gamma> T" and con: "pH_consistent \<Sigma> \<Gamma> T"
    using max unfolding pH_maximal_extension_def by simp_all
  have at: "has_ptype \<Gamma> A Prop" by (rule pH_set_formula[OF d])
  have sa: "pterm_in_signature \<Sigma> A" by (rule pH_set_in_signature[OF d])
  have ti: "pH_typed_theory \<Sigma> \<Gamma> (insert A T)"
    using typed at sa unfolding pH_typed_theory_def by simp
  have ci: "pH_consistent \<Sigma> \<Gamma> (insert A T)"
    by (rule pH_consistent_insert_derivable[OF con d])
  have equality: "insert A T = T" using max ti ci unfolding pH_maximal_extension_def by blast
  have "A \<in> insert A T" by (rule insertI1)
  then show ?thesis by (simp only: equality)
qed

lemma pH_maximal_extension_decides:
  assumes max: "pH_maximal_extension \<Sigma> \<Gamma> S T"
    and at: "has_ptype \<Gamma> A Prop" and sa: "pterm_in_signature \<Sigma> A"
  shows "A \<in> T \<or> PNeg A \<in> T"
proof -
  have typed: "pH_typed_theory \<Sigma> \<Gamma> T" and con: "pH_consistent \<Sigma> \<Gamma> T"
    using max unfolding pH_maximal_extension_def by simp_all
  have choice: "pH_consistent \<Sigma> \<Gamma> (insert A T) \<or>
      pH_consistent \<Sigma> \<Gamma> (insert (PNeg A) T)"
    by (rule pH_consistent_decision_extension[OF con at sa])
  show ?thesis
  proof (rule disjE[OF choice])
    assume positive: "pH_consistent \<Sigma> \<Gamma> (insert A T)"
    have ti: "pH_typed_theory \<Sigma> \<Gamma> (insert A T)"
      using typed at sa unfolding pH_typed_theory_def by simp
    have eq: "insert A T = T" using max ti positive unfolding pH_maximal_extension_def by blast
    have "A \<in> T" using insertI1[of A T] by (simp only: eq)
    then show ?thesis by (rule disjI1)
  next
    assume negative: "pH_consistent \<Sigma> \<Gamma> (insert (PNeg A) T)"
    have nt: "has_ptype \<Gamma> (PNeg A) Prop" by (rule has_ptype.PNeg[OF at])
    have sn: "pterm_in_signature \<Sigma> (PNeg A)" using sa by simp
    have ti: "pH_typed_theory \<Sigma> \<Gamma> (insert (PNeg A) T)"
      using typed nt sn unfolding pH_typed_theory_def by simp
    have eq: "insert (PNeg A) T = T" using max ti negative unfolding pH_maximal_extension_def by blast
    have "PNeg A \<in> T" using insertI1[of "PNeg A" T] by (simp only: eq)
    then show ?thesis by (rule disjI2)
  qed
qed

theorem pH_Lindenbaum_extension:
  assumes typed: "pH_typed_theory \<Sigma> \<Gamma> S" and con: "pH_consistent \<Sigma> \<Gamma> S"
  obtains T where "S \<subseteq> T" and "pH_typed_theory \<Sigma> \<Gamma> T" and "pH_consistent \<Sigma> \<Gamma> T"
    and "\<And>A. pH_set_derivable \<Sigma> \<Gamma> T A \<Longrightarrow> A \<in> T"
    and "\<And>A. has_ptype \<Gamma> A Prop \<Longrightarrow> pterm_in_signature \<Sigma> A \<Longrightarrow> A \<in> T \<or> PNeg A \<in> T"
    and "\<And>U. T \<subseteq> U \<Longrightarrow> pH_typed_theory \<Sigma> \<Gamma> U \<Longrightarrow> pH_consistent \<Sigma> \<Gamma> U \<Longrightarrow> U = T"
proof -
  obtain T where max: "pH_maximal_extension \<Sigma> \<Gamma> S T"
    by (rule pH_maximal_extension_exists[OF typed con])
  have extends: "S \<subseteq> T" and tt: "pH_typed_theory \<Sigma> \<Gamma> T" and tc: "pH_consistent \<Sigma> \<Gamma> T"
    using max unfolding pH_maximal_extension_def by simp_all
  have closed: "A \<in> T" if "pH_set_derivable \<Sigma> \<Gamma> T A" for A
    by (rule pH_maximal_extension_closed[OF max that])
  have complete: "A \<in> T \<or> PNeg A \<in> T" if "has_ptype \<Gamma> A Prop" "pterm_in_signature \<Sigma> A" for A
    by (rule pH_maximal_extension_decides[OF max that])
  have maximal: "U = T" if "T \<subseteq> U" "pH_typed_theory \<Sigma> \<Gamma> U" "pH_consistent \<Sigma> \<Gamma> U" for U
    using max that unfolding pH_maximal_extension_def by blast
  show thesis by (rule that[OF extends tt tc closed complete maximal])
qed

end
