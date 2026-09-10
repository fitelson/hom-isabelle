theory Bacon_Parametric_Local_Derivability
  imports Bacon_Parametric_Henkin_One_Step
begin

section \<open>Local consequence and consistency over arbitrary signatures\<close>

text \<open>
  Write Σ; Γ; Δ ⊢H A for a derivation from a finite list Δ of local
  assumptions, and Σ; Γ; S ⊢H A when such a list is drawn from S.
  Only assumptions, H theorems, and modus ponens act on local premises.
  Consequently a derivation from an arbitrary set has finite support.
  Sources: Bacon--Dorr Figure 2, p.8, and the finite-proof Henkin argument
  in p.45 n.64; Bacon, Chapter 15, Proposition 15.4.

  These are sources for the proof method, not definitions of this local
  relation. Footnote 64 concerns formula sets, whereas Theorem 3.2 states
  model existence for sentence sets. Unrestricted closure of open premises
  under the source H-theory rules differs from assumption/theorem/MP closure.
  Quantifier-rule transport here requires the explicit independence guards
  proved in Bacon_Parametric_Local_Quantifiers.

  Isabelle representation.  The name type is arbitrary.  Signature guards
  accompany local assumptions as well as H theorems.  Consistency means
  nonderivability of PObjFalse, the negation of ∀p.(p → p).
  No enumeration or countability assumption is used.
\<close>

inductive pH_derivable :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm list \<Rightarrow> 'c pterm \<Rightarrow> bool"
  for \<Sigma> \<Gamma> \<Delta> where
  Assumption: "A \<in> set \<Delta> \<Longrightarrow> has_ptype \<Gamma> A Prop \<Longrightarrow>
    pterm_in_signature \<Sigma> A \<Longrightarrow> pH_derivable \<Sigma> \<Gamma> \<Delta> A"
| Theorem: "pH_proves \<Sigma> \<Gamma> A \<Longrightarrow> pH_derivable \<Sigma> \<Gamma> \<Delta> A"
| MP: "pH_derivable \<Sigma> \<Gamma> \<Delta> A \<Longrightarrow> pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp A B) \<Longrightarrow>
    pH_derivable \<Sigma> \<Gamma> \<Delta> B"

definition pH_set_derivable :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pH_set_derivable \<Sigma> \<Gamma> S A \<longleftrightarrow> (\<exists>\<Delta>. set \<Delta> \<subseteq> S \<and> pH_derivable \<Sigma> \<Gamma> \<Delta> A)"

definition pH_consistent :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_consistent \<Sigma> \<Gamma> S \<longleftrightarrow> \<not> pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"

definition pH_typed_theory :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm set \<Rightarrow> bool" where
  "pH_typed_theory \<Sigma> \<Gamma> S \<longleftrightarrow>
    (\<forall>A \<in> S. has_ptype \<Gamma> A Prop \<and> pterm_in_signature \<Sigma> A)"

lemma pH_derivable_formula:
  "pH_derivable \<Sigma> \<Gamma> \<Delta> A \<Longrightarrow> has_ptype \<Gamma> A Prop"
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  show ?case by (rule Assumption.hyps(2))
next
  case (Theorem A)
  show ?case by (rule pH_proves_formula[OF Theorem.hyps])
next
  case (MP A B)
  show ?case using MP.IH(2) by (auto elim: has_ptype.cases)
qed

lemma pH_derivable_in_signature:
  "pH_derivable \<Sigma> \<Gamma> \<Delta> A \<Longrightarrow> pterm_in_signature \<Sigma> A"
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  show ?case by (rule Assumption.hyps(3))
next
  case (Theorem A)
  show ?case by (rule pH_proves_in_signature[OF Theorem.hyps])
next
  case (MP A B)
  show ?case using MP.IH(2) by simp
qed

lemma pH_derivable_mono:
  assumes derivation: "pH_derivable \<Sigma> \<Gamma> \<Delta> A" and subset: "set \<Delta> \<subseteq> set \<Pi>"
  shows "pH_derivable \<Sigma> \<Gamma> \<Pi> A"
  using derivation
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have member: "A \<in> set \<Pi>" by (rule subsetD[OF subset Assumption.hyps(1)])
  show ?case by (rule pH_derivable.Assumption[OF member Assumption.hyps(2,3)])
next
  case (Theorem A)
  show ?case by (rule pH_derivable.Theorem[OF Theorem.hyps])
next
  case (MP A B)
  show ?case by (rule pH_derivable.MP[OF MP.IH])
qed

lemma pH_set_formula:
  "pH_set_derivable \<Sigma> \<Gamma> S A \<Longrightarrow> has_ptype \<Gamma> A Prop"
  unfolding pH_set_derivable_def using pH_derivable_formula by blast

lemma pH_set_in_signature:
  "pH_set_derivable \<Sigma> \<Gamma> S A \<Longrightarrow> pterm_in_signature \<Sigma> A"
  unfolding pH_set_derivable_def using pH_derivable_in_signature by blast

lemma pH_set_mono:
  assumes "pH_set_derivable \<Sigma> \<Gamma> S A" and "S \<subseteq> T"
  shows "pH_set_derivable \<Sigma> \<Gamma> T A"
  using assms unfolding pH_set_derivable_def by blast

lemma pH_set_Assumption:
  assumes member: "A \<in> S" and typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature \<Sigma> A"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
proof -
  have d: "pH_derivable \<Sigma> \<Gamma> [A] A" by (rule pH_derivable.Assumption[OF _ typed sig]) simp
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x="[A]"], rule conjI) (simp add: member, rule d)
qed

lemma pH_set_Theorem:
  assumes "pH_proves \<Sigma> \<Gamma> A"
  shows "pH_set_derivable \<Sigma> \<Gamma> S A"
  unfolding pH_set_derivable_def
  by (rule exI[where x="[]"], rule conjI) (simp, rule pH_derivable.Theorem[OF assms])

lemma pH_set_MP:
  assumes first: "pH_set_derivable \<Sigma> \<Gamma> S A" and second: "pH_set_derivable \<Sigma> \<Gamma> S (PImp A B)"
  shows "pH_set_derivable \<Sigma> \<Gamma> S B"
proof -
  obtain \<Delta> where ds: "set \<Delta> \<subseteq> S" and d: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    using first unfolding pH_set_derivable_def by blast
  obtain \<Pi> where ps: "set \<Pi> \<subseteq> S" and p: "pH_derivable \<Sigma> \<Gamma> \<Pi> (PImp A B)"
    using second unfolding pH_set_derivable_def by blast
  have d': "pH_derivable \<Sigma> \<Gamma> (\<Delta> @ \<Pi>) A" by (rule pH_derivable_mono[OF d]) auto
  have p': "pH_derivable \<Sigma> \<Gamma> (\<Delta> @ \<Pi>) (PImp A B)" by (rule pH_derivable_mono[OF p]) auto
  have result: "pH_derivable \<Sigma> \<Gamma> (\<Delta> @ \<Pi>) B" by (rule pH_derivable.MP[OF d' p'])
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x="\<Delta> @ \<Pi>"], rule conjI) (use ds ps in auto, rule result)
qed

lemma pH_set_finite_support:
  assumes derivation: "pH_set_derivable \<Sigma> \<Gamma> S A"
  obtains F where "finite F" and "F \<subseteq> S" and "pH_set_derivable \<Sigma> \<Gamma> F A"
proof -
  obtain \<Delta> where subset: "set \<Delta> \<subseteq> S" and d: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    using derivation unfolding pH_set_derivable_def by blast
  have finite: "finite (set \<Delta>)" by simp
  have supported: "pH_set_derivable \<Sigma> \<Gamma> (set \<Delta>) A"
    unfolding pH_set_derivable_def by (rule exI[where x=\<Delta>], rule conjI) (simp, rule d)
  show ?thesis by (rule that[where F="set \<Delta>", OF finite subset supported])
qed

lemma pH_consistent_subset:
  "pH_consistent \<Sigma> \<Gamma> T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> pH_consistent \<Sigma> \<Gamma> S"
  unfolding pH_consistent_def using pH_set_mono by blast

subsection \<open>Discharging one local premise\<close>

lemma pH_local_PC:
  "pprop_tautology \<Gamma> A \<Longrightarrow> pterm_in_signature \<Sigma> A \<Longrightarrow> pH_derivable \<Sigma> \<Gamma> \<Delta> A"
  by (intro pH_derivable.Theorem pH_proves.PC)

lemma pH_local_imp_of_right:
  assumes A: "has_ptype \<Gamma> A Prop" and sigA: "pterm_in_signature \<Sigma> A"
    and d: "pH_derivable \<Sigma> \<Gamma> \<Delta> B"
  shows "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp A B)"
proof -
  have B: "has_ptype \<Gamma> B Prop" by (rule pH_derivable_formula[OF d])
  have sigB: "pterm_in_signature \<Sigma> B" by (rule pH_derivable_in_signature[OF d])
  have taut: "pprop_tautology \<Gamma> (PImp B (PImp A B))"
    unfolding pprop_tautology_def using A B by auto
  have sig: "pterm_in_signature \<Sigma> (PImp B (PImp A B))" using sigA sigB by simp
  show ?thesis by (rule pH_derivable.MP[OF d pH_local_PC[OF taut sig]])
qed

lemma pH_derivable_deduction_subset:
  assumes A: "has_ptype \<Gamma> A Prop" and sigA: "pterm_in_signature \<Sigma> A"
    and derivation: "pH_derivable \<Sigma> \<Gamma> \<Pi> B"
    and subset: "set \<Pi> \<subseteq> insert A (set \<Delta>)"
  shows "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp A B)"
  using derivation
proof (induction rule: pH_derivable.induct)
  case (Assumption B)
  show ?case
  proof (cases "B = A")
    case True
    have taut: "pprop_tautology \<Gamma> (PImp A A)" unfolding pprop_tautology_def using A by auto
    have sig: "pterm_in_signature \<Sigma> (PImp A A)" using sigA by simp
    show ?thesis using pH_local_PC[OF taut sig] by (simp only: True)
  next
    case False
    have member: "B \<in> set \<Delta>" using subset Assumption.hyps(1) False by blast
    have local_B: "pH_derivable \<Sigma> \<Gamma> \<Delta> B"
      by (rule pH_derivable.Assumption[OF member Assumption.hyps(2,3)])
    show ?thesis by (rule pH_local_imp_of_right[OF A sigA local_B])
  qed
next
  case (Theorem B)
  have local_B: "pH_derivable \<Sigma> \<Gamma> \<Delta> B" by (rule pH_derivable.Theorem[OF Theorem.hyps])
  show ?case by (rule pH_local_imp_of_right[OF A sigA local_B])
next
  case (MP B C)
  have B: "has_ptype \<Gamma> B Prop" by (rule pH_derivable_formula[OF MP.hyps(1)])
  have BC: "has_ptype \<Gamma> (PImp B C) Prop" by (rule pH_derivable_formula[OF MP.hyps(2)])
  have C: "has_ptype \<Gamma> C Prop" using BC by (auto elim: has_ptype.cases)
  have sigB: "pterm_in_signature \<Sigma> B" by (rule pH_derivable_in_signature[OF MP.hyps(1)])
  have sigC: "pterm_in_signature \<Sigma> C" using pH_derivable_in_signature[OF MP.hyps(2)] by simp
  let ?T = "PImp (PImp A (PImp B C)) (PImp (PImp A B) (PImp A C))"
  have taut: "pprop_tautology \<Gamma> ?T" unfolding pprop_tautology_def using A B C by auto
  have sig: "pterm_in_signature \<Sigma> ?T" using sigA sigB sigC by simp
  have step: "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp (PImp A B) (PImp A C))"
    by (rule pH_derivable.MP[OF MP.IH(2) pH_local_PC[OF taut sig]])
  show ?case by (rule pH_derivable.MP[OF MP.IH(1) step])
qed

lemma pH_derivable_deduction:
  assumes "has_ptype \<Gamma> A Prop" and "pterm_in_signature \<Sigma> A"
    and "pH_derivable \<Sigma> \<Gamma> (A # \<Delta>) B"
  shows "pH_derivable \<Sigma> \<Gamma> \<Delta> (PImp A B)"
  by (rule pH_derivable_deduction_subset[OF assms]) simp

lemma pH_set_deduction:
  assumes A: "has_ptype \<Gamma> A Prop" and sigA: "pterm_in_signature \<Sigma> A"
    and d: "pH_set_derivable \<Sigma> \<Gamma> (insert A S) B"
  shows "pH_set_derivable \<Sigma> \<Gamma> S (PImp A B)"
proof -
  obtain \<Pi> where subset: "set \<Pi> \<subseteq> insert A S" and local: "pH_derivable \<Sigma> \<Gamma> \<Pi> B"
    using d unfolding pH_set_derivable_def by blast
  have discharge: "set \<Pi> \<subseteq> insert A (set (removeAll A \<Pi>))" by auto
  have result: "pH_derivable \<Sigma> \<Gamma> (removeAll A \<Pi>) (PImp A B)"
    by (rule pH_derivable_deduction_subset[OF A sigA local discharge])
  have remaining: "set (removeAll A \<Pi>) \<subseteq> S" using subset by auto
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x="removeAll A \<Pi>"], rule conjI) (rule remaining, rule result)
qed

subsection \<open>Changing and embedding constant-name carriers\<close>

lemma pH_derivable_map:
  assumes d: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Omega> \<sigma>"
  shows "pH_derivable \<Omega> \<Gamma> (map (phenkin_map k) \<Delta>) (phenkin_map k A)"
  using d
proof (induction rule: pH_derivable.induct)
  case (Assumption A)
  have member: "phenkin_map k A \<in> set (map (phenkin_map k) \<Delta>)"
    by (simp only: set_map) (rule imageI[OF Assumption.hyps(1)])
  show ?case by (rule pH_derivable.Assumption[OF member phenkin_map_type[OF Assumption.hyps(2)]
    phenkin_map_signature[OF Assumption.hyps(3) names]])
next
  case (Theorem A)
  show ?case by (rule pH_derivable.Theorem[OF phenkin_map_proves[OF Theorem.hyps names]])
next
  case (MP A B)
  have implication: "pH_derivable \<Omega> \<Gamma> (map (phenkin_map k) \<Delta>) (PImp (phenkin_map k A) (phenkin_map k B))"
    using MP.IH(2) by simp
  show ?case by (rule pH_derivable.MP[OF MP.IH(1) implication])
qed

lemma pH_set_map:
  assumes d: "pH_set_derivable \<Sigma> \<Gamma> S A"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Omega> \<sigma>"
  shows "pH_set_derivable \<Omega> \<Gamma> (phenkin_map k ` S) (phenkin_map k A)"
proof -
  obtain \<Delta> where subset: "set \<Delta> \<subseteq> S" and local: "pH_derivable \<Sigma> \<Gamma> \<Delta> A"
    using d unfolding pH_set_derivable_def by blast
  have mapped_subset: "set (map (phenkin_map k) \<Delta>) \<subseteq> phenkin_map k ` S" using subset by auto
  have mapped: "pH_derivable \<Omega> \<Gamma> (map (phenkin_map k) \<Delta>) (phenkin_map k A)"
    by (rule pH_derivable_map[OF local names])
  show ?thesis unfolding pH_set_derivable_def
    by (rule exI[where x="map (phenkin_map k) \<Delta>"], rule conjI) (rule mapped_subset, rule mapped)
qed

lemma pH_set_embed:
  "pH_set_derivable \<Sigma> \<Gamma> S A \<Longrightarrow>
    pH_set_derivable (phenkin_signature \<Sigma>) \<Gamma> (phenkin_embed ` S) (phenkin_embed A)"
  unfolding phenkin_embed_def by (rule pH_set_map) (assumption, simp)

lemma pH_typed_theory_embed:
  assumes "pH_typed_theory \<Sigma> \<Gamma> S"
  shows "pH_typed_theory (phenkin_signature \<Sigma>) \<Gamma> (phenkin_embed ` S)"
  using assms phenkin_embed_type unfolding pH_typed_theory_def
  by (auto simp only: phenkin_embed_signature)

lemma pH_name_map_PObjFalse[simp]: "phenkin_map k PObjFalse = PObjFalse"
  by (simp add: PObjFalse_def PObjTrue_def)

lemma pH_name_map_inverse:
  assumes inverse: "\<And>c. l (k c) = c"
  shows "phenkin_map l (phenkin_map k A) = A"
  by (induction A) (simp_all add: inverse)

lemma pH_map_consistency_reflection:
  assumes maps: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Omega> \<sigma>"
    and consistent: "pH_consistent \<Omega> \<Gamma> (phenkin_map k ` S)"
  shows "pH_consistent \<Sigma> \<Gamma> S"
proof (unfold pH_consistent_def, intro notI)
  assume bad: "pH_set_derivable \<Sigma> \<Gamma> S PObjFalse"
  have mapped: "pH_set_derivable \<Omega> \<Gamma> (phenkin_map k ` S) PObjFalse"
    using pH_set_map[OF bad maps] by simp
  show False using consistent mapped unfolding pH_consistent_def by blast
qed

text \<open>
  These mapping lemmas preserve proofs into an expanded signature and
  reflect consistency from it.  They do not yet prove consistency of
  an embedded old theory in that expansion.  In particular, projecting
  all new names to one old name need not respect every type-indexed
  signature.  Fresh-witness conservativity requires its own argument.
\<close>

end
