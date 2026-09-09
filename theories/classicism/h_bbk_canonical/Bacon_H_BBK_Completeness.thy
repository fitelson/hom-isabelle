theory Bacon_H_BBK_Completeness
  imports Bacon_H_BBK_Canonical_Model
begin

section \<open>Closed-sentence soundness and completeness for represented H\<close>

text \<open>
  ⊢ₕ A ⇔ every represented BBK model satisfies A, for closed A. Bacon–Dorr, Theorem
  3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Validity is indexed by a HOL carrier type. Soundness holds
  for every carrier; completeness uses the fixed carrier of tagged term classes so
  that canonical countermodels fit.

  Status: Closed-sentence completeness for F and universal typed-string names.
  Arbitrary small carriers are not separately claimed complete.
\<close>

definition H_BBK_closed_valid :: "'v itself \<Rightarrow> oterm \<Rightarrow> bool" where
  "H_BBK_closed_valid TYPE('v) A \<longleftrightarrow>
    [] \<turnstile> A : Prop \<and>
    (\<forall>D :: otype \<Rightarrow> 'v set. \<forall>J :: (nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v.
      \<forall>V :: 'v \<Rightarrow> bool. bbk_model (\<lambda>_. UNIV) D J V \<longrightarrow> (\<forall>g. V (J g A)))"

lemma H_BBK_closed_valid_typed:
  "H_BBK_closed_valid TYPE('v) A \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding H_BBK_closed_valid_def by blast

lemma H_BBK_closed_validD:
  assumes valid: "H_BBK_closed_valid TYPE('v) A"
    and model: "bbk_model (\<lambda>_. UNIV) D J (V :: 'v \<Rightarrow> bool)"
  shows "\<forall>g. V (J g A)"
  using valid model unfolding H_BBK_closed_valid_def by blast

theorem H_BBK_closed_soundness:
  assumes derivation: "[] \<turnstile>\<^sub>H A"
  shows "H_BBK_closed_valid TYPE('v) A"
proof (unfold H_BBK_closed_valid_def, rule conjI)
  show "[] \<turnstile> A : Prop" by (rule H_proves_formula[OF derivation])
next
  show "\<forall>D :: otype \<Rightarrow> 'v set. \<forall>J :: (nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v.
    \<forall>V :: 'v \<Rightarrow> bool. bbk_model (\<lambda>_. UNIV) D J V \<longrightarrow> (\<forall>g. V (J g A))"
  proof (intro allI impI)
    fix D :: "otype \<Rightarrow> 'v set" and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v"
      and V :: "'v \<Rightarrow> bool" and g :: "nat \<Rightarrow> 'v"
    assume model: "bbk_model (\<lambda>_. UNIV) D J V"
    interpret M: bbk_model "\<lambda>_. UNIV" D J V by (rule model)
    have full: "\<And>\<sigma>. (\<lambda>_ :: otype. (UNIV :: string set)) \<sigma> = UNIV" by simp
    note valid = M.H_BBK_soundness_universal_signature[OF full derivation]
    have env: "bbk_env_typed D [] g" by (rule bbk_env_empty)
    note satisfied = M.valid_satisfies[OF valid env]
    show "V (J g A)" using satisfied by (simp only: M.bbk_satisfies_def)
  qed
qed

context H_closed_Henkin
begin

lemma H_BBK_canonical_model:
  "bbk_model (\<lambda>_. UNIV) H_BBK_domain H_BBK_denote H_BBK_holds"
  by (rule Canonical.bbk_model_axioms)

lemma H_BBK_closed_truth_lemma:
  assumes typed: "[] \<turnstile> A : Prop"
  shows "H_BBK_holds (H_BBK_denote g A) \<longleftrightarrow> A \<in> T"
proof -
  have env: "H_BBK_env_typed [] g" by (simp add: H_BBK_env_typed_def lookup_def)
  show ?thesis
    by (simp only: H_BBK_denote_eq_den[OF typed env] H_BBK_den_closed[OF typed]
          H_BBK_holds_class[OF typed])
qed

end

subsection \<open>An actual BBK countermodel for every unprovable sentence\<close>

text \<open>
  ⊬ₕ A ⇒ ∃𝔐, 𝔐 ⊭ A for a typed closed sentence A. Bacon–Dorr, Theorem 3.2, p. 45 n.
  64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: Extend {¬A} to a Henkin theory, interpret the canonical
  model, and use the semantic membership truth lemma.

  Status: This file starts from a finite singleton; arbitrary-theory model existence
  is supplied in h_bbk_strong_completeness.
\<close>

theorem H_BBK_closed_countermodel:
  assumes typed: "[] \<turnstile> A : Prop" and unprovable: "\<not> [] \<turnstile>\<^sub>H A"
  obtains D :: "otype \<Rightarrow> h_bbk_value set"
    and J :: "(nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value"
    and V :: "h_bbk_value \<Rightarrow> bool"
  where "bbk_model (\<lambda>_. UNIV) D J V" and "\<forall>g. \<not> V (J g A)"
proof -
  obtain body_enum where bodies: "enumerates_witness_bodies [] body_enum"
    using enumerates_witness_bodies_exists by blast
  obtain formula_enum where formulas: "enumerates_formulas [] formula_enum"
    using enumerates_formulas_exists by blast
  obtain U where henkin_U: "H_Henkin_theory [] U" and neg_in: "Neg A \<in> U"
    by (rule H_canonical_Henkin_theory_for_unprovable_staged[OF typed unprovable bodies formulas])
  have not_in: "A \<notin> U"
    using H_Henkin_neg_mem_iff[OF henkin_U typed] neg_in by blast
  interpret C: H_closed_Henkin U by (unfold_locales) (rule henkin_U)
  let ?D = "H_closed_Henkin.H_BBK_domain U"
  let ?J = "H_closed_Henkin.H_BBK_denote U"
  let ?V = "H_closed_Henkin.H_BBK_holds U"
  have model: "bbk_model (\<lambda>_. UNIV) ?D ?J ?V"
    by (rule C.H_BBK_canonical_model)
  have falsifies: "\<forall>g. \<not> ?V (?J g A)"
  proof (rule allI)
    fix g
    show "\<not> ?V (?J g A)"
      using C.H_BBK_closed_truth_lemma[OF typed, where g=g] not_in by blast
  qed
  show ?thesis
    by (rule that[where D="?D" and J="?J" and V="?V",
          OF model falsifies])
qed

theorem H_BBK_closed_valid_iff_proves:
  "H_BBK_closed_valid TYPE(h_bbk_value) A \<longleftrightarrow> [] \<turnstile>\<^sub>H A"
proof
  assume valid: "H_BBK_closed_valid TYPE(h_bbk_value) A"
  have typed: "[] \<turnstile> A : Prop" by (rule H_BBK_closed_valid_typed[OF valid])
  show "[] \<turnstile>\<^sub>H A"
  proof (rule ccontr)
    assume unprovable: "\<not> [] \<turnstile>\<^sub>H A"
    obtain D :: "otype \<Rightarrow> h_bbk_value set"
      and J :: "(nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value"
      and V :: "h_bbk_value \<Rightarrow> bool"
      where model: "bbk_model (\<lambda>_. UNIV) D J V"
      and falsifies: "\<forall>g. \<not> V (J g A)"
    proof (rule H_BBK_closed_countermodel[OF typed unprovable])
      fix D :: "otype \<Rightarrow> h_bbk_value set"
        and J :: "(nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value"
        and V :: "h_bbk_value \<Rightarrow> bool"
      assume model_D: "bbk_model (\<lambda>_. UNIV) D J V"
        and falsifies_D: "\<forall>g. \<not> V (J g A)"
      show thesis by (rule that[where D=D and J=J and V=V, OF model_D falsifies_D])
    qed
    have truth: "\<forall>g. V (J g A)" by (rule H_BBK_closed_validD[OF valid model])
    show False using truth falsifies by blast
  qed
next
  assume derivation: "[] \<turnstile>\<^sub>H A"
  show "H_BBK_closed_valid TYPE(h_bbk_value) A" by (rule H_BBK_closed_soundness[OF derivation])
qed

corollary H_BBK_closed_valid_every_carrier:
  assumes valid: "H_BBK_closed_valid TYPE(h_bbk_value) A"
  shows "H_BBK_closed_valid TYPE('v) A"
proof -
  have derivation: "[] \<turnstile>\<^sub>H A" using H_BBK_closed_valid_iff_proves valid by blast
  show ?thesis by (rule H_BBK_closed_soundness[OF derivation])
qed

text \<open>
  The construction here starts from {¬A}.  Arbitrary consistent starting sets
  need a reserved witness signature: first embed the original names into a
  disjoint stock, then Henkinize and pull the interpretation back.

  That extension is supplied by Bacon_H_Arbitrary_Henkin and
  Bacon_H_Arbitrary_Model in h_bbk_strong_completeness.  The h_bbk_countable
  theories subsequently put the domains inside ℕ.  Neither development
  removes the separate first-class-logical-constant translation or
  arbitrary-cardinality-signature completeness obligations.
\<close>

end
