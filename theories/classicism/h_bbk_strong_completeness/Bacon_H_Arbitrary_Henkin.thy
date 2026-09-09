theory Bacon_H_Arbitrary_Henkin
  imports Bacon_H_Signature_Renaming
begin

section \<open>Henkin extension of an arbitrary renamed theory\<close>

text \<open>
  Conₕ(S) ⇒ ∃T ⊇ ι(S), T is consistent, negation-complete, and witness-complete.
  Bacon, Proposition 15.4, p. 319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: Each stage adds only finitely many witness axioms to the
  renamed base. A disjoint W-prefixed stock avoids that base and the finitely many new
  forbidden names.

  Status: Arbitrary sets of closed sentences in the represented string language;
  pullback to original names is the next file.
\<close>

subsection \<open>A reserved witness outside every finite forbidden set\<close>

text \<open>
  F finite ⇒ ∃c ∈ range(ω), c ∉ F. Bacon, Proposition 15.4, p. 319; Bacon–Dorr, p. 45
  n. 64.

  Isabelle representation: The reserve is infinite and disjoint from original
  O-prefixed names. Freshness is checked against the current finite additions and
  witness body.

  Status: Freshness is proved after renaming; none is assumed in the original
  arbitrary theory.
\<close>

lemma H_witness_name_unprefix[simp]:
  "H_unprefix_name (H_witness_name c) = c"
  by (simp add: H_unprefix_name_def H_witness_name_def)

lemma H_witness_name_fresh_finite:
  assumes finite_F: "finite F"
  shows "\<exists>w. H_witness_name w \<notin> F"
proof -
  have finite_inverse: "finite (H_unprefix_name ` F)" using finite_F by simp
  obtain w where fresh: "w \<notin> H_unprefix_name ` F"
    using fresh_string_finite[OF finite_inverse] by blast
  have candidate: "H_witness_name w \<notin> F"
  proof
    assume member: "H_witness_name w \<in> F"
    have "H_unprefix_name (H_witness_name w) \<in> H_unprefix_name ` F"
      by (rule imageI[OF member])
    then show False using fresh by simp
  qed
  show ?thesis by (rule exI[where x=w]) (rule candidate)
qed

lemma H_fresh_for_finite_extra:
  assumes finite_extra: "finite (U - H_rename_constants H_original_name ` S)"
  shows "fresh_const_for (fresh_const_for_stage U A) U A"
proof -
  let ?B = "H_rename_constants H_original_name ` S"
  let ?E = "U - ?B"
  let ?F = "consts_of_set ?E \<union> consts_of A"
  have finite_names: "finite ?F"
    using finite_consts_of_set[OF finite_extra] by simp
  obtain w where fresh: "H_witness_name w \<notin> ?F"
    using H_witness_name_fresh_finite[OF finite_names] by blast
  have base_fresh: "H_witness_name w \<notin> consts_of_set ?B"
    by (rule H_original_theory_avoids_witness_names)
  have names_cover: "consts_of_set U \<subseteq> consts_of_set ?B \<union> consts_of_set ?E"
    unfolding consts_of_set_def by blast
  have whole_fresh: "H_witness_name w \<notin> consts_of_set U"
    using fresh base_fresh names_cover by blast
  have body_fresh: "H_witness_name w \<notin> consts_of A" using fresh by blast
  have candidate: "fresh_const_for (H_witness_name w) U A"
    using whole_fresh body_fresh unfolding fresh_const_for_def by blast
  have exists_fresh: "\<exists>c. fresh_const_for c U A"
    by (rule exI[where x="H_witness_name w"]) (rule candidate)
  show ?thesis unfolding fresh_const_for_stage_def by (rule someI_ex[OF exists_fresh])
qed

subsection \<open>Each stage has only finitely many additional formulas\<close>

text \<open>
  T₀ = ι(S), Tₙ ⊆ Tₙ₊₁, and Tₙ ∖ ι(S) is finite. Bacon, Proposition 15.4, p. 319;
  Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: Induction on n tracks the staged_henkin_chain while
  allowing S itself to be infinite.

  Status: Finite growth above an arbitrary base, not finiteness of the whole stage.
\<close>

lemma H_staged_step_finite_extra:
  assumes finite_extra: "finite (U - B)"
  shows "finite (staged_henkin_step \<Gamma> spec U - B)"
proof -
  obtain \<sigma> A where spec: "spec = (\<sigma>, A)" by (cases spec) blast
  let ?ax = "henkin_witness_axiom (fresh_const_for_stage U A) \<sigma> A"
  have finite_cover: "finite (insert ?ax (U - B))" using finite_extra by simp
  have subset: "insert ?ax U - B \<subseteq> insert ?ax (U - B)" by blast
  have finite_insert: "finite (insert ?ax U - B)"
    by (rule finite_subset[OF subset finite_cover])
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    show ?thesis using finite_insert by (simp add: staged_henkin_step_def spec True)
  next
    case False
    show ?thesis using finite_extra by (simp add: staged_henkin_step_def spec False)
  qed
qed

lemma H_staged_chain_finite_extra:
  "finite (staged_henkin_chain \<Gamma> B enum n - B)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have next_finite: "finite (staged_henkin_step \<Gamma> (enum n)
      (staged_henkin_chain \<Gamma> B enum n) - B)"
    by (rule H_staged_step_finite_extra[OF Suc.IH])
  show ?case using next_finite by simp
qed

lemma H_staged_chain_extends_base:
  "B \<subseteq> staged_henkin_chain \<Gamma> B enum n"
proof -
  have "staged_henkin_chain \<Gamma> B enum 0 \<subseteq> staged_henkin_chain \<Gamma> B enum n"
    by (rule nat_chain_mono[where S="staged_henkin_chain \<Gamma> B enum" and i=0 and j=n])
      (rule staged_henkin_chain_step, simp)
  then show ?thesis by simp
qed

lemma H_arbitrary_staged_step_consistent:
  assumes finite_extra: "finite (U - H_rename_constants H_original_name ` S)"
    and typed: "typed_theory \<Gamma> U" and consistent: "H_consistent \<Gamma> U"
  shows "H_consistent \<Gamma> (staged_henkin_step \<Gamma> spec U)"
proof -
  obtain \<sigma> A where spec: "spec = (\<sigma>, A)" by (cases spec) blast
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh: "fresh_const_for (fresh_const_for_stage U A) U A"
      by (rule H_fresh_for_finite_extra[OF finite_extra])
    have fresh_U: "fresh_const_for_stage U A \<notin> consts_of_set U"
      and fresh_A: "fresh_const_for_stage U A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by blast+
    have next_consistent: "H_consistent \<Gamma>
        (insert (henkin_witness_axiom (fresh_const_for_stage U A) \<sigma> A) U)"
      by (rule H_consistent_insert_fresh_witness_axiom[OF typed consistent fresh_U fresh_A True])
    show ?thesis using next_consistent by (simp add: staged_henkin_step_def spec True)
  next
    case False
    show ?thesis using consistent by (simp add: staged_henkin_step_def spec False)
  qed
qed

lemma H_arbitrary_staged_chain_typed:
  assumes typed: "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma> (staged_henkin_chain \<Gamma> (H_rename_constants H_original_name ` S) enum n)"
  by (rule staged_henkin_chain_typed[OF H_original_theory_typed[OF typed]])

lemma H_arbitrary_staged_chain_consistent:
  assumes typed: "typed_theory \<Gamma> S" and consistent: "H_consistent \<Gamma> S"
  shows "H_consistent \<Gamma> (staged_henkin_chain \<Gamma> (H_rename_constants H_original_name ` S) enum n)"
proof (induction n)
  case 0
  have base_consistent: "H_consistent \<Gamma> (H_rename_constants H_original_name ` S)"
    using H_original_theory_consistent_iff consistent by blast
  show ?case using base_consistent by simp
next
  case (Suc n)
  let ?U = "staged_henkin_chain \<Gamma> (H_rename_constants H_original_name ` S) enum n"
  have extras: "finite (?U - H_rename_constants H_original_name ` S)"
    by (rule H_staged_chain_finite_extra)
  have stage_typed: "typed_theory \<Gamma> ?U" by (rule H_arbitrary_staged_chain_typed[OF typed])
  have next_consistent: "H_consistent \<Gamma> (staged_henkin_step \<Gamma> (enum n) ?U)"
    by (rule H_arbitrary_staged_step_consistent[OF extras stage_typed Suc.IH])
  show ?case using next_consistent by simp
qed

subsection \<open>The increasing union remains consistent\<close>

text \<open>
  T∞ = ⋃ₙTₙ is consistent whenever every Tₙ is consistent. Bacon, Proposition 15.4, p.
  319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: Any derivation of ⊥ uses finitely many premises, all
  contained in one stage of the increasing chain.

  Status: Consistency of the union is proved; witness availability and maximal
  completion are separate subsequent steps.
\<close>

definition H_arbitrary_witness_limit ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> oterm set" where
  "H_arbitrary_witness_limit \<Gamma> S enum =
    staged_henkin_extension \<Gamma> (H_rename_constants H_original_name ` S) enum"

lemma H_arbitrary_witness_limit_extends:
  "H_rename_constants H_original_name ` S \<subseteq> H_arbitrary_witness_limit \<Gamma> S enum"
  unfolding H_arbitrary_witness_limit_def by (rule staged_henkin_extension_extends)

lemma H_arbitrary_witness_limit_typed:
  assumes typed: "typed_theory \<Gamma> S"
  shows "typed_theory \<Gamma> (H_arbitrary_witness_limit \<Gamma> S enum)"
  unfolding H_arbitrary_witness_limit_def
  by (rule staged_henkin_extension_typed[OF H_original_theory_typed[OF typed]])

lemma H_arbitrary_witness_limit_consistent:
  assumes typed: "typed_theory \<Gamma> S" and consistent: "H_consistent \<Gamma> S"
  shows "H_consistent \<Gamma> (H_arbitrary_witness_limit \<Gamma> S enum)"
proof (unfold H_consistent_def, intro notI)
  assume bad: "\<Gamma> ; H_arbitrary_witness_limit \<Gamma> S enum \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  obtain F where finite_F: "finite F" and subset: "F \<subseteq> H_arbitrary_witness_limit \<Gamma> S enum"
    and bad_F: "\<Gamma> ; F \<turnstile>\<^sub>H\<^sub>s ObjFalse"
  proof (rule H_set_derivable_finite_support[OF bad])
    fix F
    assume finite_F: "finite F" and subset: "F \<subseteq> H_arbitrary_witness_limit \<Gamma> S enum"
      and bad_F: "\<Gamma> ; F \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    show thesis by (rule that[where F=F, OF finite_F subset bad_F])
  qed
  let ?chain = "staged_henkin_chain \<Gamma> (H_rename_constants H_original_name ` S) enum"
  have in_union: "F \<subseteq> (\<Union>n. ?chain n)"
    using subset by (simp only: H_arbitrary_witness_limit_def staged_henkin_extension_def)
  have steps: "\<And>n. ?chain n \<subseteq> ?chain (Suc n)" by (rule staged_henkin_chain_step)
  have bounded: "\<exists>n. F \<subseteq> ?chain n"
    by (rule finite_subset_nat_chain[where S="?chain" and F=F, OF finite_F in_union steps])
  obtain n where stage_subset: "F \<subseteq> ?chain n" using bounded by blast
  have bad_stage: "\<Gamma> ; ?chain n \<turnstile>\<^sub>H\<^sub>s ObjFalse"
    by (rule H_set_derivable_mono[OF bad_F stage_subset])
  have good_stage: "H_consistent \<Gamma> (?chain n)"
    by (rule H_arbitrary_staged_chain_consistent[OF typed consistent])
  show False using good_stage bad_stage unfolding H_consistent_def by blast
qed

lemma H_arbitrary_witness_limit_available:
  assumes enumeration: "enumerates_witness_bodies \<Gamma> enum"
  shows "Henkin_witness_axioms_available \<Gamma> (H_arbitrary_witness_limit \<Gamma> S enum)"
  unfolding H_arbitrary_witness_limit_def
  by (rule staged_henkin_extension_witness_axioms_available[OF enumeration])

subsection \<open>A negation-complete and witness-complete extension\<close>

text \<open>
  ∀A, A ∈ T or ¬A ∈ T; ∃x A ∈ T ⇒ A[c/x] ∈ T for some witness c. Bacon, Proposition
  15.4, p. 319; Bacon–Dorr, p. 45 n. 64.

  Isabelle representation: Lindenbaum completion closes the consistent staged union.
  Deductive closure turns the available witness axioms into actual witnesses.

  Status: The extension realizes the renamed arbitrary theory; semantic pullback
  remains to be performed.
\<close>

definition H_arbitrary_Henkin ::
    "ctx \<Rightarrow> oterm set \<Rightarrow> (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> (nat \<Rightarrow> oterm) \<Rightarrow> oterm set" where
  "H_arbitrary_Henkin \<Gamma> S bodies formulas =
    H_lindenbaum_extension \<Gamma> (H_arbitrary_witness_limit \<Gamma> S bodies) formulas"

theorem H_arbitrary_Henkin_theory:
  assumes typed: "typed_theory \<Gamma> S" and consistent: "H_consistent \<Gamma> S"
    and bodies: "enumerates_witness_bodies \<Gamma> bodies"
    and formulas: "enumerates_formulas \<Gamma> formulas"
  shows "H_Henkin_theory \<Gamma> (H_arbitrary_Henkin \<Gamma> S bodies formulas)"
  unfolding H_arbitrary_Henkin_def
  by (rule H_lindenbaum_extension_Henkin_theory_from_available[
        OF H_arbitrary_witness_limit_typed[OF typed]
        H_arbitrary_witness_limit_consistent[OF typed consistent] formulas
        H_arbitrary_witness_limit_available[OF bodies]])

lemma H_arbitrary_Henkin_extends:
  "H_rename_constants H_original_name ` S \<subseteq> H_arbitrary_Henkin \<Gamma> S bodies formulas"
proof -
  have base: "H_rename_constants H_original_name ` S \<subseteq> H_arbitrary_witness_limit \<Gamma> S bodies"
    by (rule H_arbitrary_witness_limit_extends)
  have limit_subset: "H_arbitrary_witness_limit \<Gamma> S bodies \<subseteq> H_arbitrary_Henkin \<Gamma> S bodies formulas"
    unfolding H_arbitrary_Henkin_def by (rule H_lindenbaum_extension_extends)
  show ?thesis by (rule subset_trans[OF base limit_subset])
qed

lemma H_arbitrary_Henkin_witnessed:
  assumes "typed_theory \<Gamma> S" and "H_consistent \<Gamma> S"
    and "enumerates_witness_bodies \<Gamma> bodies" and "enumerates_formulas \<Gamma> formulas"
  shows "Henkin_witnessed \<Gamma> (H_arbitrary_Henkin \<Gamma> S bodies formulas)"
  by (rule H_Henkin_theory_witnessed[OF H_arbitrary_Henkin_theory[OF assms]])

theorem H_arbitrary_Henkin_extension_exists:
  assumes typed: "typed_theory \<Gamma> S" and consistent: "H_consistent \<Gamma> S"
  obtains U where "H_Henkin_theory \<Gamma> U" and "H_rename_constants H_original_name ` S \<subseteq> U"
proof -
  obtain bodies where bodies: "enumerates_witness_bodies \<Gamma> bodies"
    using enumerates_witness_bodies_exists by blast
  obtain formulas where formulas: "enumerates_formulas \<Gamma> formulas"
    using enumerates_formulas_exists by blast
  let ?U = "H_arbitrary_Henkin \<Gamma> S bodies formulas"
  have henkin_U: "H_Henkin_theory \<Gamma> ?U" by (rule H_arbitrary_Henkin_theory[OF typed consistent bodies formulas])
  have extends: "H_rename_constants H_original_name ` S \<subseteq> ?U" by (rule H_arbitrary_Henkin_extends)
  show ?thesis by (rule that[where U="?U", OF henkin_U extends])
qed

text \<open>
  No finiteness assumption on S occurs in these results.  Only the
  difference between each finite stage and its initial renamed theory is
  finite.  Obtaining a model of the original unrenamed sentences still
  requires pulling the interpretation of constants back along the original
  namespace embedding.
\<close>

end
