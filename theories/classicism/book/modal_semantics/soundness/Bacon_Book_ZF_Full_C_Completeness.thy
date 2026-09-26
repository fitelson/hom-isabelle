theory Bacon_Book_ZF_Full_C_Completeness
  imports Bacon_Book_ZF_Full_C_Soundness
    Bacon_Book_ZF_Modal_Representation.Bacon_Book_ZF_Countable_Nontrivial_Existence
begin

section \<open>Modal consequence, soundness and completeness of full-type Classicism\<close>

text \<open>
  This theory closes the loop. Modal consequence for full-type C is
  truth at the root of every independent nontrivial book modal model
  with an admissible interpretation that satisfies the premises at
  the root. The soundness half is full_C_theory_valid_at_root; the
  completeness half combines the syntactic universal-closure and
  closed-refutation results for full-C theory derivability with the
  countable nontrivial model-existence theorem and a semantic
  universal-closure bridge proved here: truth of the universal
  closure at a world under one typed assignment is validity of the
  formula at that world under every typed assignment. The signature
  must be countably declared at each type, as in the existence
  theorem; the variable stock must be rich. The consistency
  characterisation (consistent iff satisfiable) is the same
  combination without a conclusion formula.
\<close>

context book_ZF_modal_interpretation
begin

subsection \<open>Semantic universal closure\<close>

theorem truth_all_list:
  assumes al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_all_list G ns A) \<longleftrightarrow>
    (\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> set ns \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A)"
  using typed
proof (induction ns arbitrary: g)
  case Nil
  have "book_ZF_truth_at J w g A \<longleftrightarrow>
    (\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> set [] \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A)"
  proof (rule iffI)
    assume base: "book_ZF_truth_at J w g A"
    show "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> set [] \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A"
    proof (intro allI impI)
      fix h assume "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> set [] \<longrightarrow> h n = g n)"
      then have "h = g" by (intro ext) simp
      then show "book_ZF_truth_at J w h A" using base by simp
    qed
  next
    assume "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> set [] \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A"
    then show "book_ZF_truth_at J w g A" using Nil by blast
  qed
  then show ?case by (simp only: book_all_list.simps)
next
  case (Cons n ns)
  have inner: "book_theory_formula signature G (book_all_list G ns A)" by (rule book_all_list_language[OF al])
  have step: "book_ZF_truth_at J w g (book_all_list G (n # ns) A) \<longleftrightarrow>
    (\<forall>a\<in>explode (D (G n) w). \<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and>
      (\<forall>m. m \<notin> set ns \<longrightarrow> h m = (g(n := a)) m) \<longrightarrow> book_ZF_truth_at J w h A)"
    by (simp only: book_all_list.simps truth_all[OF inner ww Cons.prems]; rule ball_cong[OF refl];
      rule Cons.IH; rule book_env_update[OF Cons.prems]; assumption)
  show ?case
  proof (simp only: step, rule iffI)
    assume each: "\<forall>a\<in>explode (D (G n) w). \<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and>
      (\<forall>m. m \<notin> set ns \<longrightarrow> h m = (g(n := a)) m) \<longrightarrow> book_ZF_truth_at J w h A"
    show "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>m. m \<notin> set (n # ns) \<longrightarrow> h m = g m) \<longrightarrow>
      book_ZF_truth_at J w h A"
    proof (intro allI impI, elim conjE)
      fix h assume ht: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
        and agree: "\<forall>m. m \<notin> set (n # ns) \<longrightarrow> h m = g m"
      have hn: "h n \<in> explode (D (G n) w)" using ht by (simp only: book_env_typed_def)
      have agree': "\<forall>m. m \<notin> set ns \<longrightarrow> h m = (g(n := h n)) m" using agree by auto
      show "book_ZF_truth_at J w h A" using each hn ht agree' by blast
    qed
  next
    assume whole: "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>m. m \<notin> set (n # ns) \<longrightarrow> h m = g m) \<longrightarrow>
      book_ZF_truth_at J w h A"
    show "\<forall>a\<in>explode (D (G n) w). \<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and>
      (\<forall>m. m \<notin> set ns \<longrightarrow> h m = (g(n := a)) m) \<longrightarrow> book_ZF_truth_at J w h A"
    proof (intro ballI allI impI, elim conjE)
      fix a h assume ht: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
        and agree: "\<forall>m. m \<notin> set ns \<longrightarrow> h m = (g(n := a)) m"
      have agree': "\<forall>m. m \<notin> set (n # ns) \<longrightarrow> h m = g m" using agree by auto
      show "book_ZF_truth_at J w h A" using whole ht agree' by blast
    qed
  qed
qed

theorem truth_universal_closure:
  assumes al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_universal_closure G A) \<longleftrightarrow> book_ZF_valid_at D G J w A"
proof -
  have fv: "set (sorted_list_of_set (named_fv A)) = named_fv A" by (rule set_sorted_list_of_set[OF named_fv_finite])
  have closure: "book_ZF_truth_at J w g (book_universal_closure G A) \<longleftrightarrow>
    (\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> named_fv A \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A)"
    unfolding book_universal_closure_def by (simp only: truth_all_list[OF al ww typed] fv)
  show ?thesis
  proof (simp only: closure, rule iffI)
    assume agreeing: "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> named_fv A \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A"
    show "book_ZF_valid_at D G J w A"
    proof (rule book_ZF_valid_atI)
      fix h assume ht: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
      let ?k = "\<lambda>n. if n \<in> named_fv A then h n else g n"
      have kt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?k"
        using ht typed unfolding book_env_typed_def by simp
      have kg: "\<forall>n. n \<notin> named_fv A \<longrightarrow> ?k n = g n" by simp
      have truth_k: "book_ZF_truth_at J w ?k A" using agreeing kt kg by blast
      have same: "J w ?k A = J w h A" by (rule denote_coincidence[OF al ww kt ht]) simp
      show "book_ZF_truth_at J w h A" using truth_k unfolding book_ZF_truth_at_def same .
    qed
  next
    assume valid: "book_ZF_valid_at D G J w A"
    show "\<forall>h. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h \<and> (\<forall>n. n \<notin> named_fv A \<longrightarrow> h n = g n) \<longrightarrow>
      book_ZF_truth_at J w h A"
      using book_ZF_valid_atD[OF valid] by blast
  qed
qed

end

subsection \<open>Modal consequence over the nontrivial class\<close>

definition book_ZF_full_C_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c, book_minimal_logical) named_term set \<Rightarrow> ('c, book_minimal_logical) named_term \<Rightarrow> bool" where
  "book_ZF_full_C_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>W R root D i I J.
      book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<longrightarrow>
      book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<longrightarrow>
      book_ZF_satisfies D G J root S \<longrightarrow> book_ZF_formula_valid D G J root A)"

definition book_ZF_full_C_satisfiable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c, book_minimal_logical) named_term set \<Rightarrow> bool" where
  "book_ZF_full_C_satisfiable \<Sigma> G S \<longleftrightarrow>
    (\<exists>W R root D i I J.
      book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
      book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
      book_ZF_satisfies D G J root S)"

subsection \<open>Soundness\<close>

theorem book_full_C_theory_sound:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable \<Sigma> G S A"
  shows "book_ZF_full_C_consequence \<Sigma> G S A"
proof (unfold book_ZF_full_C_consequence_def, intro allI impI)
  fix W R root D i I J
  assume model: "book_ZF_nontrivial_modal_model W R root D i \<Sigma> I"
    and interp: "book_ZF_modal_interpretation W R root D i \<Sigma> I G J"
    and satisfied: "book_ZF_satisfies D G J root S"
  interpret M: book_ZF_nontrivial_modal_interpretation W R root D i \<Sigma> I G J
    by (rule book_ZF_nontrivial_modal_interpretation.intro[OF model interp])
  show "book_ZF_formula_valid D G J root A"
    by (rule M.full_C_theory_valid_at_root[OF rich derivation satisfied])
qed

theorem book_full_C_satisfiable_consistent:
  assumes rich: "sg_rich G" and satisfiable: "book_ZF_full_C_satisfiable \<Sigma> G S"
  shows "book_full_C_theory_consistent \<Sigma> G S"
proof -
  obtain W R root D i I J where
    model: "book_ZF_nontrivial_modal_model W R root D i \<Sigma> I"
    and interp: "book_ZF_modal_interpretation W R root D i \<Sigma> I G J"
    and satisfied: "book_ZF_satisfies D G J root S"
    using satisfiable unfolding book_ZF_full_C_satisfiable_def by blast
  interpret M: book_ZF_nontrivial_modal_interpretation W R root D i \<Sigma> I G J
    by (rule book_ZF_nontrivial_modal_interpretation.intro[OF model interp])
  show ?thesis by (rule M.satisfiable_theory_consistent[OF rich satisfied])
qed

subsection \<open>Completeness from model existence\<close>

theorem book_full_C_theory_complete_from_existence:
  assumes rich: "sg_rich G"
    and existence: "\<And>T. (\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G B) \<Longrightarrow>
      book_full_C_theory_consistent \<Sigma> G T \<Longrightarrow> book_ZF_full_C_satisfiable \<Sigma> G T"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and consequence: "book_ZF_full_C_consequence \<Sigma> G S A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof (rule ccontr)
  assume missing: "\<not> book_full_C_theory_derivable \<Sigma> G S A"
  let ?U = "book_universal_closure G A"
  have ul: "book_theory_formula \<Sigma> G ?U" by (rule book_universal_closure_language[OF al])
  have uc: "named_fv ?U = {}" by (rule book_universal_closure_closed)
  have missing_U: "\<not> book_full_C_theory_derivable \<Sigma> G S ?U"
    using missing book_full_C_theory_universal_closure_iff[OF rich al] by blast
  let ?T = "insert (book_not G ?U) S"
  have consistent: "book_full_C_theory_consistent \<Sigma> G ?T"
    by (rule book_full_C_theory_consistent_negative_extension[OF rich ul uc missing_U])
  have tl: "book_theory_formula \<Sigma> G B" if member: "B \<in> ?T" for B
    using member language book_not_language[OF rich ul] by blast
  obtain W R root D i I J where
    model: "book_ZF_nontrivial_modal_model W R root D i \<Sigma> I"
    and interp: "book_ZF_modal_interpretation W R root D i \<Sigma> I G J"
    and satisfied_T: "book_ZF_satisfies D G J root ?T"
    using existence[OF tl consistent] unfolding book_ZF_full_C_satisfiable_def by blast
  interpret M: book_ZF_nontrivial_modal_interpretation W R root D i \<Sigma> I G J
    by (rule book_ZF_nontrivial_modal_interpretation.intro[OF model interp])
  have satisfied_S: "book_ZF_satisfies D G J root S"
    using satisfied_T unfolding book_ZF_satisfies_def by blast
  have negation_valid: "book_ZF_formula_valid D G J root (book_not G ?U)"
    using satisfied_T unfolding book_ZF_satisfies_def by blast
  have valid_A: "book_ZF_valid_at D G J root A"
    using consequence model interp satisfied_S
    unfolding book_ZF_full_C_consequence_def book_ZF_valid_at_root by blast
  obtain g where typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> root)) G g"
    using M.typed_assignment_exists[OF M.root_world] by blast
  have true_U: "book_ZF_truth_at J root g ?U"
    using valid_A by (simp only: M.truth_universal_closure[OF al M.root_world typed])
  have true_not_U: "book_ZF_truth_at J root g (book_not G ?U)"
    using negation_valid typed unfolding book_ZF_formula_valid_def by blast
  have false_U: "\<not> book_ZF_truth_at J root g ?U"
    using true_not_U M.truth_not_classical[OF rich ul M.root_world typed M.bottom_false_at[OF rich M.root_world typed]]
    by blast
  show False using true_U false_U by contradiction
qed

subsection \<open>Completeness for countably declared signatures\<close>

theorem book_full_C_theory_complete:
  assumes rich: "sg_rich G"
    and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and consequence: "book_ZF_full_C_consequence \<Sigma> G S A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof (rule book_full_C_theory_complete_from_existence[OF rich _ language al consequence])
  fix T assume tl: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G B" and tc: "book_full_C_theory_consistent \<Sigma> G T"
  show "book_ZF_full_C_satisfiable \<Sigma> G T"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_countable_nontrivial_modal_model_exists[OF rich small tl tc])
qed

theorem book_full_C_theory_derivable_iff_consequence:
  assumes rich: "sg_rich G"
    and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_ZF_full_C_consequence \<Sigma> G S A"
  using book_full_C_theory_sound[OF rich] book_full_C_theory_complete[OF rich small language al] by blast

theorem book_full_C_theory_consistent_iff_satisfiable:
  assumes rich: "sg_rich G"
    and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow> book_ZF_full_C_satisfiable \<Sigma> G S"
proof
  assume consistent: "book_full_C_theory_consistent \<Sigma> G S"
  show "book_ZF_full_C_satisfiable \<Sigma> G S"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_countable_nontrivial_modal_model_exists[OF rich small language consistent])
next
  assume satisfiable: "book_ZF_full_C_satisfiable \<Sigma> G S"
  show "book_full_C_theory_consistent \<Sigma> G S" by (rule book_full_C_satisfiable_consistent[OF rich satisfiable])
qed

text \<open>
  Scope. Both equivalences are for the book's full simple types over
  the minimal primitive language in HOL-ZF, a rich variable stock, and
  a signature that is countable at every type. The model class is the
  nontrivial refinement of Definition 18.1 (inhabited domains and a
  false proposition at every world); soundness alone holds for it and
  consistency-from-satisfiability needs it. The premise set is
  satisfied at the root only (local consequence). The countability
  premise is inherited from book_full_C_countable_nontrivial_modal_model_exists,
  the existence theorem used here; the small-carrier and ZF-small
  declared-union versions, which cover uncountably declared signatures,
  are Bacon_Book_ZF_Full_C_Small_Carrier_Completeness and
  Bacon_Book_ZF_Full_C_Declared_Names_Completeness in the same session.
\<close>

end
