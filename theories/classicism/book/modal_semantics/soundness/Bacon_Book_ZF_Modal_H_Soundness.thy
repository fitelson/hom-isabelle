theory Bacon_Book_ZF_Modal_H_Soundness
  imports Bacon_Book_ZF_Modal_Conversion
begin

section \<open>The H rules preserve truth at any fixed world of a modal model\<close>

text \<open>
  Validity at a world w is truth under every typed assignment at w. Each
  rule of the Chapter 5 calculus (book_theory_derivable) preserves this
  local validity at any fixed world of any structural modal model, with
  the premises of a theory derivation assumed valid at that same world.
  This is the H component of Theorem 18.4's soundness direction for
  Bacon's modal models; it is separate from the H results for the
  general models of Chapters 14–15. The PC3 case handles the possible
  truth of bottom explicitly: if bottom is true at w, every formula is.
\<close>

definition book_ZF_valid_at ::
  "book_ZF_domains \<Rightarrow> sgcontext \<Rightarrow> (ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> 'c book_named_term \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_ZF_valid_at D G J w A \<longleftrightarrow> (\<forall>g. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<longrightarrow> book_ZF_truth_at J w g A)"

lemma book_ZF_valid_atI:
  assumes "\<And>g. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g \<Longrightarrow> book_ZF_truth_at J w g A"
  shows "book_ZF_valid_at D G J w A"
  unfolding book_ZF_valid_at_def using assms by blast

lemma book_ZF_valid_atD:
  assumes "book_ZF_valid_at D G J w A" and "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g A"
  using assms unfolding book_ZF_valid_at_def by blast

lemma book_ZF_valid_at_root:
  "book_ZF_valid_at D G J root A \<longleftrightarrow> book_ZF_formula_valid D G J root A"
  unfolding book_ZF_valid_at_def book_ZF_formula_valid_def ..

context book_ZF_modal_interpretation
begin

theorem PC1_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_imp A (book_imp B A))"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "book_ZF_truth_at J w g (book_imp A (book_imp B A))"
    by (simp only: truth_imp[OF al book_imp_language[OF bl al] ww typed] truth_imp[OF bl al ww typed]; blast)
qed

theorem PC2_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and cl: "book_theory_formula signature G C" and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have bcl: "book_theory_formula signature G (book_imp B C)" by (rule book_imp_language[OF bl cl])
  have abl: "book_theory_formula signature G (book_imp A B)" by (rule book_imp_language[OF al bl])
  have acl: "book_theory_formula signature G (book_imp A C)" by (rule book_imp_language[OF al cl])
  show "book_ZF_truth_at J w g (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
    by (simp only: truth_imp[OF book_imp_language[OF al bcl] book_imp_language[OF abl acl] ww typed]
      truth_imp[OF al bcl ww typed] truth_imp[OF bl cl ww typed] truth_imp[OF abl acl ww typed]
      truth_imp[OF al bl ww typed] truth_imp[OF al cl ww typed]; blast)
qed

theorem PC3_valid:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have nal: "book_theory_formula signature G (book_not G A)" and nbl: "book_theory_formula signature G (book_not G B)"
    by (rule book_not_language[OF rich al], rule book_not_language[OF rich bl])
  have outer: "book_ZF_truth_at J w g (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A)) \<longleftrightarrow>
    ((book_ZF_truth_at J w g (book_not G A) \<longrightarrow> book_ZF_truth_at J w g (book_not G B)) \<longrightarrow>
      (book_ZF_truth_at J w g B \<longrightarrow> book_ZF_truth_at J w g A))"
    by (simp only: truth_imp[OF book_imp_language[OF nal nbl] book_imp_language[OF bl al] ww typed]
      truth_imp[OF nal nbl ww typed] truth_imp[OF bl al ww typed])
  show "book_ZF_truth_at J w g (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
  proof (cases "book_ZF_truth_at J w g (book_bottom G)")
    case True
    show ?thesis by (rule bottom_true_everything[OF rich ww typed True _ typed];
      rule book_imp_language[OF book_imp_language[OF nal nbl] book_imp_language[OF bl al]])
  next
    case False
    show ?thesis unfolding outer
      by (simp only: truth_not_classical[OF rich al ww typed False] truth_not_classical[OF rich bl ww typed False]; blast)
  qed
qed

theorem UI_valid:
  assumes fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> Prop)"
    and al: "book_in_language book_minimal_logical_type UNIV signature G a \<sigma>"
    and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have quantified: "book_theory_formula signature G (NApp (NLogical (SBAll \<sigma>)) F)"
    by (rule book_language_App[OF book_all_operator_language fl])
  have inst_l: "book_theory_formula signature G (NApp F a)" by (rule book_language_App[OF fl al])
  have am: "J w g a \<in> explode (D \<sigma> w)" by (rule denote_type[OF ww al typed])
  have applied: "book_ZF_truth_at J w g (NApp F a) \<longleftrightarrow> Elem w (app (J w g F) (Opair w (J w g a)))"
    unfolding book_ZF_truth_at_def by (simp only: denote_application[OF ww fl al typed])
  show "book_ZF_truth_at J w g (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
    by (simp only: truth_imp[OF quantified inst_l ww typed] truth_all_predicate[OF fl ww typed] applied; intro impI;
      erule bspec[OF _ am])
qed

theorem Beta_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and step: "named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A"
    and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_imp A B)"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have equal: "J w g A = J w g B"
  proof (rule disjE[OF step])
    assume forward: "named_compatible_step named_beta_contract A B"
    show ?thesis by (rule denote_beta_step[OF forward al ww typed])
  next
    assume backward: "named_compatible_step named_beta_contract B A"
    show ?thesis by (rule denote_beta_step[OF backward bl ww typed, symmetric])
  qed
  show "book_ZF_truth_at J w g (book_imp A B)"
    by (simp only: truth_imp[OF al bl ww typed]; simp only: book_ZF_truth_at_def equal simp_thms)
qed

theorem Eta_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and step: "named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A"
    and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_imp A B)"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have equal: "J w g A = J w g B"
  proof (rule disjE[OF step])
    assume forward: "named_compatible_step named_eta_contract A B"
    show ?thesis by (rule denote_eta_step[OF forward al ww typed])
  next
    assume backward: "named_compatible_step named_eta_contract B A"
    show ?thesis by (rule denote_eta_step[OF backward bl ww typed, symmetric])
  qed
  show "book_ZF_truth_at J w g (book_imp A B)"
    by (simp only: truth_imp[OF al bl ww typed]; simp only: book_ZF_truth_at_def equal simp_thms)
qed

theorem MP_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W"
    and antecedent: "book_ZF_valid_at D G J w A" and conditional: "book_ZF_valid_at D G J w (book_imp A B)"
  shows "book_ZF_valid_at D G J w B"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "book_ZF_truth_at J w g B"
    using book_ZF_valid_atD[OF antecedent typed] book_ZF_valid_atD[OF conditional typed]
    by (simp only: truth_imp[OF al bl ww typed])
qed

theorem Gen_valid:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and fresh: "n \<notin> named_fv A" and ww: "w \<in> explode W"
    and conditional: "book_ZF_valid_at D G J w (book_imp A B)"
  shows "book_ZF_valid_at D G J w (book_imp A (book_all G n B))"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have each: "book_ZF_truth_at J w (g(n := a)) B"
    if premise: "book_ZF_truth_at J w g A" and am: "a \<in> explode (D (G n) w)" for a
  proof -
    have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(n := a))" by (rule book_env_update[OF typed am])
    have same: "book_ZF_truth_at J w (g(n := a)) A \<longleftrightarrow> book_ZF_truth_at J w g A"
      unfolding book_ZF_truth_at_def
      by (rule book_ZF_truth_at_transfer[unfolded book_ZF_truth_at_def]; rule denote_coincidence[OF al ww updated typed];
        insert fresh; auto)
    show ?thesis using book_ZF_valid_atD[OF conditional updated] premise
      by (simp only: truth_imp[OF al bl ww updated] same)
  qed
  show "book_ZF_truth_at J w g (book_imp A (book_all G n B))"
    by (simp only: truth_imp[OF al book_all_language[OF bl] ww typed] truth_all[OF bl ww typed]; intro impI ballI;
      rule each; assumption)
qed

theorem theory_derivable_valid_at:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W"
    and derivation: "book_theory_derivable signature G S A"
    and assumptions_valid: "\<And>B. B \<in> S \<Longrightarrow> book_ZF_valid_at D G J w B"
  shows "book_ZF_valid_at D G J w A"
  using derivation assumptions_valid
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule PC1_valid[OF PC1.hyps ww])
next
  case PC2
  show ?case by (rule PC2_valid[OF PC2.hyps ww])
next
  case PC3
  show ?case by (rule PC3_valid[OF rich PC3.hyps ww])
next
  case UI
  show ?case by (rule UI_valid[OF UI.hyps ww])
next
  case Beta
  show ?case by (rule Beta_valid[OF Beta.hyps ww])
next
  case Eta
  show ?case by (rule Eta_valid[OF Eta.hyps ww])
next
  case MP
  show ?case by (rule MP_valid[OF book_theory_derivable_language[OF MP.hyps(1) rich] MP.hyps(3) ww
    MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems]])
next
  case Gen
  show ?case by (rule Gen_valid[OF Gen.hyps(2,3,4) ww Gen.IH[OF Gen.prems]])
qed

theorem H_valid_at:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and theorem_H: "book_H signature G A"
  shows "book_ZF_valid_at D G J w A"
proof (rule theory_derivable_valid_at[OF rich ww])
  show "book_theory_derivable signature G {} A" using theorem_H by (simp only: book_H_iff_theory[OF rich])
qed simp

end

text \<open>
  These are local validity statements for one interpretation of one
  structural modal model at one world. They do not use nontriviality,
  countability, a canonical construction, or the MF/PE rules, and they
  do not by themselves establish anything about full-type C.
\<close>

end
