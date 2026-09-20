theory Goodman_M5_Nested_Collision
  imports Goodman_M5_Object_Transfer
begin

section \<open>The corrected collision input has one additional necessity operator\<close>

text \<open>
  Goodman's notes, pp. 5–6, propose the inputs NC(r) and truth for
  F(p) = (p ↔ NC(p)). The exact-model counterexample shows that this pair
  does not collide under a merely local fun′(r) hypothesis. We keep F but
  replace the first input by q = NC(□r). Literally q = □□r ∨ □¬□r;
  replacing its first disjunct by □r uses S4, not syntactic equality.

  The proof below establishes q ↔ NC(q), and consequently Fq = F⊤, with
  NO added axioms. Only afterward do we assume fun′(r) locally to establish
  q ≠ ⊤. Equivalence and Necessitation are never applied under that temporary
  hypothesis. This is an object-language repair, not the separate semantic
  collision at punctured truth and not an appeal to an inconsistent stock.
\<close>

definition gi_M5_nested_input where
  "gi_M5_nested_input r = pp_noncontingent (ObjBox r)"

definition gi_M5_nested_result where
  "gi_M5_nested_result r = gi_M5_collision_result (ObjBox r)"

lemma gi_M5_nested_input_type:
  "\<Gamma> \<turnstile> r : Prop \<Longrightarrow> \<Gamma> \<turnstile> gi_M5_nested_input r : Prop"
  unfolding gi_M5_nested_input_def by (rule typed_pp_noncontingent, rule typed_ObjBox; assumption)

section \<open>Small propositional proof-combination lemmas\<close>

lemma gi_M5_PC1:
  assumes da: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A" and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<forall>v. prop_eval v A \<longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
proof -
  have at: "\<Gamma> \<turnstile> A : Prop" by (rule CEV_axiom_proves_formula[OF da])
  have rule: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A C"
    by (rule CEVp_M5_propositional[OF has_type.Imp[OF at ct]]; use taut in auto)
  show ?thesis by (rule CEV_axiom_proves.MP[OF da rule])
qed

lemma gi_M5_PC2:
  assumes da: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A" and db: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<forall>v. prop_eval v A \<longrightarrow> prop_eval v B \<longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C"
proof -
  have pair: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B" by (rule CEV_axiom_conj_intro[OF da db])
  show ?thesis by (rule gi_M5_PC1[OF pair ct]; use taut in auto)
qed

lemma gi_M5_PC3:
  assumes da: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A" and db: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
    and dc: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ C" and dt: "\<Gamma> \<turnstile> D : Prop"
    and taut: "\<forall>v. prop_eval v A \<longrightarrow> prop_eval v B \<longrightarrow> prop_eval v C \<longrightarrow> prop_eval v D"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ D"
proof -
  have pair: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Conj A B" by (rule CEV_axiom_conj_intro[OF da db])
  show ?thesis by (rule gi_M5_PC2[OF pair dc dt]; use taut in auto)
qed

lemma gi_M5_local_PC2:
  assumes da: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and db: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B" and ct: "\<Gamma> \<turnstile> C : Prop"
    and taut: "\<forall>v. prop_eval v A \<longrightarrow> prop_eval v B \<longrightarrow> prop_eval v C"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C"
proof -
  have at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    by (rule CEV_axiom_from_formula[OF da], rule CEV_axiom_from_formula[OF db])
  have global: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp B C)"
    by (rule CEVp_M5_propositional[OF has_type.Imp[OF at has_type.Imp[OF bt ct]]]; use taut in auto)
  have step: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp B C"
    by (rule CEV_axiom_from.MP[OF da CEV_axiom_from.Theorem[OF global]])
  show ?thesis by (rule CEV_axiom_from.MP[OF db step])
qed

lemma gi_M5_local_PC3:
  assumes da: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
    and db: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
    and dc: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s C" and dt: "\<Gamma> \<turnstile> D : Prop"
    and taut: "\<forall>v. prop_eval v A \<longrightarrow> prop_eval v B \<longrightarrow> prop_eval v C \<longrightarrow> prop_eval v D"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s D"
proof -
  have pair: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj A B"
    by (rule CEV_axiom_from_conj_intro[OF da db])
  show ?thesis by (rule gi_M5_local_PC2[OF pair dc dt]; use taut in auto)
qed

section \<open>S4 makes the nested input stable and dense\<close>

lemma gi_M5_box_mono:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    and implication: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox A) (ObjBox B)"
proof -
  have boxed: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjBox (Imp A B)" by (rule CEV_axiom_necessitation[OF implication])
  have K: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (Imp A B)) (Imp (ObjBox A) (ObjBox B))"
    using CEV_axiom_proves.Base[OF CEV_modal_K[OF at bt]] by (simp only: modal_K_def)
  show ?thesis by (rule CEV_axiom_proves.MP[OF boxed K])
qed

lemma gi_M5_modal_T:
  "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox A) A"
  using CEV_axiom_proves.Base[OF CEV_modal_T] by (simp only: modal_T_def)

lemma gi_M5_modal_four:
  "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox A) (ObjBox (ObjBox A))"
  using CEV_axiom_proves.Base[OF CEV_modal_4] by (simp only: modal_4_def)

lemma gi_M5_box_branch_stable:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and qt: "\<Gamma> \<turnstile> Q : Prop"
    and branch: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox A) Q"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox A) (ObjBox Q)"
  by (rule CEV_axiom_imp_trans_plus[OF typed_ObjBox[OF at] typed_ObjBox[OF typed_ObjBox[OF at]]
    typed_ObjBox[OF qt] gi_M5_modal_four[OF at] gi_M5_box_mono[OF typed_ObjBox[OF at] qt branch]])

theorem gi_M5_nested_stable:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (gi_M5_nested_input r) (ObjBox (gi_M5_nested_input r))"
proof -
  let ?q = "gi_M5_nested_input r"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have bt: "\<Gamma> \<turnstile> ObjBox r : Prop" by (rule typed_ObjBox[OF rt])
  have nt: "\<Gamma> \<turnstile> Neg (ObjBox r) : Prop" by (rule has_type.Neg[OF bt])
  have left: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (ObjBox r)) ?q"
    by (rule CEVp_M5_propositional[OF has_type.Imp[OF typed_ObjBox[OF bt] qt]];
      simp add: gi_M5_nested_input_def pp_noncontingent_def)
  have right: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (Neg (ObjBox r))) ?q"
    by (rule CEVp_M5_propositional[OF has_type.Imp[OF typed_ObjBox[OF nt] qt]];
      simp add: gi_M5_nested_input_def pp_noncontingent_def)
  have left_box: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (ObjBox r)) (ObjBox ?q)"
    by (rule gi_M5_box_branch_stable[OF bt qt left])
  have right_box: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (Neg (ObjBox r))) (ObjBox ?q)"
    by (rule gi_M5_box_branch_stable[OF nt qt right])
  show ?thesis by (rule gi_M5_PC2[OF left_box right_box has_type.Imp[OF qt typed_ObjBox[OF qt]]];
    simp only: gi_M5_nested_input_def pp_noncontingent_def prop_eval.simps; blast)
qed

theorem gi_M5_nested_dense:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (ObjBox (Neg (gi_M5_nested_input r)))"
proof -
  let ?q = "gi_M5_nested_input r"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have bt: "\<Gamma> \<turnstile> ObjBox r : Prop" by (rule typed_ObjBox[OF rt])
  have four: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox r) (ObjBox (ObjBox r))"
    by (rule gi_M5_modal_four[OF rt])
  have neg_q: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Neg ?q) (Neg (ObjBox r))"
    by (rule gi_M5_PC1[OF four has_type.Imp[OF has_type.Neg[OF qt] has_type.Neg[OF bt]]];
      simp only: gi_M5_nested_input_def pp_noncontingent_def prop_eval.simps; blast)
  have boxed: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (Neg ?q)) (ObjBox (Neg (ObjBox r)))"
    by (rule gi_M5_box_mono[OF has_type.Neg[OF qt] has_type.Neg[OF bt] neg_q])
  have t: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (ObjBox (Neg ?q)) (Neg ?q)"
    by (rule gi_M5_modal_T[OF has_type.Neg[OF qt]])
  show ?thesis by (rule gi_M5_PC2[OF boxed t has_type.Neg[OF typed_ObjBox[OF has_type.Neg[OF qt]]]];
    simp only: gi_M5_nested_input_def pp_noncontingent_def prop_eval.simps; blast)
qed

theorem gi_M5_nested_NC_equivalent:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (gi_M5_nested_input r \<longleftrightarrow>\<^sub>o pp_noncontingent (gi_M5_nested_input r))"
proof -
  have qt: "\<Gamma> \<turnstile> gi_M5_nested_input r : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have nt: "\<Gamma> \<turnstile> pp_noncontingent (gi_M5_nested_input r) : Prop" by (rule typed_pp_noncontingent[OF qt])
  have result_type: "\<Gamma> \<turnstile> (gi_M5_nested_input r \<longleftrightarrow>\<^sub>o pp_noncontingent (gi_M5_nested_input r)) : Prop"
    by (intro has_type.Conj has_type.Imp qt nt)
  show ?thesis by (rule gi_M5_PC3[OF gi_M5_nested_stable[OF rt] gi_M5_modal_T[OF qt]
    gi_M5_nested_dense[OF rt] result_type]; simp only: pp_noncontingent_def prop_eval.simps; blast)
qed

section \<open>The output identity is proved with an empty added stock\<close>

lemma gi_M5_nested_F_true:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ App pp_M5_collision_operator (gi_M5_nested_input r)"
proof -
  have qt: "\<Gamma> \<turnstile> gi_M5_nested_input r : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have nt: "\<Gamma> \<turnstile> pp_noncontingent (gi_M5_nested_input r) : Prop" by (rule typed_pp_noncontingent[OF qt])
  have bt: "\<Gamma> \<turnstile> (gi_M5_nested_input r \<longleftrightarrow>\<^sub>o pp_noncontingent (gi_M5_nested_input r)) : Prop"
    by (intro has_type.Conj has_type.Imp qt nt)
  show ?thesis by (rule CEVp_M5_app_true[OF typed_pp_M5_collision_operator qt bt
    pp_M5_collision_operator_beta gi_M5_nested_NC_equivalent[OF rt]])
qed

lemma gi_M5_F_truth_true:
  "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ App pp_M5_collision_operator ObjTrue"
proof -
  have boxed: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ ObjBox ObjTrue"
    by (rule CEV_axiom_necessitation[OF CEV_axiom_proves_ObjTrue])
  have nc: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ pp_noncontingent ObjTrue"
    by (rule gi_M5_PC1[OF boxed typed_pp_noncontingent[OF typed_ObjTrue]]; simp add: pp_noncontingent_def)
  have bt: "\<Gamma> \<turnstile> (ObjTrue \<longleftrightarrow>\<^sub>o pp_noncontingent ObjTrue) : Prop"
    by (intro has_type.Conj has_type.Imp typed_ObjTrue typed_pp_noncontingent)
  have body: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ (ObjTrue \<longleftrightarrow>\<^sub>o pp_noncontingent ObjTrue)"
    by (rule gi_M5_PC2[OF CEV_axiom_proves_ObjTrue nc bt]; simp)
  show ?thesis by (rule CEVp_M5_app_true[OF typed_pp_M5_collision_operator typed_ObjTrue bt pp_M5_collision_operator_beta body])
qed

theorem gi_M5_nested_outputs_equal:
  assumes rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop
    (App pp_M5_collision_operator (gi_M5_nested_input r)) (App pp_M5_collision_operator ObjTrue)"
proof -
  have ft: "\<Gamma> \<turnstile> pp_M5_collision_operator : Arr Prop Prop"
    using typed_pp_M5_collision_operator[where \<Gamma>=\<Gamma>] by (simp only: pp_unary_ty_def)
  have lt: "\<Gamma> \<turnstile> App pp_M5_collision_operator (gi_M5_nested_input r) : Prop"
    by (rule has_type.App[OF ft gi_M5_nested_input_type[OF rt]])
  have tt: "\<Gamma> \<turnstile> App pp_M5_collision_operator ObjTrue : Prop" by (rule has_type.App[OF ft typed_ObjTrue])
  have both: "\<Gamma> ; {} \<turnstile>\<^sub>CEV\<^sup>+
    (App pp_M5_collision_operator (gi_M5_nested_input r) \<longleftrightarrow>\<^sub>o App pp_M5_collision_operator ObjTrue)"
    by (rule CEV_axiom_biconditional_of_theorems[OF gi_M5_nested_F_true[OF rt] gi_M5_F_truth_true])
  show ?thesis by (rule CEV_axiom_zeroary_equivalence[OF lt tt both])
qed

section \<open>Only the inequality of inputs uses local fun′\<close>

lemma gi_M5_nested_input_false_locally:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (gi_M5_nested_input r)"
proof -
  let ?F = "pp_fun_prime r"
  let ?B = "ObjBox r"
  let ?q = "gi_M5_nested_input r"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" by (rule typed_pp_fun_prime[OF rt])
  have bt: "\<Gamma> \<turnstile> ?B : Prop" by (rule typed_ObjBox[OF rt])
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have fp: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F" by (rule CEV_axiom_from.Assumption; simp add: ft)
  have not_box_rule: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Neg ?B)"
    using CEV_fun_prime_neq_ObjTrue[OF core rt] by (simp only: ObjBox_def)
  have not_box: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?B"
    by (rule CEV_axiom_from.MP[OF fp CEV_axiom_from.Theorem[OF not_box_rule]])
  have pure_top_member: "pp_pure Prop ObjTrue \<in> T"
    using core Bacon_PP_Diagonal.pp_ObjTrue_purity_axiom unfolding pp_T2_min_axioms_def by blast
  have pure_top: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjTrue"
    by (rule CEV_axiom_proves.Axiom[OF pure_top_member typed_pp_pure[OF typed_ObjTrue]])
  have attainment: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?F (Imp (pp_pure Prop ObjTrue) (ObjDiamond ?B))"
    using CEV_Goodman_T2c_parameter[OF core rt typed_ObjTrue] by (simp only: ObjBox_def)
  have step: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (pp_pure Prop ObjTrue) (ObjDiamond ?B)"
    by (rule CEV_axiom_from.MP[OF fp CEV_axiom_from.Theorem[OF attainment]])
  have possible: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjDiamond ?B"
    by (rule CEV_axiom_from.MP[OF CEV_axiom_from.Theorem[OF pure_top] step])
  have t: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (ObjBox ?B) ?B"
    by (rule CEV_axiom_from.Theorem[OF gi_M5_modal_T[OF bt]])
  show ?thesis by (rule gi_M5_local_PC3[OF not_box possible t has_type.Neg[OF qt]];
    simp only: gi_M5_nested_input_def pp_noncontingent_def ObjDiamond_def prop_eval.simps; blast)
qed

theorem gi_M5_nested_local_collision:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r) (gi_M5_nested_result r)"
proof -
  let ?q = "gi_M5_nested_input r"
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have ft: "\<Gamma> \<turnstile> pp_fun_prime r : Prop" by (rule typed_pp_fun_prime[OF rt])
  have not_q: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?q"
    by (rule gi_M5_nested_input_false_locally[OF core rt])
  have t: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (ObjBox ?q) ?q"
    by (rule CEV_axiom_from.Theorem[OF gi_M5_modal_T[OF qt]])
  have not_box: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (ObjBox ?q)"
    by (rule gi_M5_local_PC2[OF not_q t has_type.Neg[OF typed_ObjBox[OF qt]]]; simp)
  have unequal: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ?q ObjTrue)"
    using not_box by (simp only: ObjBox_def)
  have global_equal: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop
    (App pp_M5_collision_operator ?q) (App pp_M5_collision_operator ObjTrue)"
    by (rule CEV_axiom_proves_mono[OF gi_M5_nested_outputs_equal[OF rt]]; simp)
  have local_equal: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop
    (App pp_M5_collision_operator ?q) (App pp_M5_collision_operator ObjTrue)"
    by (rule CEV_axiom_from.Theorem[OF global_equal])
  have result: "\<Gamma> ; T ; {pp_fun_prime r} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_M5_nested_result r"
    unfolding gi_M5_nested_result_def gi_M5_collision_result_def gi_M5_nested_input_def[symmetric]
    by (rule CEV_axiom_from_conj_intro[OF unequal local_equal])
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF ft result])
qed

theorem gi_M5_nested_local_nonreversibility:
  assumes core: "pp_T2_min_axioms \<subseteq> T" and rt: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_fun_prime r) (Neg (pp_reversible pp_M5_collision_operator))"
proof -
  let ?q = "gi_M5_nested_input r"
  let ?F = "pp_fun_prime r"
  have ft: "\<Gamma> \<turnstile> ?F : Prop" by (rule typed_pp_fun_prime[OF rt])
  have qt: "\<Gamma> \<turnstile> ?q : Prop" by (rule gi_M5_nested_input_type[OF rt])
  have rt': "\<Gamma> \<turnstile> pp_reversible pp_M5_collision_operator : Prop"
    by (rule typed_pp_reversible[OF typed_pp_M5_collision_operator])
  have fp: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F" by (rule CEV_axiom_from.Assumption; simp add: ft)
  have result: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s gi_M5_nested_result r"
    by (rule CEV_axiom_from.MP[OF fp CEV_axiom_from.Theorem[OF gi_M5_nested_local_collision[OF core rt]]])
  have pair: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Conj
    (Neg (Eq Prop ?q ObjTrue))
    (Eq Prop (App pp_M5_collision_operator ?q) (App pp_M5_collision_operator ObjTrue))"
    using result by (simp only: gi_M5_nested_result_def gi_M5_collision_result_def gi_M5_nested_input_def)
  have unequal: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ?q ObjTrue)"
    by (rule CEV_axiom_from_conj_left[OF pair])
  have equal: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Eq Prop (App pp_M5_collision_operator ?q) (App pp_M5_collision_operator ObjTrue)"
    by (rule CEV_axiom_from_conj_right[OF pair])
  have injective: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Imp (pp_reversible pp_M5_collision_operator)
      (Imp (Eq Prop (App pp_M5_collision_operator ?q) (App pp_M5_collision_operator ObjTrue)) (Eq Prop ?q ObjTrue))"
    by (rule CEV_axiom_from.Theorem[OF CEV_M5_reversible_injective[OF typed_pp_M5_collision_operator qt typed_ObjTrue]])
  have nonrev: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (pp_reversible pp_M5_collision_operator)"
    by (rule gi_M5_local_PC3[OF unequal equal injective has_type.Neg[OF rt']]; simp only: prop_eval.simps; blast)
  show ?thesis by (rule CEV_axiom_from_singleton_imp[OF ft nonrev])
qed

section \<open>Transfer the repaired local claims to the restricted native signature\<close>

theorem gi_M5_nested_native_collision_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted cmap gb_signature (Imp (pp_fun_prime r) (gi_M5_nested_result r))"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns cmap (Imp (pp_fun_prime r) (gi_M5_nested_result r)))"
  by (rule gi_T2_min_native_preservation[OF rich names gi_M5_nested_local_collision[OF subset_refl rt]
    chart distinct admitted])

theorem gi_M5_nested_native_nonreversibility_translated:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap"
    and rt: "\<Gamma> \<turnstile> r : Prop" and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and admitted: "gi_constants_admitted cmap gb_signature
      (Imp (pp_fun_prime r) (Neg (pp_reversible pp_M5_collision_operator)))"
  shows "goodman_book_proves gb_signature G (gb_T2_min_axioms G)
    (gi_to_book G ns cmap (Imp (pp_fun_prime r) (Neg (pp_reversible pp_M5_collision_operator))))"
  by (rule gi_T2_min_native_preservation[OF rich names gi_M5_nested_local_nonreversibility[OF subset_refl rt]
    chart distinct admitted])

text \<open>
  The repaired pair is NC(□r), ⊤. The output equality is separately certified
  with the empty added stock, and the input inequality is proved using a
  local fun′ assumption under MP-only temporary reasoning. Thus the new
  implication does not reuse the old globally assumed fun′ axiom. Neither
  the validity nor the consistency of a PP extension is inferred here.
\<close>

end
