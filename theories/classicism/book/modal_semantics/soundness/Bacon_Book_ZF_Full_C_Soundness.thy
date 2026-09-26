theory Bacon_Book_ZF_Full_C_Soundness
  imports
    Bacon_Book_ZF_Modal_H_Soundness
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Nontrivial_Interpretation
begin

section \<open>Generic soundness of full-type Classicism for the nontrivial book modal models\<close>

text \<open>
  Full-type C (Chapter 8, endnote 5: H, all-type Modalized Functionality,
  and Propositional Equivalence) is sound for every independent
  nontrivial modal model with an admissible interpretation. The
  invariant is validity at every world under every typed assignment.
  PE needs it: the identity P =ₜ Q at w is equality of the two
  proposition values, which are future sets, and their members are
  the future worlds where P, Q are true under moved assignments.
  The identity and box clauses hold in every book modal model, so
  MF and PE are in fact valid in the structural class as well; the
  nontrivial locale is used here because the endpoint that matters,
  satisfiable-implies-consistent, needs a false proposition and an
  actual typed assignment at the root (docs/MODAL_NONTRIVIALITY.md).
  The single-world all-true regression shows the endpoint fails
  without that refinement.
\<close>

definition book_ZF_valid_everywhere ::
  "ZF \<Rightarrow> book_ZF_domains \<Rightarrow> sgcontext \<Rightarrow> (ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> 'c book_named_term \<Rightarrow> ZF) \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_ZF_valid_everywhere W D G J A \<longleftrightarrow> (\<forall>w\<in>explode W. book_ZF_valid_at D G J w A)"

lemma book_ZF_valid_everywhereI:
  assumes "\<And>w. w \<in> explode W \<Longrightarrow> book_ZF_valid_at D G J w A"
  shows "book_ZF_valid_everywhere W D G J A"
  unfolding book_ZF_valid_everywhere_def using assms by blast

lemma book_ZF_valid_everywhereD:
  assumes "book_ZF_valid_everywhere W D G J A" and "w \<in> explode W"
  shows "book_ZF_valid_at D G J w A"
  using assms unfolding book_ZF_valid_everywhere_def by blast

locale book_ZF_nontrivial_modal_interpretation =
  book_ZF_nontrivial_modal_model W R root D i signature I +
  book_ZF_modal_interpretation W R root D i signature I G J
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF
    and D :: book_ZF_domains and i :: book_ZF_counterparts
    and signature :: "'c ssignature" and I :: "'c \<Rightarrow> otype \<Rightarrow> ZF"
    and G :: sgcontext and J :: "ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ('c,book_minimal_logical) named_term \<Rightarrow> ZF"
begin

theorem bottom_false_at:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "\<not> book_ZF_truth_at J w g (book_bottom G)"
  using false_at_world[OF ww] by (simp only: truth_bottom[OF rich ww typed]; blast)

subsection \<open>Modalized Functionality\<close>

theorem MF_valid_at:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W"
  shows "book_ZF_valid_at D G J w (book_MF_axiom G \<sigma> \<tau>)"
proof (rule book_ZF_valid_atI)
  fix g assume typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  let ?x = "book_MF_left G \<sigma> \<tau>" and ?y = "book_MF_right G \<sigma> \<tau>" and ?z = "book_MF_argument G \<sigma> \<tau>"
  have xt: "G ?x = Arr \<sigma> \<tau>" and yt: "G ?y = Arr \<sigma> \<tau>" and zt: "G ?z = \<sigma>" by (rule book_MF_names_type[OF rich])+
  have distinct: "?x \<noteq> ?y" "?x \<noteq> ?z" "?y \<noteq> ?z" using book_MF_names_distinct[OF rich] by simp_all
  let ?xz = "NApp (NVar ?x) (NVar ?z)" and ?yz = "NApp (NVar ?y) (NVar ?z)"
  have xl: "book_in_language book_minimal_logical_type UNIV signature G (NVar ?x) (Arr \<sigma> \<tau>)"
    and yl: "book_in_language book_minimal_logical_type UNIV signature G (NVar ?y) (Arr \<sigma> \<tau>)"
    and zl: "book_in_language book_minimal_logical_type UNIV signature G (NVar ?z) \<sigma>"
    by (simp_all only: book_language_var_iff xt yt zt)
  have xzl: "book_in_language book_minimal_logical_type UNIV signature G ?xz \<tau>"
    and yzl: "book_in_language book_minimal_logical_type UNIV signature G ?yz \<tau>"
    by (rule book_language_App[OF xl zl], rule book_language_App[OF yl zl])
  let ?inner = "book_leibniz G \<tau> ?xz ?yz"
  let ?boxed = "book_box G (book_all G ?z ?inner)"
  let ?outer = "book_leibniz G (Arr \<sigma> \<tau>) (NVar ?x) (NVar ?y)"
  have il: "book_theory_formula signature G ?inner" by (rule book_leibniz_language[OF rich xzl yzl])
  have al: "book_theory_formula signature G (book_all G ?z ?inner)" by (rule book_all_language[OF il])
  have bl: "book_theory_formula signature G ?boxed" by (rule book_box_language[OF rich al])
  have ol: "book_theory_formula signature G ?outer" by (rule book_leibniz_language[OF rich xl yl])
  have bodyl: "book_theory_formula signature G (book_MF_body G \<sigma> \<tau>)" by (rule book_MF_body_language[OF rich])
  have body_eq: "book_MF_body G \<sigma> \<tau> = book_imp ?boxed ?outer" by (simp only: book_MF_body_def)
  have inner_body: "book_ZF_truth_at J w (g(?x := F, ?y := H)) (book_MF_body G \<sigma> \<tau>)"
    if fm: "F \<in> explode (D (G ?x) w)" and hm: "H \<in> explode (D (G ?y) w)" for F H
  proof -
    let ?h = "g(?x := F, ?y := H)"
    have ht: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?h" by (rule book_env_update[OF book_env_update[OF typed fm] hm])
    have fm': "F \<in> explode (D (Arr \<sigma> \<tau>) w)" and hm': "H \<in> explode (D (Arr \<sigma> \<tau>) w)" using fm hm by (simp_all only: xt yt)
    have hx: "?h ?x = F" and hy: "?h ?y = H" using distinct by simp_all
    have consequent: "book_ZF_truth_at J w ?h ?outer \<longleftrightarrow> F = H"
      by (simp only: truth_leibniz[OF rich xl yl ww ht] denote_variable[OF ww ht] hx hy)
    have premise: "book_ZF_truth_at J w ?h ?boxed \<Longrightarrow> F = H"
    proof -
      assume boxed: "book_ZF_truth_at J w ?h ?boxed"
      have future: "book_ZF_truth_at J v (book_ZF_move i G w v ?h) (book_all G ?z ?inner)"
        if vw: "v \<in> explode W" and wv: "R w v" for v
        using boxed vw wv by (simp only: truth_box[OF rich al ww ht]; blast)
      have agree: "app F (Opair v a) = app H (Opair v a)"
        if vw: "v \<in> explode W" and wv: "R w v" and am: "a \<in> explode (D \<sigma> v)" for v a
      proof -
        let ?m = "book_ZF_move i G w v ?h"
        have mt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G ?m" by (rule assignment_move_typed[OF ww vw wv ht])
        have at: "a \<in> explode (D (G ?z) v)" using am by (simp only: zt)
        let ?k = "?m(?z := a)"
        have kt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G ?k" by (rule book_env_update[OF mt at])
        have inst_l: "book_ZF_truth_at J v ?k ?inner"
          using future[OF vw wv] at by (simp only: truth_all[OF il vw mt]; blast)
        have kx: "?k ?x = i (Arr \<sigma> \<tau>) w v F" and ky: "?k ?y = i (Arr \<sigma> \<tau>) w v H" and kz: "?k ?z = a"
          using distinct by (simp_all add: book_ZF_move_def xt yt)
        have restricted_F: "i (Arr \<sigma> \<tau>) w v F = book_ZF_restrict W R (D \<sigma>) v F"
          and restricted_H: "i (Arr \<sigma> \<tau>) w v H = book_ZF_restrict W R (D \<sigma>) v H"
          by (rule function_restriction[OF ww vw wv fm'], rule function_restriction[OF ww vw wv hm'])
        have current: "Elem (Opair v a) (book_ZF_pairs W R (D \<sigma>) v)"
          using vw am reflexive[OF vw] by (simp only: book_ZF_pairs_member explode_Elem)
        have vals: "J v ?k ?xz = app F (Opair v a)" "J v ?k ?yz = app H (Opair v a)"
          by (simp_all only: denote_application[OF vw xl zl kt] denote_application[OF vw yl zl kt]
            denote_variable[OF vw kt] kx ky kz restricted_F restricted_H book_ZF_restrict_app[OF current])
        show ?thesis using inst_l by (simp only: truth_leibniz[OF rich xzl yzl vw kt] vals)
      qed
      show "F = H" by (rule future_function_extensionality[OF ww fm' hm']; rule agree; assumption)
    qed
    show ?thesis unfolding body_eq
      by (simp only: truth_imp[OF bl ol ww ht] consequent; rule impI; rule premise; assumption)
  qed
  show "book_ZF_truth_at J w g (book_MF_axiom G \<sigma> \<tau>)"
    unfolding book_MF_axiom_def
    by (simp only: truth_all[OF book_all_language[OF bodyl] ww typed]; intro ballI;
      simp only: truth_all[OF bodyl ww book_env_update[OF typed]]; intro ballI; rule inner_body; assumption)
qed

subsection \<open>Propositional Equivalence\<close>

theorem PE_valid_everywhere:
  assumes rich: "sg_rich G" and pl: "book_theory_formula signature G P" and ql: "book_theory_formula signature G Q"
    and premise: "book_ZF_valid_everywhere W D G J (book_iff G P Q)"
  shows "book_ZF_valid_everywhere W D G J (book_leibniz G Prop P Q)"
proof (rule book_ZF_valid_everywhereI, rule book_ZF_valid_atI)
  fix w g assume ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  have equal: "J w g P = J w g Q"
  proof (rule iffD2[OF Ext], intro allI)
    fix v
    show "Elem v (J w g P) = Elem v (J w g Q)"
    proof (cases "v \<in> explode W \<and> R w v")
      case True
      then have vw: "v \<in> explode W" and wv: "R w v" by blast+
      have mt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G (book_ZF_move i G w v g)"
        by (rule assignment_move_typed[OF ww vw wv typed])
      have iff: "book_ZF_truth_at J v (book_ZF_move i G w v g) (book_iff G P Q)"
        by (rule book_ZF_valid_atD[OF book_ZF_valid_everywhereD[OF premise vw] mt])
      show ?thesis
        by (simp only: truth_at_future[OF pl ww vw wv typed] truth_at_future[OF ql ww vw wv typed];
          insert iff; simp only: truth_iff[OF rich pl ql vw mt])
    next
      case False
      show ?thesis using proposition_future[OF pl ww typed] proposition_future[OF ql ww typed] False by blast
    qed
  qed
  show "book_ZF_truth_at J w g (book_leibniz G Prop P Q)"
    by (simp only: truth_leibniz[OF rich pl ql ww typed] equal)
qed

subsection \<open>Every full-C theorem is valid at every world\<close>

theorem full_C_valid_everywhere:
  assumes rich: "sg_rich G" and theorem_C: "book_full_C_proves signature G A"
  shows "book_ZF_valid_everywhere W D G J A"
  using theorem_C
proof (induction rule: book_full_C_proves.induct)
  case (H A)
  show ?case by (rule book_ZF_valid_everywhereI; rule H_valid_at[OF rich _ H.hyps]; assumption)
next
  case (MF \<sigma> \<tau>)
  show ?case by (rule book_ZF_valid_everywhereI; rule MF_valid_at[OF rich]; assumption)
next
  case (MP A B)
  have al: "book_theory_formula signature G A" by (rule book_full_C_proves_language[OF rich MP.hyps(1)])
  show ?case
    by (rule book_ZF_valid_everywhereI; rule MP_valid[OF al MP.hyps(3) _ book_ZF_valid_everywhereD[OF MP.IH(1)]
      book_ZF_valid_everywhereD[OF MP.IH(2)]]; assumption)
next
  case (Gen A B n)
  show ?case
    by (rule book_ZF_valid_everywhereI; rule Gen_valid[OF Gen.hyps(2,3,4) _ book_ZF_valid_everywhereD[OF Gen.IH]]; assumption)
next
  case (PE P Q)
  show ?case by (rule PE_valid_everywhere[OF rich PE.hyps(2,3) PE.IH])
qed

subsection \<open>Theory-level soundness at the root and consistency from satisfiability\<close>

theorem full_C_theory_valid_at_root:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable signature G S A"
    and satisfied: "book_ZF_satisfies D G J root S"
  shows "book_ZF_formula_valid D G J root A"
proof -
  have base: "book_theory_derivable signature G ({B. book_full_C_proves signature G B} \<union> S) A"
    using derivation by (simp only: book_full_C_theory_derivable_def)
  have leaves: "book_ZF_valid_at D G J root B" if member: "B \<in> {B. book_full_C_proves signature G B} \<union> S" for B
    using member
  proof (elim UnE)
    assume "B \<in> {B. book_full_C_proves signature G B}"
    then have theorem_C: "book_full_C_proves signature G B" by simp
    show ?thesis by (rule book_ZF_valid_everywhereD[OF full_C_valid_everywhere[OF rich theorem_C] root_world])
  next
    assume "B \<in> S"
    then show ?thesis using satisfied by (simp only: book_ZF_satisfies_def book_ZF_valid_at_root; blast)
  qed
  show ?thesis
    by (simp only: book_ZF_valid_at_root[symmetric]; rule theory_derivable_valid_at[OF rich root_world base leaves])
qed

theorem satisfiable_theory_consistent:
  assumes rich: "sg_rich G" and satisfied: "book_ZF_satisfies D G J root S"
  shows "book_full_C_theory_consistent signature G S"
proof (unfold book_full_C_theory_consistent_def, rule notI)
  assume absurd: "book_full_C_theory_derivable signature G S (book_bottom G)"
  have valid: "book_ZF_formula_valid D G J root (book_bottom G)"
    by (rule full_C_theory_valid_at_root[OF rich absurd satisfied])
  obtain g where typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> root)) G g"
    using typed_assignment_exists[OF root_world] by blast
  have true_bottom: "book_ZF_truth_at J root g (book_bottom G)"
    using valid typed by (simp only: book_ZF_formula_valid_def; blast)
  show False using bottom_false_at[OF rich root_world typed] true_bottom by blast
qed

end

text \<open>
  full_C_valid_everywhere is the generic soundness statement: every
  theorem of the independent full-C calculus is true at every world of
  every nontrivial book modal model under every typed assignment, for
  every admissible interpretation. full_C_theory_valid_at_root is the
  theory-level form used by completeness: premises need only be
  satisfied at the root. Nothing here constructs a model; consistency
  of a satisfiable theory follows from the root's false proposition and
  an actual typed root assignment.
\<close>

end
