theory Classicism_2_11_Extension
  imports
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Action_Classicism_Soundness"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Validity_Rules"
begin

section \<open>Classicism extended by unnecessitated hypotheses\<close>

text \<open>
  Bacon–Dorr say that principles imply a formula when it is derivable in
  the smallest H-theory containing them. H-theories are closed under MP,
  Gen and Inst (§1.1, p.7; rules in Figure 2, p.8), and Classicism C is the smallest H-theory
  containing Logical Equivalence (§1.3, p.12). The judgment below adds a
  set Ax of in-language hypotheses to C and closes under exactly the MP,
  Gen and Inst shapes of the native C judgment.

  The added hypotheses are NOT necessitated: no Necessitation rule is
  included, and Logical Equivalence is supplied only through C itself
  (its certificate remains native H theoremhood, never this judgment).
  Truth in an action model is truth at the identity arrow of the root
  under every typed, adequate assignment (Definition 3.20, p.56).
\<close>

inductive c211_proves ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext and Ax :: "'c paper_named_term set" where
  Classicism: "paper_R_classicism_proves \<Sigma> G A \<Longrightarrow> c211_proves \<Sigma> G Ax A"
| Axiom: "A \<in> Ax \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop \<Longrightarrow> c211_proves \<Sigma> G Ax A"
| MP: "c211_proves \<Sigma> G Ax A \<Longrightarrow>
    c211_proves \<Sigma> G Ax (named_paper_imp G A B) \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> c211_proves \<Sigma> G Ax B"
| Gen: "c211_proves \<Sigma> G Ax (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv P \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
    c211_proves \<Sigma> G Ax (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
| Inst: "c211_proves \<Sigma> G Ax (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv Q \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
    c211_proves \<Sigma> G Ax (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"

subsection \<open>Basic proof-theoretic facts\<close>

theorem c211_proves_language:
  assumes derivation: "c211_proves \<Sigma> G Ax A"
  shows "paper_R_in_language \<Sigma> G A Prop"
  using derivation
proof (induction rule: c211_proves.induct)
  case (Classicism A)
  show ?case by (rule paper_R_classicism_proves_language[OF Classicism.hyps])
next
  case (Axiom A)
  show ?case by (rule Axiom.hyps(2))
next
  case (MP A B)
  show ?case by (rule MP.hyps(3))
next
  case (Gen P Q n \<sigma>)
  show ?case by (rule Gen.hyps(4))
next
  case (Inst P Q n \<sigma>)
  show ?case by (rule Inst.hyps(4))
qed

theorem c211_proves_classicism_mono:
  "paper_R_classicism_proves \<Sigma> G A \<Longrightarrow> c211_proves \<Sigma> G Ax A"
  by (rule c211_proves.Classicism)

theorem c211_proves_mono:
  assumes derivation: "c211_proves \<Sigma> G Ax A" and subset: "Ax \<subseteq> Bx"
  shows "c211_proves \<Sigma> G Bx A"
  using derivation
proof (induction rule: c211_proves.induct)
  case (Classicism A)
  show ?case by (rule c211_proves.Classicism[OF Classicism.hyps])
next
  case (Axiom A)
  show ?case by (rule c211_proves.Axiom[OF subsetD[OF subset Axiom.hyps(1)] Axiom.hyps(2)])
next
  case (MP A B)
  show ?case by (rule c211_proves.MP[OF MP.IH MP.hyps(3)])
next
  case (Gen P Q n \<sigma>)
  show ?case by (rule c211_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
next
  case (Inst P Q n \<sigma>)
  show ?case by (rule c211_proves.Inst[OF Inst.IH Inst.hyps(2,3,4)])
qed

theorem c211_proves_empty_iff:
  "c211_proves \<Sigma> G {} A \<longleftrightarrow> paper_R_classicism_proves \<Sigma> G A"
proof
  assume "c211_proves \<Sigma> G {} A"
  then show "paper_R_classicism_proves \<Sigma> G A"
  proof (induction rule: c211_proves.induct)
    case (Classicism A)
    show ?case by (rule Classicism.hyps)
  next
    case (Axiom A)
    show ?case using Axiom.hyps(1) by (rule emptyE)
  next
    case (MP A B)
    show ?case by (rule paper_R_classicism_proves.MP[OF MP.IH MP.hyps(3)])
  next
    case (Gen P Q n \<sigma>)
    show ?case by (rule paper_R_classicism_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
  next
    case (Inst P Q n \<sigma>)
    show ?case by (rule paper_R_classicism_proves.Inst[OF Inst.IH Inst.hyps(2,3,4)])
  qed
next
  assume "paper_R_classicism_proves \<Sigma> G A"
  then show "c211_proves \<Sigma> G {} A" by (rule c211_proves.Classicism)
qed

subsection \<open>The derivable set is the least closed set\<close>

definition c211_closed ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "c211_closed \<Sigma> G Ax Th \<longleftrightarrow>
    (\<forall>A. paper_R_classicism_proves \<Sigma> G A \<longrightarrow> A \<in> Th) \<and>
    (\<forall>A\<in>Ax. paper_R_in_language \<Sigma> G A Prop \<longrightarrow> A \<in> Th) \<and>
    (\<forall>A B. A \<in> Th \<longrightarrow> named_paper_imp G A B \<in> Th \<longrightarrow>
      paper_R_in_language \<Sigma> G B Prop \<longrightarrow> B \<in> Th) \<and>
    (\<forall>P Q n \<sigma>. named_paper_imp G P Q \<in> Th \<longrightarrow> G n = \<sigma> \<longrightarrow> n \<notin> named_fv P \<longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<longrightarrow>
      named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)) \<in> Th) \<and>
    (\<forall>P Q n \<sigma>. named_paper_imp G P Q \<in> Th \<longrightarrow> G n = \<sigma> \<longrightarrow> n \<notin> named_fv Q \<longrightarrow>
      paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<longrightarrow>
      named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q \<in> Th)"

theorem c211_proves_closed: "c211_closed \<Sigma> G Ax {A. c211_proves \<Sigma> G Ax A}"
  unfolding c211_closed_def mem_Collect_eq
  by (intro conjI allI ballI impI;
      erule c211_proves.Classicism c211_proves.Axiom c211_proves.MP
        c211_proves.Gen c211_proves.Inst; assumption)

theorem c211_proves_least:
  assumes closed: "c211_closed \<Sigma> G Ax Th" and derivation: "c211_proves \<Sigma> G Ax A"
  shows "A \<in> Th"
  using derivation
proof (induction rule: c211_proves.induct)
  case (Classicism A)
  show ?case using closed Classicism.hyps unfolding c211_closed_def by blast
next
  case (Axiom A)
  show ?case using closed Axiom.hyps unfolding c211_closed_def by blast
next
  case (MP A B)
  show ?case using closed MP.IH MP.hyps(3) unfolding c211_closed_def by blast
next
  case (Gen P Q n \<sigma>)
  show ?case using closed Gen.IH Gen.hyps(2,3,4) unfolding c211_closed_def by blast
next
  case (Inst P Q n \<sigma>)
  show ?case using closed Inst.IH Inst.hyps(2,3,4) unfolding c211_closed_def by blast
qed

theorem c211_proves_Inter:
  "{A. c211_proves \<Sigma> G Ax A} = \<Inter>{Th. c211_closed \<Sigma> G Ax Th}"
proof (rule equalityI)
  show "{A. c211_proves \<Sigma> G Ax A} \<subseteq> \<Inter>{Th. c211_closed \<Sigma> G Ax Th}"
    using c211_proves_least by blast
  show "\<Inter>{Th. c211_closed \<Sigma> G Ax Th} \<subseteq> {A. c211_proves \<Sigma> G Ax A}"
    by (rule Inter_lower, rule CollectI, rule c211_proves_closed)
qed

section \<open>Truth at the identity arrow of the root\<close>

definition c211_valid ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "c211_valid \<Sigma> G Ar source target compose identity Root D T I A \<longleftrightarrow>
    paper_R_in_language \<Sigma> G A Prop \<and>
    (\<forall>g. paper_ZF_action_env_typed D G (target (identity Root)) g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_ZF_action_holds Ar source target compose identity D T I G (identity Root) g A)"

lemma c211_root_identity:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
  shows "identity Root \<in> explode Ar" and "source (identity Root) = Root"
    and "target (identity Root) = Root"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity Root"
    using model unfolding paper_ZF_action_model_def paper_ZF_action_premodel_def by blast
  interpret C: paper_rooted_category Obj "explode Ar" source target compose identity Root
    by (rule rooted)
  show "identity Root \<in> explode Ar" by (rule C.identity_arrow[OF C.root_object])
  show "source (identity Root) = Root" by (rule C.identity_source[OF C.root_object])
  show "target (identity Root) = Root" by (rule C.identity_target[OF C.root_object])
qed

lemma c211_valid_iff_bbk:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
  shows "c211_valid \<Sigma> G Ar source target compose identity Root D T I A \<longleftrightarrow>
    paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_ZF_action_bbk_domain D (target (identity Root)))
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G (identity Root))
      (paper_ZF_action_bbk_valuation target identity (identity Root)) A"
    (is "?valid \<longleftrightarrow> ?bbk")
proof -
  let ?h = "identity Root"
  let ?D = "paper_ZF_action_bbk_domain D (target ?h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G ?h"
  let ?V = "paper_ZF_action_bbk_valuation target identity ?h"
  note arrow = c211_root_identity(1)[OF model]
  note origin = c211_root_identity(2)[OF model]
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  show ?thesis
  proof
    assume valid: ?valid
    have language: "paper_R_in_language \<Sigma> G A Prop"
      using valid unfolding c211_valid_def by (rule conjunct1)
    show ?bbk
    proof (rule M.paper_R_validI[OF language])
      fix g
      assume typed: "named_env_typed ?D G g" and adequate: "named_adequate g A"
      have env: "paper_ZF_action_env_typed D G (target ?h) g"
        by (rule iffD1[OF paper_ZF_action_bbk_env_iff typed])
      have holds: "paper_ZF_action_holds Ar source target compose identity D T I G ?h g A"
        using valid env adequate unfolding c211_valid_def by blast
      show "?V (?J g A)"
        by (rule iffD1[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin typed adequate]
              holds])
    qed
  next
    assume bbk: ?bbk
    have language: "paper_R_in_language \<Sigma> G A Prop" by (rule M.paper_R_valid_language[OF bbk])
    show ?valid
      unfolding c211_valid_def
    proof (intro conjI allI impI)
      show "paper_R_in_language \<Sigma> G A Prop" by (rule language)
      fix g
      assume env: "paper_ZF_action_env_typed D G (target ?h) g" and adequate: "named_adequate g A"
      have typed: "named_env_typed ?D G g" by (rule iffD2[OF paper_ZF_action_bbk_env_iff env])
      have truth: "?V (?J g A)" by (rule M.paper_R_validE[OF bbk typed adequate])
      show "paper_ZF_action_holds Ar source target compose identity D T I G ?h g A"
        by (rule iffD2[OF paper_ZF_action_bbk_holds_iff[OF model language arrow origin typed adequate]
              truth])
    qed
  qed
qed

section \<open>Soundness of the extension at the root\<close>

theorem c211_soundness:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and hyp_valid: "\<forall>B\<in>Ax. c211_valid \<Sigma> G Ar source target compose identity Root D T I B"
    and derivation: "c211_proves \<Sigma> G Ax A"
  shows "c211_valid \<Sigma> G Ar source target compose identity Root D T I A"
proof -
  let ?h = "identity Root"
  let ?D = "paper_ZF_action_bbk_domain D (target ?h)"
  let ?J = "paper_ZF_action_bbk_denote Ar source target compose identity D T I G ?h"
  let ?V = "paper_ZF_action_bbk_valuation target identity ?h"
  note arrow = c211_root_identity(1)[OF model]
  note origin = c211_root_identity(2)[OF model]
  interpret M: paper_R_bbk_model \<Sigma> G ?D ?J ?V
    by (rule paper_ZF_action_to_R_bbk_model[OF model arrow origin])
  have "M.paper_R_valid A"
    using derivation
  proof (induction rule: c211_proves.induct)
    case (Classicism A)
    show ?case
      by (rule paper_ZF_action_classicism_BBK_valid[OF model Classicism.hyps arrow origin])
  next
    case (Axiom A)
    have "c211_valid \<Sigma> G Ar source target compose identity Root D T I A"
      using hyp_valid Axiom.hyps(1) by (rule bspec)
    then show ?case by (simp only: c211_valid_iff_bbk[OF model])
  next
    case (MP A B)
    show ?case by (rule M.paper_R_valid_MP[
      OF M.paper_R_valid_language[OF MP.IH(1)] MP.hyps(3) MP.IH(1,2)])
  next
    case (Gen P Q n \<sigma>)
    have operands: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
      by (rule paper_R_imp_language_operands[OF M.stock_rich M.paper_R_valid_language[OF Gen.IH]])
    have quantifier: "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> (NLam n Q)) Prop"
      by (rule conjunct2[OF paper_R_imp_language_operands[OF M.stock_rich Gen.hyps(4)]])
    have predicate: "paper_R_in_language \<Sigma> G (NLam n Q) (Arr \<sigma> Prop)"
      by (rule paper_R_all_language_operand[OF quantifier])
    have rt: "paper_R_type \<sigma>"
      by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
    show ?case by (rule M.paper_R_valid_Gen[
      OF conjunct1[OF operands] conjunct2[OF operands] Gen.hyps(2) rt Gen.hyps(3) Gen.IH])
  next
    case (Inst P Q n \<sigma>)
    have operands: "paper_R_in_language \<Sigma> G P Prop \<and> paper_R_in_language \<Sigma> G Q Prop"
      by (rule paper_R_imp_language_operands[OF M.stock_rich M.paper_R_valid_language[OF Inst.IH]])
    have quantifier: "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> (NLam n P)) Prop"
      by (rule conjunct1[OF paper_R_imp_language_operands[OF M.stock_rich Inst.hyps(4)]])
    have predicate: "paper_R_in_language \<Sigma> G (NLam n P) (Arr \<sigma> Prop)"
      by (rule paper_R_ex_language_operand[OF quantifier])
    have rt: "paper_R_type \<sigma>"
      by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
    show ?case by (rule M.paper_R_valid_Inst[
      OF conjunct1[OF operands] conjunct2[OF operands] Inst.hyps(2) rt Inst.hyps(3) Inst.IH])
  qed
  then show ?thesis by (simp only: c211_valid_iff_bbk[OF model])
qed

corollary c211_underivable:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and hyp_valid: "\<forall>A\<in>Ax. c211_valid \<Sigma> G Ar source target compose identity Root D T I A"
    and fails: "\<not> c211_valid \<Sigma> G Ar source target compose identity Root D T I B"
  shows "\<not> c211_proves \<Sigma> G Ax B"
proof
  assume "c211_proves \<Sigma> G Ax B"
  then have "c211_valid \<Sigma> G Ar source target compose identity Root D T I B"
    by (rule c211_soundness[OF model hyp_valid])
  then show False using fails by (rule notE[rotated])
qed

text \<open>
  Sources: H-theory closure under MP, Gen and Inst, §1.1, p.7 (Figure 2, p.8);
  C as the smallest H-theory containing Logical Equivalence, §1.3, p.12;
  truth in an action model, Definition 3.20, p.56; the soundness direction
  of Theorem 3.23, p.58, via Proposition C.7, pp.71–72. Hypotheses in Ax
  are used only as premises: there is no Necessitation rule for them, so
  validity at the root identity arrow (not at every arrow) suffices.
\<close>

ML \<open>
  val facts = [@{thm c211_proves_language}, @{thm c211_proves_classicism_mono},
    @{thm c211_proves_mono}, @{thm c211_proves_empty_iff}, @{thm c211_proves_closed},
    @{thm c211_proves_least}, @{thm c211_proves_Inter}, @{thm c211_root_identity(1)},
    @{thm c211_root_identity(2)}, @{thm c211_root_identity(3)}, @{thm c211_valid_iff_bbk},
    @{thm c211_soundness}, @{thm c211_underivable}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-EXTENSION: C plus unnecessitated hypotheses is sound for root truth";
\<close>

end
