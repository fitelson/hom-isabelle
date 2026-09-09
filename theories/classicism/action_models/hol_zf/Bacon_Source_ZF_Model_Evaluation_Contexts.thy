theory Bacon_Source_ZF_Model_Evaluation_Contexts
  imports Bacon_Source_ZF_Evaluation_Contexts Bacon_Source_ZF_Action_Model
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Language_Inversion
begin

section \<open>Typing inversions for the two sides of a context\<close>

lemma paper_ZF_context_language_unique:
  assumes left: "paper_R_in_language \<Sigma> G A \<sigma>" and right: "paper_R_in_language \<Sigma> G A \<tau>"
  shows "\<sigma> = \<tau>"
  using left right paper_R_type_unique unfolding paper_R_in_language_def by blast

lemma paper_ZF_context_Lam_languageE:
  assumes language: "paper_R_in_language \<Sigma> G (NLam n A) \<rho>"
  obtains \<tau> where "\<rho> = Arr (G n) \<tau>" "paper_R_in_language \<Sigma> G A \<tau>"
    "paper_R_type (G n)" "\<tau> \<noteq> Ind"
proof -
  have typed: "paper_R_has_type G (NLam n A) \<rho>" and names: "named_in_signature \<Sigma> (NLam n A)"
    using language unfolding paper_R_in_language_def by blast+
  obtain \<tau> where shape: "\<rho> = Arr (G n) \<tau>" and body: "paper_R_has_type G A \<tau>"
    and binder_type: "paper_R_type (G n)" and relational: "\<tau> \<noteq> Ind"
    by (rule paper_R_lam_type_obtain[OF typed])
  have body_language: "paper_R_in_language \<Sigma> G A \<tau>"
    using body names by (simp add: paper_R_in_language_def)
  show thesis by (rule that[OF shape body_language binder_type relational])
qed

section \<open>Contextual equality only on legitimate root inputs\<close>

text \<open>
  In C.2 (pp.70–71), the replaced terms agree at every typed adequate
  root-arrow input, not at arbitrary raw evaluator inputs. Under λn,
  compare the bodies at i∘h and (i·g)[n↦a] for every outgoing pair.
  The premodel action laws preserve the input guards. A fixed operand's
  unique type aligns the potentially different App inversion witnesses.

  The conclusion is equality of option-valued evaluations, including
  None. Thus the core proof needs only a premodel; the model wrapper is
  provided for Appendix C. No independent totality, off-input equality,
  source BBK interpretation or representation map is assumed.
\<close>

theorem paper_ZF_premodel_eval_compatible:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity Root D T I"
    and step: "named_compatible_step R A B"
    and roots: "\<And>U V \<tau> h g. R U V \<Longrightarrow>
      paper_R_in_language \<Sigma> G U \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> G V \<tau> \<Longrightarrow>
      h \<in> explode Ar \<Longrightarrow> source h = Root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target h) g \<Longrightarrow>
      named_adequate g U \<Longrightarrow> named_adequate g V \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G U h g =
      paper_ZF_action_eval Ar source target compose identity D T I G V h g"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof -
  have rooted: "paper_rooted_category Obj (explode Ar) source target compose identity Root"
    using premodel unfolding paper_ZF_action_premodel_def by blast
  interpret Category: paper_rooted_category Obj "explode Ar" source target compose identity Root by (rule rooted)
  show ?thesis using step left right arrow origin typed adequate_left adequate_right
  proof (induction arbitrary: \<rho> h g rule: named_compatible_step.induct)
    case (root U V)
    show ?case by (rule roots[OF root.hyps root.prems])
  next
    case (App_left M M' N)
    obtain \<sigma> where ml: "paper_R_in_language \<Sigma> G M (Arr \<sigma> \<rho>)"
      and nl: "paper_R_in_language \<Sigma> G N \<sigma>"
      by (rule paper_R_language_AppE[OF App_left.prems(1)])
    obtain \<upsilon> where mr: "paper_R_in_language \<Sigma> G M' (Arr \<upsilon> \<rho>)"
      and nr: "paper_R_in_language \<Sigma> G N \<upsilon>"
      by (rule paper_R_language_AppE[OF App_left.prems(2)])
    have same: "\<sigma> = \<upsilon>" by (rule paper_ZF_context_language_unique[OF nl nr])
    have right_head: "paper_R_in_language \<Sigma> G M' (Arr \<sigma> \<rho>)"
      by (simp only: same; rule mr)
    have ma: "named_adequate g M" and mb: "named_adequate g M'"
      using App_left.prems(6,7) by (auto simp: named_adequate_def)
    have equal: "paper_ZF_action_eval Ar source target compose identity D T I G M h g =
        paper_ZF_action_eval Ar source target compose identity D T I G M' h g"
      by (rule App_left.IH[OF ml right_head App_left.prems(3,4,5) ma mb])
    show ?case by (simp only: paper_ZF_action_eval.simps equal)
  next
    case (App_right N N' M)
    obtain \<sigma> where ml: "paper_R_in_language \<Sigma> G M (Arr \<sigma> \<rho>)"
      and nl: "paper_R_in_language \<Sigma> G N \<sigma>"
      by (rule paper_R_language_AppE[OF App_right.prems(1)])
    obtain \<upsilon> where mr: "paper_R_in_language \<Sigma> G M (Arr \<upsilon> \<rho>)"
      and nr: "paper_R_in_language \<Sigma> G N' \<upsilon>"
      by (rule paper_R_language_AppE[OF App_right.prems(2)])
    have heads: "Arr \<sigma> \<rho> = Arr \<upsilon> \<rho>" by (rule paper_ZF_context_language_unique[OF ml mr])
    have same: "\<sigma> = \<upsilon>" using heads by simp
    have right_argument: "paper_R_in_language \<Sigma> G N' \<sigma>" by (simp only: same; rule nr)
    have na: "named_adequate g N" and nb: "named_adequate g N'"
      using App_right.prems(6,7) by (auto simp: named_adequate_def)
    have equal: "paper_ZF_action_eval Ar source target compose identity D T I G N h g =
        paper_ZF_action_eval Ar source target compose identity D T I G N' h g"
      by (rule App_right.IH[OF nl right_argument App_right.prems(3,4,5) na nb])
    show ?case by (simp only: paper_ZF_action_eval.simps equal)
  next
    case (Lam_body M M' n)
    obtain \<tau> where ls: "\<rho> = Arr (G n) \<tau>" and ml: "paper_R_in_language \<Sigma> G M \<tau>"
      and binder_type: "paper_R_type (G n)" and rel: "\<tau> \<noteq> Ind"
      by (rule paper_ZF_context_Lam_languageE[OF Lam_body.prems(1)])
    obtain \<upsilon> where rs: "\<rho> = Arr (G n) \<upsilon>" and mr: "paper_R_in_language \<Sigma> G M' \<upsilon>"
      by (rule paper_ZF_context_Lam_languageE[OF Lam_body.prems(2)]; rule that; assumption)
    have same: "\<tau> = \<upsilon>" using ls rs by simp
    have right_body: "paper_R_in_language \<Sigma> G M' \<tau>" by (simp only: same; rule mr)
    show ?case
    proof (simp only: paper_ZF_action_eval.simps; rule paper_ZF_action_abstract_cong)
      fix i a
      assume pair: "Elem (Opair i a) (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
      have ia: "i \<in> explode Ar" and isource: "source i = target h" and am: "a \<in> explode (D (G n) (target i))"
        using pair by (auto simp only: paper_ZF_pair_code_member)
      have meeting: "target h = source i" by (rule isource[symmetric])
      have composite: "compose i h \<in> explode Ar" by (rule Category.compose_arrow[OF Lam_body.prems(3) ia meeting])
      have csource: "source (compose i h) = Root"
        by (simp only: Category.compose_source[OF Lam_body.prems(3) ia meeting] Lam_body.prems(4))
      have ctarget: "target (compose i h) = target i" by (rule Category.compose_target[OF Lam_body.prems(3) ia meeting])
      have it: "paper_ZF_action_env_typed D G (source i) g" by (simp only: isource; rule Lam_body.prems(5))
      have moved: "paper_ZF_action_env_typed D G (target i) (paper_ZF_action_transport_assignment G T i g)"
        by (rule paper_ZF_premodel_transport_env_typed[OF premodel ia it])
      let ?k = "(paper_ZF_action_transport_assignment G T i g)(n := Some a)"
      have kt: "paper_ZF_action_env_typed D G (target (compose i h)) ?k"
        by (simp only: ctarget; rule paper_ZF_action_env_update[where G=G and n=n, OF moved refl binder_type am])
      have ka: "named_adequate ?k M"
        by (simp only: paper_ZF_action_transport_body_adequate_iff; rule Lam_body.prems(6))
      have kb: "named_adequate ?k M'"
        by (simp only: paper_ZF_action_transport_body_adequate_iff; rule Lam_body.prems(7))
      show "paper_ZF_action_eval Ar source target compose identity D T I G M (compose i h) ?k =
          paper_ZF_action_eval Ar source target compose identity D T I G M' (compose i h) ?k"
        by (rule Lam_body.IH[OF ml right_body composite csource kt ka kb])
    qed
  qed
qed

corollary paper_ZF_model_eval_compatible:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and step: "named_compatible_step R A B"
    and roots: "\<And>U V \<tau> h g. R U V \<Longrightarrow>
      paper_R_in_language \<Sigma> G U \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> G V \<tau> \<Longrightarrow>
      h \<in> explode Ar \<Longrightarrow> source h = Root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target h) g \<Longrightarrow>
      named_adequate g U \<Longrightarrow> named_adequate g V \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G U h g =
      paper_ZF_action_eval Ar source target compose identity D T I G V h g"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity Root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  show ?thesis by (rule paper_ZF_premodel_eval_compatible[
    OF premodel step roots left right arrow origin typed adequate_left adequate_right])
qed

end
