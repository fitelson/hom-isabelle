theory Bacon_Source_ZF_Model_Vector_Equality
  imports Bacon_Source_ZF_Model_Evaluation_Contexts Bacon_Source_ZF_Model_Truth_Separation
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Binder_Vectors
begin

section \<open>Literal binder vectors are compatible contexts\<close>

text \<open>
  The fold λn₁…nₖ.A keeps the first name outermost. The list may
  be empty or contain repeated names. A compatible replacement lifts
  beneath this fold without a freshness or distinctness condition.
  Source: the vector notation of Figure 1 and the C.7 argument, p.71.
\<close>

lemma paper_ZF_named_lam_vec_compatible:
  assumes step: "named_compatible_step R A B"
  shows "named_compatible_step R (named_lam_vec ns A) (named_lam_vec ns B)"
proof (induction ns)
  case Nil
  show ?case by (simp only: named_lam_vec.simps; rule step)
next
  case (Cons n ns)
  show ?case by (simp only: named_lam_vec.simps; rule named_compatible_step.Lam_body[OF Cons.IH])
qed

section \<open>Uniform body equality lifts with only abstraction adequacy\<close>

theorem paper_ZF_premodel_vector_equality:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and uniform: "\<And>k u. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u A \<Longrightarrow> named_adequate u B \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G A k u =
      paper_ZF_action_eval Ar source target compose identity D T I G B k u"
    and left: "paper_R_in_language \<Sigma> G (named_lam_vec ns A) \<rho>"
    and right: "paper_R_in_language \<Sigma> G (named_lam_vec ns B) \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g (named_lam_vec ns A)"
    and adequate_right: "named_adequate g (named_lam_vec ns B)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns A) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns B) h g"
proof -
  have root_step: "named_compatible_step (\<lambda>U V. U = A \<and> V = B) A B"
    by (rule named_compatible_step.root; simp)
  have step: "named_compatible_step (\<lambda>U V. U = A \<and> V = B)
      (named_lam_vec ns A) (named_lam_vec ns B)"
    by (rule paper_ZF_named_lam_vec_compatible[OF root_step])
  show ?thesis
  proof (rule paper_ZF_premodel_eval_compatible[
      OF premodel step _ left right arrow origin typed adequate_left adequate_right])
    fix U V \<tau> k u
    assume shape: "U = A \<and> V = B"
      and ul: "paper_R_in_language \<Sigma> G U \<tau>" and vl: "paper_R_in_language \<Sigma> G V \<tau>"
      and ka: "k \<in> explode Ar" and ko: "source k = root"
      and ut: "paper_ZF_action_env_typed D G (target k) u"
      and ua: "named_adequate u U" and va: "named_adequate u V"
    show "paper_ZF_action_eval Ar source target compose identity D T I G U k u =
      paper_ZF_action_eval Ar source target compose identity D T I G V k u"
      using uniform[of k u] shape ka ko ut ua va by blast
  qed
qed

theorem paper_ZF_action_model_vector_equality:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and uniform: "\<And>k u. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u P \<Longrightarrow> named_adequate u Q \<Longrightarrow>
      paper_ZF_action_eval Ar source target compose identity D T I G P k u =
      paper_ZF_action_eval Ar source target compose identity D T I G Q k u"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g (named_lam_vec ns P)"
    and adequate_right: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns P) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns Q) h g"
proof -
  have premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    using model unfolding paper_ZF_action_model_def by blast
  have lp: "paper_R_in_language \<Sigma> G (named_lam_vec ns P) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF left binders])
  have lq: "paper_R_in_language \<Sigma> G (named_lam_vec ns Q) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF right binders])
  show ?thesis by (rule paper_ZF_premodel_vector_equality[
    OF premodel uniform lp lq arrow origin typed adequate_left adequate_right])
qed

section \<open>The two semantic ingredients of C.7 compose\<close>

text \<open>
  Uniform truth agreement first yields proposition-value equality,
  and guarded C.2 then yields equality of the vector abstractions.
  The final assignment need cover only FV(P)−set(ns) and
  FV(Q)−set(ns). Binder updates supply the missing body variables.
  This is not yet the H theoremhood premise or the concluding identity
  formula of C.7; neither is assumed or defined by this theorem.
\<close>

theorem paper_ZF_action_model_uniform_truth_vector_equal:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
    and uniform: "\<And>k u. k \<in> explode Ar \<Longrightarrow> source k = root \<Longrightarrow>
      paper_ZF_action_env_typed D G (target k) u \<Longrightarrow>
      named_adequate u P \<Longrightarrow> named_adequate u Q \<Longrightarrow>
      paper_ZF_action_holds Ar source target compose identity D T I G k u P =
      paper_ZF_action_holds Ar source target compose identity D T I G k u Q"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g (named_lam_vec ns P)"
    and adequate_right: "named_adequate g (named_lam_vec ns Q)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns P) h g =
    paper_ZF_action_eval Ar source target compose identity D T I G (named_lam_vec ns Q) h g"
proof (rule paper_ZF_action_model_vector_equality[
    OF model left right binders _ arrow origin typed adequate_left adequate_right])
  fix k u
  assume ka: "k \<in> explode Ar" and ko: "source k = root"
    and ut: "paper_ZF_action_env_typed D G (target k) u"
    and ua: "named_adequate u P" and va: "named_adequate u Q"
  show "paper_ZF_action_eval Ar source target compose identity D T I G P k u =
    paper_ZF_action_eval Ar source target compose identity D T I G Q k u"
    by (rule paper_ZF_action_model_uniform_truth_equal[OF model left right uniform ka ko ut ua va])
qed

end
