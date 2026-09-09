theory Bacon_Source_ZF_Assignment_Transport_Laws
  imports Bacon_Source_ZF_Action_Assignments
begin

section \<open>Identity and composition on R-supported partial assignments\<close>

text \<open>
  1W·g=g and (i∘h)·g=i·(h·g) for a typed assignment g at
  source(h). Source: Definition 3.13, p.53, and the assignment
  transport used in Proposition C.1, p.70.

  The proof is pointwise. None stays None; an assigned value uses the
  action at its R type. No full-F action or total assignment is used.
  These are assignment laws, not an assumption of term naturality.
\<close>

theorem paper_ZF_action_assignment_transport_identity:
  assumes actions: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow>
    paper_action Obj Arrows source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    and object: "W \<in> Obj" and typed: "paper_ZF_action_env_typed D G W g"
  shows "paper_ZF_action_transport_assignment G T (identity W) g = g"
proof (rule ext)
  fix n
  show "paper_ZF_action_transport_assignment G T (identity W) g n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def None option.map)
  next
    case (Some a)
    have rt: "paper_R_type (G n)" by (rule paper_ZF_action_env_assigned_R[OF typed Some])
    have member: "a \<in> explode (D (G n) W)" by (rule paper_ZF_action_env_value[OF typed Some])
    interpret Act: paper_action Obj Arrows source target compose identity "\<lambda>W. explode (D (G n) W)" "T (G n)"
      by (rule actions[OF rt])
    have unchanged: "T (G n) (identity W) a = a" by (rule Act.transport_identity[OF object member])
    show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def Some option.map unchanged)
  qed
qed

theorem paper_ZF_action_assignment_transport_compose:
  assumes actions: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow>
    paper_action Obj Arrows source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    and first: "h \<in> Arrows" and second: "i \<in> Arrows" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (source h) g"
  shows "paper_ZF_action_transport_assignment G T (compose i h) g =
    paper_ZF_action_transport_assignment G T i (paper_ZF_action_transport_assignment G T h g)"
proof (rule ext)
  fix n
  show "paper_ZF_action_transport_assignment G T (compose i h) g n =
    paper_ZF_action_transport_assignment G T i (paper_ZF_action_transport_assignment G T h g) n"
  proof (cases "g n")
    case None
    show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def None option.map)
  next
    case (Some a)
    have rt: "paper_R_type (G n)" by (rule paper_ZF_action_env_assigned_R[OF typed Some])
    have member: "a \<in> explode (D (G n) (source h))" by (rule paper_ZF_action_env_value[OF typed Some])
    interpret Act: paper_action Obj Arrows source target compose identity "\<lambda>W. explode (D (G n) W)" "T (G n)"
      by (rule actions[OF rt])
    have composite: "T (G n) (compose i h) a = T (G n) i (T (G n) h a)"
      by (rule Act.transport_compose[OF first second meeting member])
    show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def Some option.map composite)
  qed
qed

corollary paper_ZF_premodel_assignment_transport_identity:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and typed: "paper_ZF_action_env_typed D G W g"
  shows "paper_ZF_action_transport_assignment G T (identity W) g = g"
proof -
  have actions: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    if "paper_R_type \<rho>" for \<rho>
    using premodel that unfolding paper_ZF_action_premodel_def by blast
  show ?thesis by (rule paper_ZF_action_assignment_transport_identity[OF actions object typed])
qed

corollary paper_ZF_premodel_assignment_transport_compose:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I"
    and first: "h \<in> explode Ar" and second: "i \<in> explode Ar" and meeting: "target h = source i"
    and typed: "paper_ZF_action_env_typed D G (source h) g"
  shows "paper_ZF_action_transport_assignment G T (compose i h) g =
    paper_ZF_action_transport_assignment G T i (paper_ZF_action_transport_assignment G T h g)"
proof -
  have actions: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    if "paper_R_type \<rho>" for \<rho>
    using premodel that unfolding paper_ZF_action_premodel_def by blast
  show ?thesis by (rule paper_ZF_action_assignment_transport_compose[OF actions first second meeting typed])
qed

end
