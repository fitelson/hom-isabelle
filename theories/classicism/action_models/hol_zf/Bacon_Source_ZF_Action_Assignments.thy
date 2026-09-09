theory Bacon_Source_ZF_Action_Assignments
  imports Bacon_Source_ZF_Action_Premodel
    Bacon_Classicism_Action_Development.Bacon_Source_Homomorphism_Assignments
begin

section \<open>R-supported partial assignments for coded action domains\<close>

text \<open>
  An assignment at W maps assigned variables n:ρ to elements of Wρ
  and is adequate for A when it covers FV(A). Source: Definitions
  3.19–3.20, pp.55–56, with the R grammar of §1.1, p.5.
  The generic premodel says nothing about its extra non-R indices.
  We therefore explicitly require every assigned name to have an R type.

  Transport is the existing option-valued assignment map: it preserves
  exactly the defined names. Its typing uses action laws only at those
  R indices. There is no total completion, interpretation or totality
  premise, and no unprinted condition on the off-R fibers.
\<close>

definition paper_ZF_action_env_typed ::
  "(otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow> 'o \<Rightarrow> ZF named_assignment \<Rightarrow> bool" where
  "paper_ZF_action_env_typed D G W g \<longleftrightarrow>
    named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G g \<and> (\<forall>n\<in>dom g. paper_R_type (G n))"

definition paper_ZF_action_transport_assignment ::
  "sgcontext \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow>
    ZF named_assignment \<Rightarrow> ZF named_assignment" where
  "paper_ZF_action_transport_assignment G T i g = paper_hom_assignment G (\<lambda>\<rho>. T \<rho> i) g"

lemma paper_ZF_action_envI:
  assumes typed: "named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G g"
    and support: "\<And>n. n \<in> dom g \<Longrightarrow> paper_R_type (G n)"
  shows "paper_ZF_action_env_typed D G W g"
  unfolding paper_ZF_action_env_typed_def by (rule conjI[OF typed], intro ballI, rule support; assumption)

lemma paper_ZF_action_env_named:
  "paper_ZF_action_env_typed D G W g \<Longrightarrow> named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G g"
  unfolding paper_ZF_action_env_typed_def by (rule conjunct1)

lemma paper_ZF_action_env_support:
  assumes typed: "paper_ZF_action_env_typed D G W g" and member: "n \<in> dom g"
  shows "paper_R_type (G n)"
  using typed member unfolding paper_ZF_action_env_typed_def by blast

lemma paper_ZF_action_env_value:
  assumes typed: "paper_ZF_action_env_typed D G W g" and assigned: "g n = Some a"
  shows "a \<in> explode (D (G n) W)"
  by (rule named_env_value[OF paper_ZF_action_env_named[OF typed] assigned])

lemma paper_ZF_action_env_assigned_R:
  assumes typed: "paper_ZF_action_env_typed D G W g" and assigned: "g n = Some a"
  shows "paper_R_type (G n)"
proof -
  have member: "n \<in> dom g" using assigned by (simp add: dom_def)
  show ?thesis by (rule paper_ZF_action_env_support[OF typed member])
qed

lemma paper_ZF_action_env_empty:
  "paper_ZF_action_env_typed D G W Map.empty"
  by (simp add: paper_ZF_action_env_typed_def named_env_typed_def)

lemma paper_ZF_action_env_update:
  assumes typed: "paper_ZF_action_env_typed D G W g"
    and nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and member: "a \<in> explode (D \<sigma> W)"
  shows "paper_ZF_action_env_typed D G W (g(n := Some a))"
proof (rule paper_ZF_action_envI)
  have at_name: "a \<in> explode (D (G n) W)" using member by (simp only: nt)
  show "named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G (g(n := Some a))"
    by (rule named_assignment_update_typed[where D="\<lambda>\<rho>. explode (D \<rho> W)" and G=G and n=n,
      OF paper_ZF_action_env_named[OF typed] at_name])
next
  fix m
  assume defined: "m \<in> dom (g(n := Some a))"
  show "paper_R_type (G m)"
  proof (cases "m = n")
    case True
    show ?thesis by (simp only: True nt; rule rt)
  next
    case False
    have original: "m \<in> dom g" using defined False by (simp add: named_assignment_update_domain)
    show ?thesis by (rule paper_ZF_action_env_support[OF typed original])
  qed
qed

lemma paper_ZF_action_transport_domain:
  "dom (paper_ZF_action_transport_assignment G T i g) = dom g"
  by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_domain)

lemma paper_ZF_action_transport_adequate_iff:
  "named_adequate (paper_ZF_action_transport_assignment G T i g) M \<longleftrightarrow> named_adequate g M"
  by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_adequate_iff)

lemma paper_ZF_action_transport_update:
  "paper_ZF_action_transport_assignment G T i (g(n := Some a)) =
    (paper_ZF_action_transport_assignment G T i g)(n := Some (T (G n) i a))"
  by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_update)

lemma paper_ZF_action_transport_body_adequate_iff:
  "named_adequate ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) M \<longleftrightarrow>
    named_adequate g (NLam n M)"
  by (simp only: named_binder_update_adequate_iff paper_ZF_action_transport_adequate_iff)

theorem paper_ZF_action_transport_env_typed:
  assumes actions: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow>
      paper_action Obj Arrows source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    and arrow: "i \<in> Arrows" and typed: "paper_ZF_action_env_typed D G (source i) g"
  shows "paper_ZF_action_env_typed D G (target i) (paper_ZF_action_transport_assignment G T i g)"
proof (rule paper_ZF_action_envI)
  show "named_env_typed (\<lambda>\<rho>. explode (D \<rho> (target i))) G (paper_ZF_action_transport_assignment G T i g)"
  proof (unfold named_env_typed_def, intro allI impI)
    fix n b
    assume assigned: "paper_ZF_action_transport_assignment G T i g n = Some b"
    obtain a where old: "g n = Some a" and shape: "b = T (G n) i a"
      using assigned unfolding paper_ZF_action_transport_assignment_def paper_hom_assignment_def
      by (cases "g n") auto
    have rt: "paper_R_type (G n)" by (rule paper_ZF_action_env_assigned_R[OF typed old])
    have member: "a \<in> explode (D (G n) (source i))" by (rule paper_ZF_action_env_value[OF typed old])
    interpret Act: paper_action Obj Arrows source target compose identity "\<lambda>W. explode (D (G n) W)" "T (G n)"
      by (rule actions[OF rt])
    have moved: "T (G n) i a \<in> explode (D (G n) (target i))"
      by (rule Act.transport_type[OF arrow member])
    show "b \<in> explode (D (G n) (target i))" by (simp only: shape; rule moved)
  qed
next
  fix n
  assume defined: "n \<in> dom (paper_ZF_action_transport_assignment G T i g)"
  have original: "n \<in> dom g" using defined by (simp only: paper_ZF_action_transport_domain)
  show "paper_R_type (G n)" by (rule paper_ZF_action_env_support[OF typed original])
qed

corollary paper_ZF_premodel_transport_env_typed:
  assumes premodel: "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
    and arrow: "i \<in> explode A" and typed: "paper_ZF_action_env_typed D G (source i) g"
  shows "paper_ZF_action_env_typed D G (target i) (paper_ZF_action_transport_assignment G T i g)"
proof -
  have actions: "paper_action Obj (explode A) source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    if "paper_R_type \<rho>" for \<rho>
    using premodel that unfolding paper_ZF_action_premodel_def by blast
  show ?thesis by (rule paper_ZF_action_transport_env_typed[OF actions arrow typed])
qed

theorem paper_ZF_action_transport_update_body:
  assumes actions: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow>
      paper_action Obj Arrows source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
    and arrow: "i \<in> Arrows" and typed: "paper_ZF_action_env_typed D G (source i) g"
    and nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>" and member: "a \<in> explode (D \<sigma> (target i))"
    and adequate: "named_adequate g (NLam n M)"
  shows "paper_ZF_action_env_typed D G (target i) ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) \<and>
    named_adequate ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) M"
proof (rule conjI)
  show "paper_ZF_action_env_typed D G (target i) ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
    by (rule paper_ZF_action_env_update[OF paper_ZF_action_transport_env_typed[OF actions arrow typed] nt rt member])
  show "named_adequate ((paper_ZF_action_transport_assignment G T i g)(n := Some a)) M"
    by (rule iffD2[OF paper_ZF_action_transport_body_adequate_iff adequate])
qed

end
