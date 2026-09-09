theory Bacon_Source_ZF_Action_BBK_Interpretation
  imports Bacon_Source_ZF_Action_BBK_Domains Bacon_Source_ZF_Evaluation_Locality
begin

section \<open>The candidate interpretation at each root arrow\<close>

text \<open>
  For h:Root→W, put Jₕ(g,A)=the(⟦A⟧gₕ) and Vₕ(p) iff idW∈p.
  The independent action-model condition supplies an actual Some value
  at each typed adequate source-language input; the choice at None is
  never used to establish a meaningful denotation. Domains are the
  existing normalized family, empty at non-R indices.
  Source: Definition 3.1, pp.43–44, and Proposition 3.21, p.70.

  These are structural interpretation facts only. No BBK-model predicate
  is assumed or concluded, and conversion and logical truth clauses
  remain separate. The arrow h is arbitrary among root arrows, not
  necessarily the identity or a chosen unique arrow.
\<close>

definition paper_ZF_action_bbk_denote ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow>
    ZF \<Rightarrow> ZF named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> ZF" where
  "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A =
    the (paper_ZF_action_eval Ar source target compose identity D T I G A h g)"

definition paper_ZF_action_bbk_valuation :: "(ZF \<Rightarrow> 'o) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "paper_ZF_action_bbk_valuation target identity h p \<longleftrightarrow> Elem (identity (target h)) p"

lemma paper_ZF_action_bbk_denote_total:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and language: "paper_R_in_language \<Sigma> G A \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
      Some (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A) \<and>
    paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A
      \<in> paper_ZF_action_bbk_domain D (target h) \<rho>"
proof -
  have action_typed: "paper_ZF_action_env_typed D G (target h) g"
    using typed by (simp only: paper_ZF_action_bbk_env_iff)
  obtain v where evaluated: "paper_ZF_action_eval Ar source target compose identity D T I G A h g = Some v"
    and member: "v \<in> explode (D \<rho> (target h))"
    using model language arrow origin action_typed adequate unfolding paper_ZF_action_model_def by blast
  have selected: "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A = v"
    by (simp add: paper_ZF_action_bbk_denote_def evaluated)
  have rt: "paper_R_type \<rho>" by (rule paper_R_language_result_type[OF language])
  show ?thesis by (simp only: selected paper_ZF_action_bbk_domain_R[OF rt]; rule conjI[OF evaluated member])
qed

lemma paper_ZF_action_bbk_denote_value:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and language: "paper_R_in_language \<Sigma> G A \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    Some (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A)"
  by (rule conjunct1[OF paper_ZF_action_bbk_denote_total[OF model language arrow origin typed adequate]])

lemma paper_ZF_action_bbk_denote_type:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and language: "paper_R_in_language \<Sigma> G A \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A
    \<in> paper_ZF_action_bbk_domain D (target h) \<rho>"
  by (rule conjunct2[OF paper_ZF_action_bbk_denote_total[OF model language arrow origin typed adequate]])

lemma paper_ZF_action_bbk_denote_var:
  assumes assigned: "g n = Some a"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NVar n) = a"
  by (simp add: paper_ZF_action_bbk_denote_def assigned)

section \<open>Actual graph application gives heterogeneous congruence\<close>

lemma paper_ZF_action_bbk_denote_application_data:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g (NApp F A)"
  shows "isFun (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F) \<and>
    Elem (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A))
      (Domain (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F)) \<and>
    paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp F A) =
      app (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F)
        (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A))"
proof -
  have fa: "named_adequate g F" and aa: "named_adequate g A" using adequate by (auto simp: named_adequate_def)
  have language: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>" by (rule paper_R_language_App[OF head argument])
  have fv: "paper_ZF_action_eval Ar source target compose identity D T I G F h g =
      Some (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F)"
    by (rule paper_ZF_action_bbk_denote_value[OF model head arrow origin typed fa])
  have av: "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
      Some (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A)"
    by (rule paper_ZF_action_bbk_denote_value[OF model argument arrow origin typed aa])
  have whole: "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F A) h g =
      Some (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp F A))"
    by (rule paper_ZF_action_bbk_denote_value[OF model language arrow origin typed adequate])
  show ?thesis using whole
    by (simp only: paper_ZF_action_eval_application_Some_iff fv av option.inject; blast)
qed

lemma paper_ZF_action_bbk_denote_application:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g (NApp F A)"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp F A) =
    app (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F)
      (Opair (identity (target h)) (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A))"
  using paper_ZF_action_bbk_denote_application_data[OF model head argument arrow origin typed adequate] by blast

theorem paper_ZF_action_bbk_denote_application_cong:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" and al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<upsilon> \<rho>)" and bl: "paper_R_in_language \<Sigma> G B \<upsilon>"
    and gt: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and kt: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G k"
    and ga: "named_adequate g (NApp F A)" and ka: "named_adequate k (NApp H B)"
    and heads: "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g F =
      paper_ZF_action_bbk_denote Ar source target compose identity D T I G h k H"
    and arguments: "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A =
      paper_ZF_action_bbk_denote Ar source target compose identity D T I G h k B"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g (NApp F A) =
    paper_ZF_action_bbk_denote Ar source target compose identity D T I G h k (NApp H B)"
  by (simp only: paper_ZF_action_bbk_denote_application[OF model fl al arrow origin gt ga]
    paper_ZF_action_bbk_denote_application[OF model hl bl arrow origin kt ka] heads arguments)

section \<open>Locality and the direct truth comparison\<close>

lemma paper_ZF_action_bbk_denote_locality:
  assumes agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
  shows "paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A =
    paper_ZF_action_bbk_denote Ar source target compose identity D T I G h k A"
  by (simp only: paper_ZF_action_bbk_denote_def paper_ZF_action_eval_locality[OF agree])

theorem paper_ZF_action_bbk_holds_iff:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity Root D T I"
    and language: "paper_R_in_language \<Sigma> G A Prop"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and typed: "named_env_typed (paper_ZF_action_bbk_domain D (target h)) G g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_action_holds Ar source target compose identity D T I G h g A \<longleftrightarrow>
    paper_ZF_action_bbk_valuation target identity h
      (paper_ZF_action_bbk_denote Ar source target compose identity D T I G h g A)"
  by (simp only: paper_ZF_action_holds_def paper_ZF_action_bbk_valuation_def
    paper_ZF_action_bbk_denote_value[OF model language arrow origin typed adequate] option.inject; auto)

end
