theory Bacon_Source_ZF_Action_Premodel
  imports Bacon_Source_ZF_Exponential_Action Bacon_Source_ZF_Powerset_Action
    Bacon_Classicism_Action_Development.Bacon_Source_Rooted_Category
    Bacon_Classicism_Action_Development.Bacon_Source_Subaction
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Types
begin

section \<open>Independent coded action premodels\<close>

text \<open>
  Definition 3.18 (p.55): A=⟨𝒞,W₀,−⋅,I⟩ has a rooted
  category, an action at each source type, nonempty individual
  fibers, proposition and function subactions, and root values
  for the nonlogical constants of Σ. The type index is R, the
  paper's default language; the surrounding otype datatype also
  contains non-R indices, on which this predicate makes no claim.

  This is an independent definition, not a field asserting that
  any BBK representation has succeeded. Arrows and values have
  actual ZF codes; powersets and coherent exponential graphs are
  the previously constructed internal sets. All their transports
  are the explicit canonical maps. There is no PER quotient.

  No interpretation, application closure, logical-constant closure,
  or totality assumption is included. Those are separate obligations
  in Definitions 3.19–3.20. In particular, only the individual
  domains are required nonempty here.
\<close>

definition paper_ZF_action_premodel ::
  "'c ssignature \<Rightarrow> 'o set \<Rightarrow> ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> bool" where
  "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I \<longleftrightarrow>
    paper_rooted_category Obj (explode A) source target compose identity root \<and>
    (\<forall>\<rho>. paper_R_type \<rho> \<longrightarrow>
      paper_action Obj (explode A) source target compose identity (\<lambda>M. explode (D \<rho> M)) (T \<rho>)) \<and>
    (\<forall>M\<in>Obj. explode (D Ind M) \<noteq> {}) \<and>
    paper_subaction Obj (explode A) source target compose identity
      (\<lambda>M. explode (D Prop M)) (T Prop)
      (\<lambda>M. explode (paper_ZF_powerset_code A source M))
      (paper_ZF_powerset_transport_code A source target compose) \<and>
    (\<forall>\<sigma> \<tau>. paper_R_type (Arr \<sigma> \<tau>) \<longrightarrow>
      paper_subaction Obj (explode A) source target compose identity
        (\<lambda>M. explode (D (Arr \<sigma> \<tau>) M)) (T (Arr \<sigma> \<tau>))
        (\<lambda>M. explode (paper_ZF_exponential_code A source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) M))
        (paper_ZF_exponential_transport_code A source target compose (D \<sigma>))) \<and>
    (\<forall>\<rho>. paper_R_type \<rho> \<longrightarrow> (\<forall>c\<in>\<Sigma> \<rho>. I \<rho> c \<in> explode (D \<rho> root)))"

lemma paper_ZF_action_premodelI:
  assumes rooted: "paper_rooted_category Obj (explode A) source target compose identity root"
    and actions: "\<And>\<rho>. paper_R_type \<rho> \<Longrightarrow>
      paper_action Obj (explode A) source target compose identity (\<lambda>M. explode (D \<rho> M)) (T \<rho>)"
    and individuals: "\<And>M. M \<in> Obj \<Longrightarrow> explode (D Ind M) \<noteq> {}"
    and propositions: "paper_subaction Obj (explode A) source target compose identity
      (\<lambda>M. explode (D Prop M)) (T Prop)
      (\<lambda>M. explode (paper_ZF_powerset_code A source M))
      (paper_ZF_powerset_transport_code A source target compose)"
    and function_subactions: "\<And>\<sigma> \<tau>. paper_R_type (Arr \<sigma> \<tau>) \<Longrightarrow>
      paper_subaction Obj (explode A) source target compose identity
        (\<lambda>M. explode (D (Arr \<sigma> \<tau>) M)) (T (Arr \<sigma> \<tau>))
        (\<lambda>M. explode (paper_ZF_exponential_code A source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) M))
        (paper_ZF_exponential_transport_code A source target compose (D \<sigma>))"
    and constants: "\<And>\<rho> c. paper_R_type \<rho> \<Longrightarrow> c \<in> \<Sigma> \<rho> \<Longrightarrow> I \<rho> c \<in> explode (D \<rho> root)"
  shows "paper_ZF_action_premodel \<Sigma> Obj A source target compose identity root D T I"
  using assms unfolding paper_ZF_action_premodel_def by blast

end
