theory Bacon_Source_ZF_Action_Model
  imports Bacon_Source_ZF_Partial_Interpretation
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Syntax
begin

section \<open>The independent totality and membership condition\<close>

text \<open>
  Definition 3.20 (p.56) requires defined interpretation and
  membership in Wρ for EVERY type-ρ term, EVERY root arrow
  h:W₀→W, and EVERY adequate assignment at W. The rich R stock
  records the source language's infinitely many variables of each
  R type (§1.1, p.5). It is not a full-F richness assumption.

  This predicate uses the independently defined recursive partial
  interpretation. It is not an assumed interpretation satisfying
  the desired equations, or a definition via an old BBK model.
  Nothing in this leaf proves that a supplied or constructed
  premodel meets the condition.
\<close>

definition paper_ZF_action_model ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'o set \<Rightarrow> ZF \<Rightarrow>
    (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    ('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> bool" where
  "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I \<longleftrightarrow>
    paper_R_rich G \<and>
    paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity root D T I \<and>
    (\<forall>B \<rho> h g. paper_R_in_language \<Sigma> G B \<rho> \<longrightarrow>
      h \<in> explode Ar \<longrightarrow> source h = root \<longrightarrow>
      paper_ZF_action_env_typed D G (target h) g \<longrightarrow> named_adequate g B \<longrightarrow>
      (\<exists>v. paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some v \<and>
        v \<in> explode (D \<rho> (target h))))"

definition paper_ZF_action_holds ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow>
    ZF \<Rightarrow> ZF named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_ZF_action_holds Ar source target compose identity D T I G h g P \<longleftrightarrow>
    (\<exists>p. paper_ZF_action_eval Ar source target compose identity D T I G P h g = Some p \<and>
      Elem (identity (target h)) p)"

text \<open>
  The last predicate is A,h,g ⊩ P. Root truth uses h=1W₀;
  it does not quantify over root arrows or select a unique one.
  Typing/adequacy guards belong to claims using this raw predicate.
  Logical truth laws, βη invariance, soundness and completeness
  have not been proved by these declarations.
\<close>

end
