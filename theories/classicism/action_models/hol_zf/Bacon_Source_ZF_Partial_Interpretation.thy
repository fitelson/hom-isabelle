theory Bacon_Source_ZF_Partial_Interpretation
  imports Bacon_Source_ZF_Partial_Abstraction Bacon_Source_ZF_Logical_Values
    Bacon_Source_ZF_Graph_Application
begin

section \<open>The independent partial interpretation of Definition 3.19\<close>

text \<open>
  ⟦A⟧g_h is represented by Some(v) when defined and None
  otherwise. This structural recursion follows p.56: variables
  consult g; constants are transported from I; the six logical
  families use their literal graphs; application checks that its
  function graph has the identity pair in its domain; abstraction
  interprets the strict body at every outgoing pair.

  The raw operations have arbitrary inputs, but source interpretation
  claims concern R terms, root arrows and R-supported adequate
  assignments. These guards will be explicit in the action-model
  definition. No old BBK interpretation or representation map
  occurs in this definition.

  Domain membership is not built into evaluation. A defined graph
  can fail to belong to the selected stock; Definition 3.20 requires
  both definedness AND correct-domain membership separately.
  The recursion is mathematical, not a decision algorithm for the
  potentially infinite abstraction-definedness condition.
\<close>

primrec paper_ZF_action_eval ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> 'c \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow>
    'c paper_named_term \<Rightarrow> ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option" where
  "paper_ZF_action_eval Ar source target compose identity D T I G (NVar n) h g = g n"
| "paper_ZF_action_eval Ar source target compose identity D T I G (NConst c \<rho>) h g =
    Some (T \<rho> h (I \<rho> c))"
| "paper_ZF_action_eval Ar source target compose identity D T I G (NLogical l) h g =
    Some (paper_ZF_logical_value Ar source target compose identity D T (target h) l)"
| "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g =
    (case paper_ZF_action_eval Ar source target compose identity D T I G F h g of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case paper_ZF_action_eval Ar source target compose identity D T I G B h g of
        None \<Rightarrow> None
      | Some b \<Rightarrow> paper_ZF_graph_apply f (Opair (identity (target h)) b)))"
| "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h g =
    paper_ZF_action_abstract Ar source target compose D T G n
      (paper_ZF_action_eval Ar source target compose identity D T I G B) h g"

lemma paper_ZF_action_eval_application_Some_iff:
  "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g = Some v \<longleftrightarrow>
    (\<exists>f b. paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f \<and>
      paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b \<and>
      isFun f \<and> Elem (Opair (identity (target h)) b) (Domain f) \<and>
      v = app f (Opair (identity (target h)) b))"
  by (auto simp: paper_ZF_action_eval.simps paper_ZF_graph_apply_Some_iff split: option.splits)

lemma paper_ZF_action_eval_application:
  assumes head: "paper_ZF_action_eval Ar source target compose identity D T I G F h g = Some f"
    and argument: "paper_ZF_action_eval Ar source target compose identity D T I G B h g = Some b"
    and graph: "isFun f" and pair: "Elem (Opair (identity (target h)) b) (Domain f)"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G (NApp F B) h g =
    Some (app f (Opair (identity (target h)) b))"
  by (simp only: paper_ZF_action_eval.simps head argument option.case;
    rule paper_ZF_graph_apply_defined_value[OF graph pair])

lemma paper_ZF_action_eval_abstraction_apply:
  assumes returned: "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h g = Some F"
    and pair: "Elem (Opair i a) (paper_ZF_pair_code Ar source target (D (G n)) (target h))"
  shows "Some (app F (Opair i a)) =
    paper_ZF_action_eval Ar source target compose identity D T I G B (compose i h)
      ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
proof -
  have abstraction: "paper_ZF_action_abstract Ar source target compose D T G n
      (paper_ZF_action_eval Ar source target compose identity D T I G B) h g = Some F"
    using returned by (simp only: paper_ZF_action_eval.simps)
  show ?thesis by (rule paper_ZF_action_abstract_apply[OF abstraction pair])
qed

lemma paper_ZF_action_eval_abstraction_None_iff:
  "paper_ZF_action_eval Ar source target compose identity D T I G (NLam n B) h g = None \<longleftrightarrow>
    (\<exists>z\<in>explode (paper_ZF_pair_code Ar source target (D (G n)) (target h)).
      paper_ZF_action_eval Ar source target compose identity D T I G B (compose (Fst z) h)
        ((paper_ZF_action_transport_assignment G T (Fst z) g)(n := Some (Snd z))) = None)"
  by (simp only: paper_ZF_action_eval.simps paper_ZF_action_abstract_None_iff
    paper_ZF_action_abstraction_body_def)

end
