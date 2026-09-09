theory Bacon_Source_ZF_Partial_Abstraction
  imports Bacon_Source_ZF_Action_Assignments Bacon_Source_ZF_Outgoing_Pairs
begin

section \<open>Partial abstraction over every outgoing pair\<close>

text \<open>
  Definition 3.19 (p.56) interprets λv.A at h by the graph
  ⟨i,a⟩ ↦ ⟦A⟧(i∘h,(i∘g)[v↦a]). The helper below takes the
  recursively interpreted BODY as a function of arrow and assignment.
  It requires that body to be defined at every legitimate pair.
  Transport precedes the update; an existing value of v is shadowed.

  This is a mathematical partial construction, not a decision procedure
  for an infinite definedness test. A graph on an empty pair domain
  is permitted. Membership in the selected function domain is NOT
  tested here: that is a separate Definition 3.20 requirement.
\<close>

definition paper_ZF_action_abstraction_body ::
  "(ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow>
    sgcontext \<Rightarrow> nat \<Rightarrow> (ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option) \<Rightarrow>
    ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF \<Rightarrow> ZF option" where
  "paper_ZF_action_abstraction_body compose T G n B h g z =
    B (compose (Fst z) h)
      ((paper_ZF_action_transport_assignment G T (Fst z) g)(n := Some (Snd z)))"

definition paper_ZF_action_abstract ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow>
    (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> (otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow>
    (otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow>
    (ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option) \<Rightarrow>
    ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option" where
  "paper_ZF_action_abstract A source target compose D T G n B h g =
    (let P = paper_ZF_pair_code A source target (D (G n)) (target h);
         V = paper_ZF_action_abstraction_body compose T G n B h g
     in if (\<forall>z\<in>explode P. V z \<noteq> None)
        then Some (Lambda P (\<lambda>z. the (V z))) else None)"

lemma paper_ZF_action_abstraction_body_pair:
  "paper_ZF_action_abstraction_body compose T G n B h g (Opair i a) =
    B (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
  by (simp only: paper_ZF_action_abstraction_body_def Fst Snd)

lemma paper_ZF_action_abstract_defined:
  assumes defined: "\<And>z. z \<in> explode (paper_ZF_pair_code A source target (D (G n)) (target h)) \<Longrightarrow>
    paper_ZF_action_abstraction_body compose T G n B h g z \<noteq> None"
  shows "paper_ZF_action_abstract A source target compose D T G n B h g =
    Some (Lambda (paper_ZF_pair_code A source target (D (G n)) (target h))
      (\<lambda>z. the (paper_ZF_action_abstraction_body compose T G n B h g z)))"
  using defined by (simp add: paper_ZF_action_abstract_def Let_def)

lemma paper_ZF_action_abstract_None_iff:
  "paper_ZF_action_abstract A source target compose D T G n B h g = None \<longleftrightarrow>
    (\<exists>z\<in>explode (paper_ZF_pair_code A source target (D (G n)) (target h)).
      paper_ZF_action_abstraction_body compose T G n B h g z = None)"
  by (auto simp: paper_ZF_action_abstract_def Let_def)

lemma paper_ZF_action_abstract_graph:
  assumes returned: "paper_ZF_action_abstract A source target compose D T G n B h g = Some F"
  shows "isFun F \<and> Domain F = paper_ZF_pair_code A source target (D (G n)) (target h)"
  using returned by (auto simp: paper_ZF_action_abstract_def Let_def isFun_Lambda domain_Lambda split: if_splits)

lemma paper_ZF_action_abstract_apply:
  assumes returned: "paper_ZF_action_abstract A source target compose D T G n B h g = Some F"
    and pair: "Elem (Opair i a) (paper_ZF_pair_code A source target (D (G n)) (target h))"
  shows "Some (app F (Opair i a)) =
    B (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
proof -
  let ?P = "paper_ZF_pair_code A source target (D (G n)) (target h)"
  let ?V = "paper_ZF_action_abstraction_body compose T G n B h g"
  have defined: "\<forall>z\<in>explode ?P. ?V z \<noteq> None"
    and shape: "F = Lambda ?P (\<lambda>z. the (?V z))"
    using returned by (auto simp: paper_ZF_action_abstract_def Let_def split: if_splits)
  have at_pair: "?V (Opair i a) \<noteq> None"
    using defined pair by (simp only: explode_Elem; blast)
  have recover: "Some (the (?V (Opair i a))) = ?V (Opair i a)"
    using at_pair by (cases "?V (Opair i a)") auto
  have body_recover: "Some (the (B (compose i h)
      ((paper_ZF_action_transport_assignment G T i g)(n := Some a)))) =
      B (compose i h) ((paper_ZF_action_transport_assignment G T i g)(n := Some a))"
    using recover by (simp only: paper_ZF_action_abstraction_body_pair)
  show ?thesis
    by (simp only: shape Lambda_app[OF pair] paper_ZF_action_abstraction_body_pair;
      rule body_recover)
qed

end
