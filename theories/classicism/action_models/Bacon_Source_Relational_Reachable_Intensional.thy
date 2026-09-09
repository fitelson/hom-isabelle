theory Bacon_Source_Relational_Reachable_Intensional
  imports Bacon_Source_Relational_Reachable_Subcategory Bacon_Source_Relational_Intensional_Restriction
begin

section \<open>The rooted restriction retains intensionality\<close>

text \<open>
  Every outgoing arrow from a reachable object remains in the restricted
  category: compose it with an arrow from M₀. Consequently its intension
  tests are unchanged, and original intensionality is inherited.
  Source: Proposition 3.22, pp.57 and 72, using Definition 3.11,
  pp.50–51. This proves the rooted-category preparation, not the
  simultaneous action-family or action-model construction.

  Records and valuations are unchanged, but the object collection is
  smaller. No equality of the two common theories is asserted; deleting
  objects can enlarge that theory. No new homomorphisms are added.
\<close>

theorem paper_R_bbk_reachable_intensional:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  shows "paper_R_intensional_on \<Sigma> G
    (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
    (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)"
proof -
  let ?Obj = "paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0"
  let ?Arrows = "paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0"
  have subset: "?Obj \<subseteq> Obj" by (rule paper_R_bbk_reachable_objects_subset[OF category])
  have outgoing: "(h \<in> ?Arrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
      (h \<in> Arrows \<and> paper_arrow_source h = M)" if "M \<in> ?Obj" for M h
    by (rule paper_R_bbk_reachable_outgoing_iff[OF category that])
  show ?thesis by (rule paper_R_intensional_outgoing_restrict[OF subset outgoing intensional])
qed

theorem paper_R_bbk_reachable_intensional_rooted:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows" and root: "M0 \<in> Obj"
  shows "paper_R_bbk_subcategory \<Sigma> G
      (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
      (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0) \<and>
    paper_R_intensional_on \<Sigma> G
      (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
      (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0) \<and>
    paper_rooted_category
      (paper_reachable_objects Arrows paper_arrow_source paper_arrow_target M0)
      (paper_reachable_arrows Arrows paper_arrow_source paper_arrow_target M0)
      paper_arrow_source paper_arrow_target (paper_typed_compose paper_bbk_domain)
      (paper_typed_identity paper_bbk_domain) M0"
  by (rule conjI[OF paper_R_bbk_reachable_subcategory[OF category]],
    rule conjI[OF paper_R_bbk_reachable_intensional[OF category intensional]
      paper_R_bbk_reachable_rooted_category[OF category root]])

end
