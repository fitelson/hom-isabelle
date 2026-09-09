theory Bacon_Source_Relational_Figure3_Certificates
  imports Bacon_Source_Relational_Figure3_Language
    Bacon_Source_Relational_Distribution_PC Bacon_Source_Relational_Classicism_Presentation
begin

section \<open>Native H certificates for the six displayed Boolean laws\<close>

fun paper_R_figure3_template :: "paper_R_figure3_law \<Rightarrow> nat sprop_template" where
  "paper_R_figure3_template RCommAnd =
    SPIff (SPAnd (SPAtom 0) (SPAtom 1)) (SPAnd (SPAtom 1) (SPAtom 0))"
| "paper_R_figure3_template RCommOr =
    SPIff (SPOr (SPAtom 0) (SPAtom 1)) (SPOr (SPAtom 1) (SPAtom 0))"
| "paper_R_figure3_template RDistAndOr =
    SPIff (SPAnd (SPAtom 0) (SPOr (SPAtom 1) (SPAtom 2)))
      (SPOr (SPAnd (SPAtom 0) (SPAtom 1)) (SPAnd (SPAtom 0) (SPAtom 2)))"
| "paper_R_figure3_template RDistOrAnd =
    SPIff (SPOr (SPAtom 0) (SPAnd (SPAtom 1) (SPAtom 2)))
      (SPAnd (SPOr (SPAtom 0) (SPAtom 1)) (SPOr (SPAtom 0) (SPAtom 2)))"
| "paper_R_figure3_template RDissolveAndOr =
    SPIff (SPAnd (SPAtom 0) (SPOr (SPAtom 1) (SPNot (SPAtom 1)))) (SPAtom 0)"
| "paper_R_figure3_template RDissolveOrAnd =
    SPIff (SPOr (SPAtom 0) (SPAnd (SPAtom 1) (SPNot (SPAtom 1)))) (SPAtom 0)"

lemma paper_R_figure3_template_tautology:
  "sprop_tautology (paper_R_figure3_template law)"
  by (cases law; auto simp: sprop_tautology_def)

lemma paper_R_figure3_template_literal:
  "named_paper_prop_instance G (\<lambda>j. if j=0 then NVar p else if j=1 then NVar q else NVar r)
      (paper_R_figure3_template law) =
    named_paper_iff G (paper_R_figure3_left law p q r) (paper_R_figure3_right law p q r)"
  by (cases law; simp)

theorem paper_R_named_H_figure3_biconditional:
  assumes rich: "paper_R_rich G" and variables: "paper_R_figure3_variables G p q r"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_iff G (paper_R_figure3_left law p q r) (paper_R_figure3_right law p q r))"
proof -
  have pl: "paper_R_in_language \<Sigma> G (NVar p) Prop"
    by (rule paper_R_figure3_variable_languages(1)[OF variables])
  have ql: "paper_R_in_language \<Sigma> G (NVar q) Prop"
    by (rule paper_R_figure3_variable_languages(2)[OF variables])
  have rl: "paper_R_in_language \<Sigma> G (NVar r) Prop"
    by (rule paper_R_figure3_variable_languages(3)[OF variables])
  have certificate: "paper_R_named_H \<Sigma> G
      (named_paper_prop_instance G (\<lambda>j. if j=0 then NVar p else if j=1 then NVar q else NVar r)
        (paper_R_figure3_template law))"
    by (rule paper_R_named_H_ternary_PC[
      OF rich pl ql rl paper_R_figure3_template_tautology])
  show ?thesis using certificate by (simp only: paper_R_figure3_template_literal)
qed

section \<open>Each closed Figure 3 identity is a native C theorem\<close>

theorem paper_R_classicism_figure3:
  assumes rich: "paper_R_rich G" and variables: "paper_R_figure3_variables G p q r"
  shows "paper_R_classicism_proves \<Sigma> G (paper_R_figure3_axiom G law p q r)"
  unfolding paper_R_figure3_axiom_def
  by (rule paper_R_classicism_proves.Logical_Equivalence[
    OF paper_R_named_H_figure3_biconditional[OF rich variables]
      paper_R_figure3_body_languages(1)[OF variables]
      paper_R_figure3_body_languages(2)[OF variables] paper_R_figure3_prefix_R[OF variables]])

corollary paper_R_classicism_figure3_member:
  assumes rich: "paper_R_rich G" and variables: "paper_R_figure3_variables G p q r"
    and member: "A \<in> set (paper_R_figure3_axioms G p q r)"
  shows "paper_R_classicism_proves \<Sigma> G A"
proof -
  obtain law where shape: "A = paper_R_figure3_axiom G law p q r"
    using member unfolding paper_R_figure3_axioms_def by auto
  show ?thesis by (simp only: shape; rule paper_R_classicism_figure3[OF rich variables])
qed

text \<open>
  The H proof is an explicit native R-PC instance of the displayed
  Boolean template. Its conclusion is the literal λ-defined
  biconditional, and native Logical Equivalence supplies exactly the
  closed two- or three-binder operator identity of Figure 3.

  These are forward membership certificates in the p.12 C calculus.
  They do not identify a six-axiom Boolean presentation with Booleanism,
  prove Figure 4, or establish the reverse Figures 3–4 presentation.
  No F proof transport, semantic model or completeness theorem is used.
\<close>

end
