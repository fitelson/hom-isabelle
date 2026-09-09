theory Bacon_Source_Relational_Conversion_Truth
  imports Bacon_Source_Relational_Logical_Truth
begin

section \<open>Literal conversion biconditionals are valid\<close>

text \<open>
  R-typed βη-equivalent formulas A and B have the same denotation
  at every typed assignment adequate for both. The literal formula
  A↔B is therefore valid. Source: Figure 2, p.8, and Definition
  3.1(ii.d), p.44.

  This semantic lemma accepts an R conversion chain. The independent
  H judgment still has only the printed one-step β and η axiom
  schemes; it does not acquire a whole-chain constructor.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_conversion_biconditional_valid:
  assumes conversion: "paper_R_raw_beta_eta stock Prop A B"
    and al: "paper_R_in_language signature stock A Prop"
    and bl: "paper_R_in_language signature stock B Prop"
  shows "paper_R_valid (named_paper_iff stock A B)"
proof (unfold paper_R_valid_def, rule conjI)
  show "paper_R_in_language signature stock (named_paper_iff stock A B) Prop"
    by (rule paper_R_named_paper_iff_language[OF stock_rich al bl])
next
  show "\<forall>g. named_env_typed domain stock g \<longrightarrow>
    named_adequate g (named_paper_iff stock A B) \<longrightarrow>
    paper_R_satisfies g (named_paper_iff stock A B)"
  proof (intro allI impI)
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_iff stock A B)"
    have aa: "named_adequate g A" and ba: "named_adequate g B"
      using adequate by (auto simp: named_adequate_def named_paper_defined_fv)
    have equal: "denote g A = denote g B"
      by (rule denote_beta_eta[OF conversion al bl typed aa ba])
    show "paper_R_satisfies g (named_paper_iff stock A B)"
      unfolding paper_R_satisfies_def
      by (simp only: paper_R_named_paper_iff_truth[OF al bl typed aa ba] equal)
  qed
qed

end

end
