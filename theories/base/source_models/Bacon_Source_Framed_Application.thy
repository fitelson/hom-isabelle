theory Bacon_Source_Framed_Application
  imports Bacon_Source_Framed_Denotation
begin

section \<open>Framed application congruence across contexts and types\<close>

text \<open>
  If F and H have equal denotations, and A and B have equal denotations,
  FA and HB have equal denotations. The two applications may initially
  have different argument and result types, and different finite frames.
  Source: the literal heterogeneous clause in Bacon–Dorr Definition 3.1(ii.b),
  p.44. The compared assignments need not be the same.

  Isabelle representation. Unfold the two independent chart choices and
  use the already proved chart application clause. No domain disjointness,
  Functionality, equality of frames, or context-erasure result is assumed.
\<close>

context paper_named_bbk_model
begin

theorem framed_denote_application:
  assumes fl: "sterm_in_language paper_logical_type signature \<Gamma> F (Arr \<sigma> \<tau>)"
    and al: "sterm_in_language paper_logical_type signature \<Gamma> A \<sigma>"
    and hl: "sterm_in_language paper_logical_type signature \<Delta> H (Arr \<upsilon> \<omega>)"
    and bl: "sterm_in_language paper_logical_type signature \<Delta> B \<upsilon>"
    and re: "pbbk_env_typed domain \<Gamma> \<rho>" and se: "pbbk_env_typed domain \<Delta> \<xi>"
    and heads: "framed_denote \<Gamma> \<rho> F = framed_denote \<Delta> \<xi> H"
    and arguments: "framed_denote \<Gamma> \<rho> A = framed_denote \<Delta> \<xi> B"
  shows "framed_denote \<Gamma> \<rho> (SApp F A) = framed_denote \<Delta> \<xi> (SApp H B)"
proof -
  have gc: "named_chart stock \<Gamma> (named_chart_choice stock \<Gamma>)"
    by (rule named_chart_choice_valid[OF stock_rich])
  have dc: "named_chart stock \<Delta> (named_chart_choice stock \<Delta>)"
    by (rule named_chart_choice_valid[OF stock_rich])
  have chart_heads: "chart_denote (named_chart_choice stock \<Gamma>) \<rho> F =
    chart_denote (named_chart_choice stock \<Delta>) \<xi> H"
    using heads unfolding framed_denote_def .
  have chart_arguments: "chart_denote (named_chart_choice stock \<Gamma>) \<rho> A =
    chart_denote (named_chart_choice stock \<Delta>) \<xi> B"
    using arguments unfolding framed_denote_def .
  show ?thesis unfolding framed_denote_def
    by (rule chart_denote_application[OF fl al hl bl gc dc re se chart_heads chart_arguments])
qed

end

end
