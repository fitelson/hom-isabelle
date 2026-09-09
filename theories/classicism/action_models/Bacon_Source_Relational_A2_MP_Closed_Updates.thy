theory Bacon_Source_Relational_A2_MP_Closed_Updates
  imports Bacon_Source_Relational_Environment_Finite_Identity
begin

section \<open>Two closed function payloads are replaced by one closed truth payload\<close>

text \<open>
  At distinct coordinates x,y of type τ, compare [x↦K,y↦L]
  with [x↦T,y↦T]. Native identities K=T and L=T give identity
  of the two substituted instances of any R template. This is an
  instance of the checked finite-coordinate environment theorem,
  which ultimately uses only Ref, LL and literal β.
  Source role: Appendix A.2's MP step, p.66.
  No general λ-congruence or open-payload transport is assumed.
\<close>

theorem paper_R_two_closed_updates_identity:
  assumes rich: "paper_R_rich G" and template: "paper_R_in_language \<Sigma> G A \<rho>"
    and xt: "G x = \<tau>" and yt: "G y = \<tau>" and distinct: "x \<noteq> y"
    and kc: "K \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    and lc: "L \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    and tc: "T \<in> paper_R_closed_terms \<Sigma> G \<tau>"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> K T)"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> L T)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<rho>
    (paper_R_environment_subst ((Map.empty(x := Some K))(y := Some L)) A)
    (paper_R_environment_subst ((Map.empty(x := Some T))(y := Some T)) A))"
proof -
  let ?r = "(Map.empty(x := Some K))(y := Some L)"
  let ?s = "(Map.empty(x := Some T))(y := Some T)"
  have empty_typed: "paper_R_closed_term_assignment \<Sigma> G Map.empty"
    by (simp add: paper_R_closed_term_assignment_def)
  have kx: "K \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule kc)
  have ly: "L \<in> paper_R_closed_terms \<Sigma> G (G y)" by (simp only: yt; rule lc)
  have tx: "T \<in> paper_R_closed_terms \<Sigma> G (G x)" by (simp only: xt; rule tc)
  have ty: "T \<in> paper_R_closed_terms \<Sigma> G (G y)" by (simp only: yt; rule tc)
  have rt: "paper_R_closed_term_assignment \<Sigma> G ?r"
    by (rule paper_R_closed_term_assignment_update[OF paper_R_closed_term_assignment_update[OF empty_typed kx] ly])
  have st: "paper_R_closed_term_assignment \<Sigma> G ?s"
    by (rule paper_R_closed_term_assignment_update[OF paper_R_closed_term_assignment_update[OF empty_typed tx] ty])
  have domains: "dom ?r = dom ?s" by (auto simp: dom_def)
  have coordinates: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (G n) B C)"
    if ra: "?r n = Some B" and sa: "?s n = Some C" for n B C
  proof (cases "n = y")
    case True
    have bs: "B = L" and cs: "C = T" using ra sa True by simp_all
    show ?thesis by (simp only: True yt bs cs; rule second)
  next
    case False
    have nx: "n = x" and bs: "B = K" using ra False by (auto split: if_splits)
    have cs: "C = T" using sa nx distinct by simp
    show ?thesis by (simp only: nx xt bs cs; rule first)
  qed
  show ?thesis by (rule paper_R_environment_subst_assignment_identity[OF rich template rt st domains coordinates])
qed

end
