theory Bacon_Source_Relational_Identity_Model
  imports Bacon_Source_Relational_Henkin_Domain_Inhabitation
    Bacon_Source_Relational_Identity_Application_Congruence Bacon_Source_Relational_Identity_Conversion
    Bacon_Source_Relational_Identity_Identity_Truth Bacon_Source_Relational_Identity_Quantifier_Truth
    Bacon_Source_Relational_BBK_Interface
begin

section \<open>The canonical identity-class structure is an independent R-BBK model\<close>

text \<open>
  Dσ consists of typed closed R terms modulo locally derivable identity.
  J substitutes chosen closed representatives into the term, and V tests
  whether a proposition representative belongs to M. Each of the source
  BBK clauses is established below from the separately proved native
  syntactic and class-algebra facts. Source: Theorem 3.2, p.45 n.64.

  The only premises are R-richness and the explicit CLOSED Henkin-theory
  properties. There is no BBK-model premise, extra valuation law,
  Functionality, full-F stock or total-assignment completion. Empty
  off-R fibers are the existing ambient-index convention. The actual
  Henkin extension theorem constructs the syntactic premise separately.

  This certificate uses the fixed representative selector. The separate
  Arbitrary_Representatives theory proves the stronger characterization
  using every alternative closed representative assignment. It is not
  an assumption of this model certificate.
\<close>

theorem paper_R_identity_bbk_model:
  assumes rich: "paper_R_rich G" and Henkin: "paper_R_closed_Henkin_theory \<Omega> G M"
  shows "paper_R_bbk_model \<Omega> G (paper_R_identity_domain \<Omega> G M)
    (paper_R_identity_denote \<Omega> G M) (paper_R_identity_valuation M)"
proof (rule paper_R_bbk_model.intro)
  show "paper_R_rich G" by (rule rich)
next
  fix \<sigma>
  assume rt: "paper_R_type \<sigma>"
  show "paper_R_identity_domain \<Omega> G M \<sigma> \<noteq> {}"
    by (rule paper_R_closed_Henkin_identity_domain_nonempty[OF rich Henkin rt])
next
  fix \<sigma>
  assume outside: "\<not> paper_R_type \<sigma>"
  show "paper_R_identity_domain \<Omega> G M \<sigma> = {}" by (rule paper_R_identity_domain_nonR[OF outside])
next
  fix A \<sigma> g
  assume language: "paper_R_in_language \<Omega> G A \<sigma>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and adequate: "named_adequate g A"
  show "paper_R_identity_denote \<Omega> G M g A \<in> paper_R_identity_domain \<Omega> G M \<sigma>"
    by (rule paper_R_identity_denote_type[OF language typed adequate])
next
  fix g n X
  assume typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and assigned: "g n = Some X"
  show "paper_R_identity_denote \<Omega> G M g (NVar n) = X"
    by (rule paper_R_identity_denote_var[where G=G and n=n, OF rich typed assigned])
next
  fix F \<sigma> \<tau> A H \<upsilon> \<rho> B g k
  assume fl: "paper_R_in_language \<Omega> G F (Arr \<sigma> \<tau>)" and al: "paper_R_in_language \<Omega> G A \<sigma>"
    and hl: "paper_R_in_language \<Omega> G H (Arr \<upsilon> \<rho>)" and bl: "paper_R_in_language \<Omega> G B \<upsilon>"
    and gt: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and kt: "named_env_typed (paper_R_identity_domain \<Omega> G M) G k"
    and ga: "named_adequate g (NApp F A)" and ka: "named_adequate k (NApp H B)"
    and heads: "paper_R_identity_denote \<Omega> G M g F = paper_R_identity_denote \<Omega> G M k H"
    and arguments: "paper_R_identity_denote \<Omega> G M g A = paper_R_identity_denote \<Omega> G M k B"
  show "paper_R_identity_denote \<Omega> G M g (NApp F A) = paper_R_identity_denote \<Omega> G M k (NApp H B)"
    by (rule paper_R_identity_denote_application_cong[OF rich fl al hl bl gt kt ga ka heads arguments])
next
  fix A \<sigma> g k
  assume language: "paper_R_in_language \<Omega> G A \<sigma>"
    and gt: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and kt: "named_env_typed (paper_R_identity_domain \<Omega> G M) G k"
    and ga: "named_adequate g A" and ka: "named_adequate k A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = k n"
  show "paper_R_identity_denote \<Omega> G M g A = paper_R_identity_denote \<Omega> G M k A"
    by (rule paper_R_identity_denote_locality[OF agree])
next
  fix \<sigma> A B g
  assume conversion: "paper_R_raw_beta_eta G \<sigma> A B"
    and left: "paper_R_in_language \<Omega> G A \<sigma>" and right: "paper_R_in_language \<Omega> G B \<sigma>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  show "paper_R_identity_denote \<Omega> G M g A = paper_R_identity_denote \<Omega> G M g B"
    by (rule paper_R_identity_denote_beta_eta[OF rich conversion left right typed aa ba])
next
  fix A g
  assume language: "paper_R_in_language \<Omega> G A Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and adequate: "named_adequate g A"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NLogical SNot) A)) =
      (\<not> paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A))"
    using paper_R_identity_denote_neg_truth[OF rich Henkin language typed adequate] by (simp only: named_paper_not_def)
next
  fix A B g
  assume left: "paper_R_in_language \<Omega> G A Prop" and right: "paper_R_in_language \<Omega> G B Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NApp (NLogical SAnd) A) B)) =
      (paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A) \<and>
       paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g B))"
    using paper_R_identity_denote_conj_truth[OF rich Henkin left right typed aa ba] by (simp only: named_paper_and_def)
next
  fix A B g
  assume left: "paper_R_in_language \<Omega> G A Prop" and right: "paper_R_in_language \<Omega> G B Prop"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NApp (NLogical SOr) A) B)) =
      (paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g A) \<or>
       paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g B))"
    using paper_R_identity_denote_disj_truth[OF rich Henkin left right typed aa ba] by (simp only: named_paper_or_def)
next
  fix F \<sigma> g n
  assume predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and adequate: "named_adequate g F"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>.
        paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M (g(n := Some X)) (NApp F (NVar n))))"
    by (rule paper_R_identity_denote_forall_truth[OF rich Henkin predicate typed adequate nt fresh])
next
  fix F \<sigma> g n
  assume predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and adequate: "named_adequate g F"
    and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>X\<in>paper_R_identity_domain \<Omega> G M \<sigma>.
        paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M (g(n := Some X)) (NApp F (NVar n))))"
    by (rule paper_R_identity_denote_exists_truth[OF rich Henkin predicate typed adequate nt fresh])
next
  fix A \<sigma> B g
  assume left: "paper_R_in_language \<Omega> G A \<sigma>" and right: "paper_R_in_language \<Omega> G B \<sigma>"
    and typed: "named_env_typed (paper_R_identity_domain \<Omega> G M) G g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  show "paper_R_identity_valuation M (paper_R_identity_denote \<Omega> G M g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
      (paper_R_identity_denote \<Omega> G M g A = paper_R_identity_denote \<Omega> G M g B)"
    using paper_R_identity_denote_identity_truth[OF rich Henkin left right typed aa ba] by (simp only: named_paper_eq_def)
qed

end
