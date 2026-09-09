theory Bacon_Source_BBK_Normalization_Validity
  imports Bacon_Source_BBK_Normalization_Inputs
begin

section \<open>Canonical normalization preserves every BBK model clause\<close>

text \<open>
  Normalization changes neither domains nor any source-defined denotation
  or propositional valuation. Here that observation is checked against
  ALL thirteen fields of the independent named BBK interface.
  Source: Bacon–Dorr Definition 3.1, pp.43–44.

  Heterogeneous application keeps all four operand types and both adequate
  assignments. Quantifier clauses use explicit typed updates and adequate
  applications, so normalization also preserves the inner evaluations.
  No model condition is replaced by an unguarded equality of total
  denotation functions. No truth-preservation requirement on homomorphisms
  is introduced.
\<close>

theorem paper_bbk_normalize_valid:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
  shows "paper_bbk_data_valid \<Sigma> G (paper_bbk_normalize \<Sigma> G M)"
proof -
  let ?D = "paper_bbk_domain M"
  let ?J = "paper_bbk_denote (paper_bbk_normalize \<Sigma> G M)"
  let ?V = "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M)"
  let ?OldJ = "paper_bbk_denote M"
  let ?OldV = "paper_bbk_valuation M"
  interpret Source: paper_named_bbk_model \<Sigma> G ?D ?OldJ ?OldV
    by (rule paper_bbk_data_model[OF valid])
  have normalized_model: "paper_named_bbk_model \<Sigma> G ?D ?J ?V"
  proof (rule paper_named_bbk_model.intro)
    show "sg_rich G" by (rule Source.stock_rich)
  next
    fix \<sigma>
    show "?D \<sigma> \<noteq> {}" by (rule Source.domain_nonempty)
  next
    fix A \<sigma> g
    assume al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A"
    have original: "?OldJ g A \<in> ?D \<sigma>"
      by (rule paper_bbk_data_denote_type[OF valid al gt ag])
    show "?J g A \<in> ?D \<sigma>"
      using original by (simp only: paper_bbk_normalize_denote[OF al gt ag])
  next
    fix g n a
    assume gt: "named_env_typed ?D G g" and assigned: "g n = Some a"
    have vl: "named_in_language paper_logical_type \<Sigma> G (NVar n) (G n)"
      by (simp add: named_in_language_def named_var_type_iff)
    have adequate: "named_adequate g (NVar n)" using assigned by (auto simp: named_adequate_def dom_def)
    have original: "?OldJ g (NVar n) = a"
      by (rule Source.denote_var[where g=g and n=n and a=a, OF gt assigned])
    show "?J g (NVar n) = a"
      using original by (simp only: paper_bbk_normalize_denote[OF vl gt adequate])
  next
    fix F A H B \<sigma> \<tau> \<upsilon> \<rho> g h
    assume fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
      and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and hl: "named_in_language paper_logical_type \<Sigma> G H (Arr \<upsilon> \<rho>)"
      and bl: "named_in_language paper_logical_type \<Sigma> G B \<upsilon>"
      and gt: "named_env_typed ?D G g" and ht: "named_env_typed ?D G h"
      and fg: "named_adequate g (NApp F A)" and hh: "named_adequate h (NApp H B)"
      and heads: "?J g F = ?J h H" and arguments: "?J g A = ?J h B"
    have first_adequate: "named_adequate g F \<and> named_adequate g A"
      using fg by (simp only: paper_bbk_adequate_App_iff)
    have fa: "named_adequate g F" by (rule conjunct1[OF first_adequate])
    have aa: "named_adequate g A" by (rule conjunct2[OF first_adequate])
    have second_adequate: "named_adequate h H \<and> named_adequate h B"
      using hh by (simp only: paper_bbk_adequate_App_iff)
    have ha: "named_adequate h H" by (rule conjunct1[OF second_adequate])
    have ba: "named_adequate h B" by (rule conjunct2[OF second_adequate])
    have old_heads: "?OldJ g F = ?OldJ h H"
      using heads by (simp only: paper_bbk_normalize_denote[OF fl gt fa]
        paper_bbk_normalize_denote[OF hl ht ha])
    have old_arguments: "?OldJ g A = ?OldJ h B"
      using arguments by (simp only: paper_bbk_normalize_denote[OF al gt aa]
        paper_bbk_normalize_denote[OF bl ht ba])
    have original: "?OldJ g (NApp F A) = ?OldJ h (NApp H B)"
      by (rule Source.denote_application_cong[OF fl al hl bl gt ht fg hh old_heads old_arguments])
    show "?J g (NApp F A) = ?J h (NApp H B)"
      using original by (simp only: paper_bbk_normalize_denote[OF named_language_App[OF fl al] gt fg]
        paper_bbk_normalize_denote[OF named_language_App[OF hl bl] ht hh])
  next
    fix A \<sigma> g h
    assume al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and gt: "named_env_typed ?D G g" and ht: "named_env_typed ?D G h"
      and ag: "named_adequate g A" and ah: "named_adequate h A"
      and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
    have original: "?OldJ g A = ?OldJ h A"
      by (rule Source.denote_locality[OF al gt ht ag ah agree])
    show "?J g A = ?J h A"
      using original by (simp only: paper_bbk_normalize_denote[OF al gt ag] paper_bbk_normalize_denote[OF al ht ah])
  next
    fix A B \<sigma> g
    assume conversion: "named_raw_beta_eta paper_logical_type G \<sigma> A B"
      and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and bl: "named_in_language paper_logical_type \<Sigma> G B \<sigma>"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A" and bg: "named_adequate g B"
    have original: "?OldJ g A = ?OldJ g B"
      by (rule Source.denote_beta_eta[OF conversion al bl gt ag bg])
    show "?J g A = ?J g B"
      using original by (simp only: paper_bbk_normalize_denote[OF al gt ag] paper_bbk_normalize_denote[OF bl gt bg])
  next
    fix A g
    assume al: "named_in_language paper_logical_type \<Sigma> G A Prop"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A"
    have op_type: "paper_logical_type SNot = Arr Prop Prop" by simp
    have lhs: "?V (?J g (NApp (NLogical SNot) A)) = ?OldV (?OldJ g (NApp (NLogical SNot) A))"
      by (rule paper_bbk_normalize_unary_truth[where l=SNot, OF valid op_type al gt ag])
    have original: "?OldV (?OldJ g (NApp (NLogical SNot) A)) = (\<not> ?OldV (?OldJ g A))"
      by (rule Source.valuation_neg[OF al gt ag])
    show "?V (?J g (NApp (NLogical SNot) A)) = (\<not> ?V (?J g A))"
      using original by (simp only: lhs paper_bbk_normalize_truth[OF valid al gt ag])
  next
    fix A B g
    assume al: "named_in_language paper_logical_type \<Sigma> G A Prop"
      and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A" and bg: "named_adequate g B"
    have op_type: "paper_logical_type SAnd = Arr Prop (Arr Prop Prop)" by simp
    have lhs: "?V (?J g (NApp (NApp (NLogical SAnd) A) B)) = ?OldV (?OldJ g (NApp (NApp (NLogical SAnd) A) B))"
      by (rule paper_bbk_normalize_binary_truth[where l=SAnd, OF valid op_type al bl gt ag bg])
    have original: "?OldV (?OldJ g (NApp (NApp (NLogical SAnd) A) B)) = (?OldV (?OldJ g A) \<and> ?OldV (?OldJ g B))"
      by (rule Source.valuation_conj[OF al bl gt ag bg])
    show "?V (?J g (NApp (NApp (NLogical SAnd) A) B)) = (?V (?J g A) \<and> ?V (?J g B))"
      using original by (simp only: lhs paper_bbk_normalize_truth[OF valid al gt ag]
        paper_bbk_normalize_truth[OF valid bl gt bg])
  next
    fix A B g
    assume al: "named_in_language paper_logical_type \<Sigma> G A Prop"
      and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A" and bg: "named_adequate g B"
    have op_type: "paper_logical_type SOr = Arr Prop (Arr Prop Prop)" by simp
    have lhs: "?V (?J g (NApp (NApp (NLogical SOr) A) B)) = ?OldV (?OldJ g (NApp (NApp (NLogical SOr) A) B))"
      by (rule paper_bbk_normalize_binary_truth[where l=SOr, OF valid op_type al bl gt ag bg])
    have original: "?OldV (?OldJ g (NApp (NApp (NLogical SOr) A) B)) = (?OldV (?OldJ g A) \<or> ?OldV (?OldJ g B))"
      by (rule Source.valuation_disj[OF al bl gt ag bg])
    show "?V (?J g (NApp (NApp (NLogical SOr) A) B)) = (?V (?J g A) \<or> ?V (?J g B))"
      using original by (simp only: lhs paper_bbk_normalize_truth[OF valid al gt ag]
        paper_bbk_normalize_truth[OF valid bl gt bg])
  next
    fix F \<sigma> g n
    assume fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> Prop)"
      and gt: "named_env_typed ?D G g" and fg: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    have op_type: "paper_logical_type (SAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
    have lhs: "?V (?J g (NApp (NLogical (SAll \<sigma>)) F)) = ?OldV (?OldJ g (NApp (NLogical (SAll \<sigma>)) F))"
      by (rule paper_bbk_normalize_unary_truth[where l="SAll \<sigma>", OF valid op_type fl gt fg])
    have rhs: "(\<forall>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n)))) =
      (\<forall>a\<in>?D \<sigma>. ?OldV (?OldJ (g(n := Some a)) (NApp F (NVar n))))"
      by (rule ball_cong[OF refl], rule paper_bbk_normalize_quantifier_instance[OF valid fl gt fg nt], assumption)
    have original: "?OldV (?OldJ g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>?D \<sigma>. ?OldV (?OldJ (g(n := Some a)) (NApp F (NVar n))))"
      by (rule Source.valuation_forall[OF fl gt fg nt fresh])
    show "?V (?J g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n))))"
      using original by (simp only: lhs rhs)
  next
    fix F \<sigma> g n
    assume fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> Prop)"
      and gt: "named_env_typed ?D G g" and fg: "named_adequate g F"
      and nt: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
    have op_type: "paper_logical_type (SEx \<sigma>) = Arr (Arr \<sigma> Prop) Prop" by simp
    have lhs: "?V (?J g (NApp (NLogical (SEx \<sigma>)) F)) = ?OldV (?OldJ g (NApp (NLogical (SEx \<sigma>)) F))"
      by (rule paper_bbk_normalize_unary_truth[where l="SEx \<sigma>", OF valid op_type fl gt fg])
    have rhs: "(\<exists>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n)))) =
      (\<exists>a\<in>?D \<sigma>. ?OldV (?OldJ (g(n := Some a)) (NApp F (NVar n))))"
      by (rule bex_cong[OF refl], rule paper_bbk_normalize_quantifier_instance[OF valid fl gt fg nt], assumption)
    have original: "?OldV (?OldJ g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>?D \<sigma>. ?OldV (?OldJ (g(n := Some a)) (NApp F (NVar n))))"
      by (rule Source.valuation_exists[OF fl gt fg nt fresh])
    show "?V (?J g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>?D \<sigma>. ?V (?J (g(n := Some a)) (NApp F (NVar n))))"
      using original by (simp only: lhs rhs)
  next
    fix A B \<sigma> g
    assume al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and bl: "named_in_language paper_logical_type \<Sigma> G B \<sigma>"
      and gt: "named_env_typed ?D G g" and ag: "named_adequate g A" and bg: "named_adequate g B"
    have op_type: "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)" by simp
    have lhs: "?V (?J g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
      ?OldV (?OldJ g (NApp (NApp (NLogical (SEq \<sigma>)) A) B))"
      by (rule paper_bbk_normalize_binary_truth[where l="SEq \<sigma>", OF valid op_type al bl gt ag bg])
    have original: "?OldV (?OldJ g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (?OldJ g A = ?OldJ g B)"
      by (rule Source.valuation_identity[OF al bl gt ag bg])
    show "?V (?J g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (?J g A = ?J g B)"
      using original by (simp only: lhs paper_bbk_normalize_denote[OF al gt ag]
        paper_bbk_normalize_denote[OF bl gt bg])
  qed
  show ?thesis using normalized_model
    by (simp only: paper_bbk_data_valid_def paper_bbk_normalize_domain)
qed

end
