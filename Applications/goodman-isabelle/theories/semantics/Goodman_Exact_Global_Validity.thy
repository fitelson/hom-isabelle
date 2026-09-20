theory Goodman_Exact_Global_Validity
  imports Goodman_Exact_Minimal_Model
    "Bacon_Book_Environment_Development.Bacon_Book_Minimal_Leibniz_Truth"
begin

section \<open>All worlds and all typed assignments, not root satisfaction\<close>

definition gi_exact_global_valid where
  "gi_exact_global_valid C G A \<longleftrightarrow>
    (\<forall>w. book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) A)"

lemma gi_exact_global_validI:
  "(\<And>w g. book_env_typed gi_exact_domain G g \<Longrightarrow>
      gi_exact_valuation w (gi_exact_named_denote C G g A)) \<Longrightarrow>
    gi_exact_global_valid C G A"
  unfolding gi_exact_global_valid_def book_formula_valid_def by blast

lemma gi_exact_global_validD:
  "gi_exact_global_valid C G A \<Longrightarrow> book_env_typed gi_exact_domain G g \<Longrightarrow>
    gi_exact_valuation w (gi_exact_named_denote C G g A)"
  unfolding gi_exact_global_valid_def book_formula_valid_def by blast

lemma gi_exact_propositions_extensional:
  assumes p: "p \<in> gi_exact_domain Prop" and q: "q \<in> gi_exact_domain Prop"
    and agreement: "\<And>w. gi_exact_valuation w p = gi_exact_valuation w q"
  shows "p = q"
proof -
  have pm: "Elem p (Power Nat)" and qm: "Elem q (Power Nat)" using p q by simp_all
  have same: "pp_n_holds p = pp_n_holds q"
    by (rule ext; use agreement in \<open>simp only: gi_exact_valuation_def\<close>)
  have "p = pp_n_prop (pp_n_holds p)" by (rule pp_n_prop_eta[OF pm, symmetric])
  also have "... = pp_n_prop (pp_n_holds q)" by (simp only: same)
  also have "... = q" by (rule pp_n_prop_eta[OF qm])
  finally show ?thesis .
qed

context pp_e_constants
begin

theorem gi_exact_H_global_sound:
  assumes rich: "sg_rich G" and derivation: "book_H \<Sigma> G A"
  shows "gi_exact_global_valid C G A"
  unfolding gi_exact_global_valid_def by (intro allI; rule gi_exact_book_H_sound[OF rich derivation])

lemma gi_exact_global_MP:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and a: "gi_exact_global_valid C G A" and implication: "gi_exact_global_valid C G (book_imp A B)"
  shows "gi_exact_global_valid C G B"
proof (unfold gi_exact_global_valid_def, intro allI)
  fix w
  have av: "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) A"
    using a unfolding gi_exact_global_valid_def by blast
  have iv: "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) (book_imp A B)"
    using implication unfolding gi_exact_global_valid_def by blast
  show "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) B"
    by (rule book_full_minimal_model.book_MP_valid[OF gi_exact_book_minimal_model[OF rich] al bl av iv])
qed

lemma gi_exact_global_Gen:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B" and fresh: "n \<notin> named_fv A"
    and premise: "gi_exact_global_valid C G (book_imp A B)"
  shows "gi_exact_global_valid C G (book_imp A (book_all G n B))"
proof (unfold gi_exact_global_valid_def, intro allI)
  fix w
  have pv: "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w) (book_imp A B)"
    using premise unfolding gi_exact_global_valid_def by blast
  show "book_formula_valid gi_exact_domain G (gi_exact_named_denote C G) (gi_exact_valuation w)
    (book_imp A (book_all G n B))"
    by (rule book_full_minimal_model.book_Gen_valid[OF gi_exact_book_minimal_model[OF rich] al bl fresh pv])
qed

theorem gi_exact_global_PE:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and premise: "gi_exact_global_valid C G (book_iff G A B)"
  shows "gi_exact_global_valid C G (book_leibniz G Prop A B)"
proof (rule gi_exact_global_validI)
  fix w g assume typed: "book_env_typed gi_exact_domain G g"
  have am: "gi_exact_named_denote C G g A \<in> gi_exact_domain Prop"
    by (rule gi_exact_named_denote_type[OF al typed])
  have bm: "gi_exact_named_denote C G g B \<in> gi_exact_domain Prop"
    by (rule gi_exact_named_denote_type[OF bl typed])
  have same_truth: "gi_exact_valuation v (gi_exact_named_denote C G g A) =
    gi_exact_valuation v (gi_exact_named_denote C G g B)" for v
    using gi_exact_global_validD[OF premise typed, where w=v]
    by (simp only: book_full_minimal_model.book_iff_truth[OF gi_exact_book_minimal_model[OF rich] rich typed al bl])
  have equal: "gi_exact_named_denote C G g A = gi_exact_named_denote C G g B"
    by (rule gi_exact_propositions_extensional[OF am bm same_truth])
  show "gi_exact_valuation w (gi_exact_named_denote C G g (book_leibniz G Prop A B))"
    by (simp only: book_full_minimal_model.book_leibniz_truth[OF gi_exact_book_minimal_model[OF rich] rich typed al bl]
      equal; rule book_leibniz_refl; rule bm)
qed

end

text \<open>
  Global PE uses equality of proposition values only after proving
  agreement at every world. The all-world premise is essential; a
  biconditional true at one world is not used as an identity rule.
  This file supplies H and the extension's rule cases, but not MF or
  the complete full-C/axiom-extension soundness induction.
\<close>

end
