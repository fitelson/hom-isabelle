theory Goodman_Exact_Logical_Values
  imports Goodman_Exact_Interpretation_Structure
    "Bacon_Book_Environment_Development.Bacon_Book_Full_Minimal_Model"
begin

section \<open>The exact values of the two minimal logical constants\<close>

fun gi_exact_logical_value :: "book_minimal_logical \<Rightarrow> ZF" where
  "gi_exact_logical_value SImp = Lambda (pp_e_domain Prop)
    (\<lambda>p. Lambda (pp_e_domain Prop)
      (\<lambda>q. pp_e_prop (\<lambda>w. pp_e_holds p w \<longrightarrow> pp_e_holds q w)))"
| "gi_exact_logical_value (SBAll \<sigma>) = Lambda (pp_e_domain (Arr \<sigma> Prop))
    (\<lambda>f. pp_e_prop (\<lambda>w. \<forall>a. Elem a (pp_e_domain \<sigma>) \<longrightarrow> pp_e_holds (f \<acute> a) w))"

definition gi_exact_valuation where
  "gi_exact_valuation w p = pp_e_holds p w"

lemma gi_exact_named_logical_value:
  "gi_exact_named_denote C G g (NLogical l) = gi_exact_logical_value l"
  by (cases l; simp add: gi_exact_named_denote_def book_named_translation_Logical
    book_minimal_logical_translation.simps)

lemma gi_exact_logical_value_member:
  "gi_exact_logical_value l \<in> gi_exact_domain (book_minimal_logical_type l)"
proof -
  have constants: "pp_e_constants pp_e_default_constants"
    by standard (simp add: pp_e_default_constants_def pp_e_default_in_domain)
  have language: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. {}) (\<lambda>_. Prop)
    (NLogical l :: string book_named_term) (book_minimal_logical_type l)"
    by (rule book_language_Logical; simp)
  have typed: "gi_exact_named_denote pp_e_default_constants (\<lambda>_. Prop)
    (gi_exact_default_assignment (\<lambda>_. Prop)) (NLogical l)
      \<in> gi_exact_domain (book_minimal_logical_type l)"
    by (rule pp_e_constants.gi_exact_named_denote_type[OF constants language gi_exact_default_assignment_typed])
  show ?thesis using typed by (simp only: gi_exact_named_logical_value)
qed

lemma gi_exact_implication_truth:
  assumes p: "p \<in> gi_exact_domain Prop" and q: "q \<in> gi_exact_domain Prop"
  shows "gi_exact_valuation w
    (gi_exact_app Prop Prop (gi_exact_app Prop (Arr Prop Prop) (gi_exact_logical_value SImp) p) q)
    = (gi_exact_valuation w p \<longrightarrow> gi_exact_valuation w q)"
  using p q by (simp add: gi_exact_valuation_def gi_exact_app_def Lambda_app)

lemma gi_exact_forall_truth:
  assumes f: "f \<in> gi_exact_domain (Arr \<sigma> Prop)"
  shows "gi_exact_valuation w (gi_exact_app (Arr \<sigma> Prop) Prop (gi_exact_logical_value (SBAll \<sigma>)) f)
    = (\<forall>a\<in>gi_exact_domain \<sigma>. gi_exact_valuation w (gi_exact_app \<sigma> Prop f a))"
  using f by (simp add: gi_exact_valuation_def gi_exact_app_def Lambda_app gi_exact_domain_def)

lemma gi_exact_false_proposition:
  "\<exists>p\<in>gi_exact_domain Prop. \<not> gi_exact_valuation w p"
proof (rule bexI[where x="pp_e_prop (\<lambda>_. False)"])
  show "\<not> gi_exact_valuation w (pp_e_prop (\<lambda>_. False))"
    by (simp add: gi_exact_valuation_def)
  show "pp_e_prop (\<lambda>_. False) \<in> gi_exact_domain Prop"
    by (simp only: gi_exact_domain_member; rule pp_e_prop_in_domain)
qed

lemma gi_exact_logical_value_witness:
  "\<exists>g. book_env_typed gi_exact_domain G g \<and>
    gi_exact_named_denote C G g (NLogical l) = gi_exact_logical_value l"
  by (rule exI[where x="gi_exact_default_assignment G"];
    simp only: gi_exact_default_assignment_typed gi_exact_named_logical_value; simp)

text \<open>
  These truth clauses are evaluated at an arbitrary world w, with the
  original restricted carriers and set-theoretic application. Universal
  quantification ranges over exactly Dσ, not all HOL values or functions.
  Each logical value has an explicit typed assignment witness. Joining
  these facts to the full environment proof is a separate final step.
\<close>

end
