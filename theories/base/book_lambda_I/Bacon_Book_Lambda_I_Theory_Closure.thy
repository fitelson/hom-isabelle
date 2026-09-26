theory Bacon_Book_Lambda_I_Theory_Closure
  imports Bacon_Book_Lambda_I_Finite_Support
begin

section \<open>Higher-order theories and the smallest theory containing S\<close>

text \<open>
  A theory is a set of λI formulas closed under the displayed
  derivations. It contains every instance of the six axiom schemas and
  is closed under MP and the guarded Gen (and so contains all its
  consequences, possibly with further assumptions). The minimality theorem below is proved using the set of all
  derivable consequences and cut; it is not taken as the definition of
  derivability. Requiring S to consist of formulas prevents a vacuous
  universal claim about typed theories containing malformed assumptions.
\<close>

definition book_lambda_I_higher_order_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_lambda_I_higher_order_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A \<in> T. book_lambda_I_formula \<Sigma> G A) \<and>
    (\<forall>A. book_lambda_I_derivable \<Sigma> G T A \<longrightarrow> A \<in> T)"

lemma book_lambda_I_contains_derivation:
  assumes theory_ok: "book_lambda_I_higher_order_theory \<Sigma> G T"
    and derivation: "book_lambda_I_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "A \<in> T"
proof -
  have lifted: "book_lambda_I_derivable \<Sigma> G T A" by (rule book_lambda_I_derivable_mono[OF derivation inclusion])
  show ?thesis using theory_ok lifted unfolding book_lambda_I_higher_order_theory_def by blast
qed

theorem book_lambda_I_derivable_consequences_form_theory:
  assumes rich: "sg_rich G"
  shows "book_lambda_I_higher_order_theory \<Sigma> G {A. book_lambda_I_derivable \<Sigma> G S A}"
proof (unfold book_lambda_I_higher_order_theory_def, rule conjI)
  show "\<forall>A \<in> {A. book_lambda_I_derivable \<Sigma> G S A}. book_lambda_I_formula \<Sigma> G A"
    by (intro ballI, rule book_lambda_I_derivable_language[OF _ rich]) simp
next
  show "\<forall>A. book_lambda_I_derivable \<Sigma> G {B. book_lambda_I_derivable \<Sigma> G S B} A \<longrightarrow>
    A \<in> {A. book_lambda_I_derivable \<Sigma> G S A}"
  proof (intro allI impI)
    fix A
    assume derivation: "book_lambda_I_derivable \<Sigma> G {B. book_lambda_I_derivable \<Sigma> G S B} A"
    have reduced: "book_lambda_I_derivable \<Sigma> G S A"
      by (rule book_lambda_I_derivable_cut[OF derivation]) simp
    show "A \<in> {A. book_lambda_I_derivable \<Sigma> G S A}" using reduced by simp
  qed
qed

theorem book_lambda_I_derivable_iff_all_theories:
  assumes rich: "sg_rich G" and assumptions_typed: "\<And>B. B \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G B"
  shows "book_lambda_I_derivable \<Sigma> G S A \<longleftrightarrow>
    (\<forall>T. book_lambda_I_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T)"
proof
  assume derivation: "book_lambda_I_derivable \<Sigma> G S A"
  show "\<forall>T. book_lambda_I_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
    by (intro allI impI, rule book_lambda_I_contains_derivation[OF _ derivation]; assumption)
next
  assume all_theories: "\<forall>T. book_lambda_I_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
  have theory_ok: "book_lambda_I_higher_order_theory \<Sigma> G {B. book_lambda_I_derivable \<Sigma> G S B}"
    by (rule book_lambda_I_derivable_consequences_form_theory[OF rich])
  have inclusion: "S \<subseteq> {B. book_lambda_I_derivable \<Sigma> G S B}"
  proof
    fix B
    assume member: "B \<in> S"
    have derivation: "book_lambda_I_derivable \<Sigma> G S B"
      by (rule book_lambda_I_derivable.Assumption[OF member assumptions_typed[OF member]])
    show "B \<in> {B. book_lambda_I_derivable \<Sigma> G S B}" using derivation by simp
  qed
  show "book_lambda_I_derivable \<Sigma> G S A" using all_theories theory_ok inclusion by blast
qed


end
