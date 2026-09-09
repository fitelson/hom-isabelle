theory Bacon_Parametric_Propositional
  imports Bacon_Parametric_Conversion
begin

section \<open>Propositional evaluation\<close>

text \<open>
  A is a propositional tautology when every Boolean valuation makes A true.
  In this test, ∀v.B, B =σ C, and applications are treated as atoms.

  Isabelle representation: pprop_eval recursively evaluates PNeg, PConj, PDisj,
  and primitive PImp.  pprop_tautology also requires has_ptype Γ A Prop.

  Status: truth-functional tautology checking; it does not identify necessarily
  equivalent propositions or assume the Fregean axiom.
\<close>

fun pprop_eval :: "('c pterm \<Rightarrow> bool) \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pprop_eval v (PVar n) = v (PVar n)"
| "pprop_eval v (PConst c \<sigma>) = v (PConst c \<sigma>)"
| "pprop_eval v (PApp M N) = v (PApp M N)"
| "pprop_eval v (PLam \<sigma> M) = v (PLam \<sigma> M)"
| "pprop_eval v (PEq \<sigma> M N) = v (PEq \<sigma> M N)"
| "pprop_eval v (PNeg A) = (\<not> pprop_eval v A)"
| "pprop_eval v (PConj A B) = (pprop_eval v A \<and> pprop_eval v B)"
| "pprop_eval v (PDisj A B) = (pprop_eval v A \<or> pprop_eval v B)"
| "pprop_eval v (PImp A B) = (pprop_eval v A \<longrightarrow> pprop_eval v B)"
| "pprop_eval v (PForall \<sigma> A) = v (PForall \<sigma> A)"
| "pprop_eval v (PExists \<sigma> A) = v (PExists \<sigma> A)"

definition pprop_tautology :: "ctx \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pprop_tautology \<Gamma> A \<longleftrightarrow> has_ptype \<Gamma> A Prop \<and> (\<forall>v. pprop_eval v A)"

text \<open>
  For string names, translating A preserves its value under corresponding
  Boolean valuations, and hence preserves and reflects tautologicity.

  Isabelle representation: pprop_eval_to_oterm and pprop_eval_of_oterm supply the
  valuation equations used by pprop_tautology_string_iff.

  Status: exact correspondence of the PC tests on the two syntaxes.
\<close>

lemma pprop_eval_to_oterm:
  "pprop_eval (\<lambda>A. v (pterm_to_oterm A)) M = prop_eval v (pterm_to_oterm M)"
  by (induction M) (simp_all only: pprop_eval.simps prop_eval.simps pterm_to_oterm.simps)

lemma pprop_eval_of_oterm:
  "pprop_eval v (pterm_of_oterm M) = prop_eval (\<lambda>A. v (pterm_of_oterm A)) M"
  by (induction M) (simp_all only: pprop_eval.simps prop_eval.simps pterm_of_oterm.simps)

theorem pprop_tautology_string_iff:
  "pprop_tautology \<Gamma> M \<longleftrightarrow> prop_tautology \<Gamma> (pterm_to_oterm M)"
proof
  assume taut: "pprop_tautology \<Gamma> M"
  have data: "has_ptype \<Gamma> M Prop \<and> (\<forall>v. pprop_eval v M)"
    using taut unfolding pprop_tautology_def .
  have typed: "has_ptype \<Gamma> M Prop" by (rule conjunct1[OF data])
  have eval_all: "\<forall>v. pprop_eval v M" by (rule conjunct2[OF data])
  have current_type: "\<Gamma> \<turnstile> pterm_to_oterm M : Prop"
    by (rule pterm_to_preserves_typing[OF typed])
  have each: "prop_eval v (pterm_to_oterm M)" for v
  proof -
    have "pprop_eval (\<lambda>A. v (pterm_to_oterm A)) M"
      by (rule spec[where x="\<lambda>A. v (pterm_to_oterm A)", OF eval_all])
    then show ?thesis by (simp only: pprop_eval_to_oterm)
  qed
  show "prop_tautology \<Gamma> (pterm_to_oterm M)"
    unfolding prop_tautology_def
  proof (rule conjI)
    show "\<Gamma> \<turnstile> pterm_to_oterm M : Prop" by (rule current_type)
    show "\<forall>v. prop_eval v (pterm_to_oterm M)" by (rule allI; rule each)
  qed
next
  assume taut: "prop_tautology \<Gamma> (pterm_to_oterm M)"
  have data: "\<Gamma> \<turnstile> pterm_to_oterm M : Prop \<and>
      (\<forall>v. prop_eval v (pterm_to_oterm M))"
    using taut unfolding prop_tautology_def .
  have typed: "\<Gamma> \<turnstile> pterm_to_oterm M : Prop" by (rule conjunct1[OF data])
  have eval_all: "\<forall>v. prop_eval v (pterm_to_oterm M)" by (rule conjunct2[OF data])
  have ptype: "has_ptype \<Gamma> M Prop" using typed by (simp only: pterm_string_typing_iff)
  have each: "pprop_eval v M" for v
  proof -
    have "prop_eval (\<lambda>A. v (pterm_of_oterm A)) (pterm_to_oterm M)"
      by (rule spec[where x="\<lambda>A. v (pterm_of_oterm A)", OF eval_all])
    then have "pprop_eval v (pterm_of_oterm (pterm_to_oterm M))"
      by (simp only: pprop_eval_of_oterm)
    then show ?thesis by (simp only: pterm_of_to)
  qed
  show "pprop_tautology \<Gamma> M"
    unfolding pprop_tautology_def
  proof (rule conjI)
    show "has_ptype \<Gamma> M Prop" by (rule ptype)
    show "\<forall>v. pprop_eval v M" by (rule allI; rule each)
  qed
qed

end
