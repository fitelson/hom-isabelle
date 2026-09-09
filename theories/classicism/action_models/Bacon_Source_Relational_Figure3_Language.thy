theory Bacon_Source_Relational_Figure3_Language
  imports Bacon_Source_Relational_Figure3_Syntax
    Bacon_Source_Relational_Identity_Proof_Basics
begin

section \<open>Distinct typed names and R language for the displayed identities\<close>

lemma paper_R_figure3_variable_languages:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "paper_R_in_language \<Sigma> G (NVar p) Prop"
    "paper_R_in_language \<Sigma> G (NVar q) Prop"
    "paper_R_in_language \<Sigma> G (NVar r) Prop"
proof -
  have pt: "G p = Prop" and qt: "G q = Prop" and rt: "G r = Prop"
    using variables unfolding paper_R_figure3_variables_def by blast+
  have prop_R: "paper_R_type Prop" by simp
  show "paper_R_in_language \<Sigma> G (NVar p) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=p, OF pt prop_R])
  show "paper_R_in_language \<Sigma> G (NVar q) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=q, OF qt prop_R])
  show "paper_R_in_language \<Sigma> G (NVar r) Prop"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=r, OF rt prop_R])
qed

lemma paper_R_figure3_prefix_distinct:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "distinct (paper_R_figure3_prefix law p q r)"
  using variables by (cases law; simp add: paper_R_figure3_variables_def)

lemma paper_R_figure3_prefix_prop_types:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "map G (paper_R_figure3_prefix law p q r) =
    replicate (length (paper_R_figure3_prefix law p q r)) Prop"
  using variables by (cases law; auto simp: paper_R_figure3_variables_def)

lemma paper_R_figure3_prefix_R:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "list_all paper_R_type (map G (paper_R_figure3_prefix law p q r))"
  using variables by (cases law; auto simp: paper_R_figure3_variables_def)

lemma paper_R_figure3_body_languages:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "paper_R_in_language \<Sigma> G (paper_R_figure3_left law p q r) Prop"
    "paper_R_in_language \<Sigma> G (paper_R_figure3_right law p q r) Prop"
proof -
  have pl: "paper_R_in_language \<Sigma> G (NVar p) Prop"
    by (rule paper_R_figure3_variable_languages(1)[OF variables])
  have ql: "paper_R_in_language \<Sigma> G (NVar q) Prop"
    by (rule paper_R_figure3_variable_languages(2)[OF variables])
  have rl: "paper_R_in_language \<Sigma> G (NVar r) Prop"
    by (rule paper_R_figure3_variable_languages(3)[OF variables])
  have nq: "paper_R_in_language \<Sigma> G (named_paper_not (NVar q)) Prop"
    by (rule paper_R_named_not_language[OF ql])
  show "paper_R_in_language \<Sigma> G (paper_R_figure3_left law p q r) Prop"
  proof (cases law)
    case RCommAnd
    show ?thesis by (simp only: RCommAnd paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_and_language[OF pl ql])
  next
    case RCommOr
    show ?thesis by (simp only: RCommOr paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_or_language[OF pl ql])
  next
    case RDistAndOr
    show ?thesis by (simp only: RDistAndOr paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_and_language[OF pl paper_R_named_or_language[OF ql rl]])
  next
    case RDistOrAnd
    show ?thesis by (simp only: RDistOrAnd paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_or_language[OF pl paper_R_named_and_language[OF ql rl]])
  next
    case RDissolveAndOr
    show ?thesis by (simp only: RDissolveAndOr paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_and_language[OF pl paper_R_named_or_language[OF ql nq]])
  next
    case RDissolveOrAnd
    show ?thesis by (simp only: RDissolveOrAnd paper_R_figure3_bodies.simps fst_conv;
      rule paper_R_named_or_language[OF pl paper_R_named_and_language[OF ql nq]])
  qed
  show "paper_R_in_language \<Sigma> G (paper_R_figure3_right law p q r) Prop"
  proof (cases law)
    case RCommAnd
    show ?thesis by (simp only: RCommAnd paper_R_figure3_bodies.simps snd_conv;
      rule paper_R_named_and_language[OF ql pl])
  next
    case RCommOr
    show ?thesis by (simp only: RCommOr paper_R_figure3_bodies.simps snd_conv;
      rule paper_R_named_or_language[OF ql pl])
  next
    case RDistAndOr
    show ?thesis by (simp only: RDistAndOr paper_R_figure3_bodies.simps snd_conv;
      rule paper_R_named_or_language[
        OF paper_R_named_and_language[OF pl ql] paper_R_named_and_language[OF pl rl]])
  next
    case RDistOrAnd
    show ?thesis by (simp only: RDistOrAnd paper_R_figure3_bodies.simps snd_conv;
      rule paper_R_named_and_language[
        OF paper_R_named_or_language[OF pl ql] paper_R_named_or_language[OF pl rl]])
  next
    case RDissolveAndOr
    show ?thesis by (simp only: RDissolveAndOr paper_R_figure3_bodies.simps snd_conv; rule pl)
  next
    case RDissolveOrAnd
    show ?thesis by (simp only: RDissolveOrAnd paper_R_figure3_bodies.simps snd_conv; rule pl)
  qed
qed

theorem paper_R_figure3_axiom_language:
  assumes variables: "paper_R_figure3_variables G p q r"
  shows "paper_R_in_language \<Sigma> G (paper_R_figure3_axiom G law p q r) Prop"
  unfolding paper_R_figure3_axiom_def
  by (rule paper_R_named_identity_language[OF
    paper_R_named_lam_vec_prop_language[OF paper_R_figure3_body_languages(1)[OF variables] paper_R_figure3_prefix_R[OF variables]]
    paper_R_named_lam_vec_prop_language[OF paper_R_figure3_body_languages(2)[OF variables] paper_R_figure3_prefix_R[OF variables]]])

theorem paper_R_figure3_variables_exists:
  assumes rich: "paper_R_rich G"
  obtains p q r where "paper_R_figure3_variables G p q r"
proof -
  have prop_R: "paper_R_type Prop" by simp
  obtain p where pt: "G p = Prop"
    using paper_R_rich_fresh[where G=G and \<sigma>=Prop and S="{}", OF rich prop_R finite.emptyI] by blast
  have finite_p: "finite {p}" by simp
  obtain q where qt: "G q = Prop" and qf: "q \<notin> {p}"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=Prop, OF rich prop_R finite_p])
  have finite_pq: "finite {p,q}" by simp
  obtain r where rt: "G r = Prop" and rf: "r \<notin> {p,q}"
    by (rule paper_R_rich_fresh[where G=G and \<sigma>=Prop, OF rich prop_R finite_pq])
  have variables: "paper_R_figure3_variables G p q r"
    using pt qt rt qf rf by (auto simp: paper_R_figure3_variables_def)
  show thesis by (rule that[OF variables])
qed

text \<open>
  The operator types are t→t→t or t→t→t→t as printed.
  R-richness constructs an actual distinct proposition-variable triple;
  after that choice, the language proofs need no further richness
  assumption. The signature Σ is arbitrary because these operators
  contain no nonlogical constants.
\<close>

end
