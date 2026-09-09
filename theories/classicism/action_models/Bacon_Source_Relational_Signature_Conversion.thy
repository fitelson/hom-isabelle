theory Bacon_Source_Relational_Signature_Conversion
  imports Bacon_Source_Relational_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Retraction_Steps
begin

section \<open>Conversion whose every intermediate term belongs to ℒᴿ(Σ)\<close>

text \<open>
  This auxiliary relation records literal contextual βη conversion with
  the independent R grammar and Σ membership at every intermediate.
  It is not raw conversion plus endpoint guards: the Trans constructor
  requires two already guarded conversions through its middle term.
  Source role: Definition 3.1(ii.d), p.44, and Appendix C.6, p.71.
  No α constructor, proof-theoretic rule or model premise is added.
\<close>

inductive paper_R_beta_eta_in_signature ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow>
    'c paper_named_term \<Rightarrow> 'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Refl: "paper_R_in_language \<Sigma> G A \<tau> \<Longrightarrow> paper_R_beta_eta_in_signature \<Sigma> G \<tau> A A"
| Beta: "paper_R_in_language \<Sigma> G A \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> G B \<tau> \<Longrightarrow>
    named_compatible_step named_beta_contract A B \<Longrightarrow> paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
| Eta: "paper_R_in_language \<Sigma> G A \<tau> \<Longrightarrow> paper_R_in_language \<Sigma> G B \<tau> \<Longrightarrow>
    named_compatible_step named_eta_contract A B \<Longrightarrow> paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
| Sym: "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B \<Longrightarrow> paper_R_beta_eta_in_signature \<Sigma> G \<tau> B A"
| Trans: "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B \<Longrightarrow>
    paper_R_beta_eta_in_signature \<Sigma> G \<tau> B C \<Longrightarrow> paper_R_beta_eta_in_signature \<Sigma> G \<tau> A C"

lemma paper_R_signature_conversion_languages:
  assumes conversion: "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
  shows "paper_R_in_language \<Sigma> G A \<tau> \<and> paper_R_in_language \<Sigma> G B \<tau>"
  using conversion by (induction rule: paper_R_beta_eta_in_signature.induct) blast+

lemma paper_R_signature_conversion_raw:
  assumes conversion: "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
  shows "paper_R_raw_beta_eta G \<tau> A B"
  using conversion
  by (induction rule: paper_R_beta_eta_in_signature.induct)
    (auto simp only: paper_R_in_language_def intro: paper_R_raw_beta_eta.intros)

section \<open>Only R types need correctly typed replacement variables\<close>

lemma paper_R_retract_type:
  assumes typed: "paper_R_has_type G A \<tau>"
    and stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
  shows "paper_R_has_type G (named_retract \<Sigma> v A) \<tau>"
  using typed
proof (induction rule: paper_R_has_type.induct)
  case (Var n)
  show ?case by (simp only: named_retract.simps; rule paper_R_has_type.Var[where G=G and n=n, OF Var.hyps])
next
  case (Const \<sigma> c)
  show ?case
  proof (cases "c \<in> \<Sigma> \<sigma>")
    case True
    show ?thesis by (simp only: named_retract.simps True if_True; rule paper_R_has_type.Const[OF Const.hyps])
  next
    case False
    have vt: "G (v \<sigma>) = \<sigma>" by (rule stock[OF Const.hyps])
    have vr: "paper_R_type (G (v \<sigma>))" by (simp only: vt; rule Const.hyps)
    have variable: "paper_R_has_type G (NVar (v \<sigma>)) (G (v \<sigma>))"
      by (rule paper_R_has_type.Var[where G=G and n="v \<sigma>", OF vr])
    show ?thesis using variable by (simp only: named_retract.simps False if_False vt)
  qed
next
  case (Logical l)
  show ?case by (simp only: named_retract.simps; rule paper_R_has_type.Logical[OF Logical.hyps])
next
  case (App F \<sigma> \<tau> B)
  show ?case by (simp only: named_retract.simps; rule paper_R_has_type.App[OF App.IH])
next
  case (Lam B \<tau> n)
  show ?case by (simp only: named_retract.simps; rule paper_R_has_type.Lam[OF Lam.IH Lam.hyps(2,3)])
qed

lemma paper_R_retract_language:
  assumes typed: "paper_R_has_type G A \<tau>"
    and stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
  shows "paper_R_in_language \<Sigma> G (named_retract \<Sigma> v A) \<tau>"
  unfolding paper_R_in_language_def
  by (rule conjI[OF paper_R_retract_type[OF typed stock] named_retract_signature])

lemma paper_R_rich_avoiding_variable:
  assumes rich: "paper_R_rich G" and rt: "paper_R_type \<sigma>" and finite: "finite S"
  shows "\<exists>n. G n = \<sigma> \<and> n \<notin> S"
proof (rule ccontr)
  assume absent: "\<not> (\<exists>n. G n = \<sigma> \<and> n \<notin> S)"
  have subset: "{n. G n = \<sigma>} \<subseteq> S" using absent by auto
  have fin: "finite {n. G n = \<sigma>}" by (rule finite_subset[OF subset finite])
  have inf: "infinite {n. G n = \<sigma>}" by (rule paper_R_rich_type[OF rich rt])
  show False using fin inf by contradiction
qed

end
