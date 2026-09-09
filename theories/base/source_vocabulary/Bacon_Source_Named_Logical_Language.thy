theory Bacon_Source_Named_Logical_Language
  imports Bacon_Source_Named_Logical_Syntax
begin

section \<open>Language guards for the native logical applications\<close>

text \<open>
  The native applications preserve the declared signature and have their
  displayed result types. Implication and biconditional use the literal
  closed λ operators of Bacon–Dorr Figure 1, p.6, in a rich stock G.
  These introduction lemmas package typing with signature membership;
  they assert no proof rule, conversion, or semantic equivalence.
\<close>

lemma named_paper_app_language:
  assumes F: "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)" and A: "named_in_language L \<Sigma> G A \<sigma>"
  shows "named_in_language L \<Sigma> G (NApp F A) \<tau>"
proof -
  note fd = F[unfolded named_in_language_def]
  note ad = A[unfolded named_in_language_def]
  have typed: "has_ntype L G (NApp F A) \<tau>" by (rule has_ntype.App[OF conjunct1[OF fd] conjunct1[OF ad]])
  have names: "named_in_signature \<Sigma> (NApp F A)"
    by (simp only: named_in_signature.simps; rule conjI[OF conjunct2[OF fd] conjunct2[OF ad]])
  show ?thesis unfolding named_in_language_def by (rule conjI[OF typed names])
qed

lemma named_paper_logical_language:
  "named_in_language paper_logical_type \<Sigma> G (NLogical l) (paper_logical_type l)"
  unfolding named_in_language_def by (rule conjI[OF has_ntype.Logical]) simp

lemma named_paper_unary_language:
  assumes head: "paper_logical_type l = Arr \<sigma> \<tau>"
    and arg: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
  shows "named_in_language paper_logical_type \<Sigma> G (NApp (NLogical l) A) \<tau>"
proof -
  have hl: "named_in_language paper_logical_type \<Sigma> G (NLogical l) (Arr \<sigma> \<tau>)"
    using named_paper_logical_language[where \<Sigma>=\<Sigma> and G=G and l=l] by (simp only: head)
  show ?thesis by (rule named_paper_app_language[OF hl arg])
qed

lemma named_paper_binary_language:
  assumes head: "paper_logical_type l = Arr \<sigma> (Arr \<rho> \<tau>)"
    and A: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and B: "named_in_language paper_logical_type \<Sigma> G B \<rho>"
  shows "named_in_language paper_logical_type \<Sigma> G (NApp (NApp (NLogical l) A) B) \<tau>"
  by (rule named_paper_app_language[OF named_paper_unary_language[OF head A] B])

lemma named_paper_not_language:
  "named_in_language paper_logical_type \<Sigma> G A Prop \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_not A) Prop"
  unfolding named_paper_not_def by (rule named_paper_unary_language[OF paper_logical_type.simps(1)]; assumption)
lemma named_paper_and_language:
  "named_in_language paper_logical_type \<Sigma> G A Prop \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G B Prop \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_and A B) Prop"
  unfolding named_paper_and_def by (rule named_paper_binary_language[OF paper_logical_type.simps(2)]; assumption)
lemma named_paper_or_language:
  "named_in_language paper_logical_type \<Sigma> G A Prop \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G B Prop \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_or A B) Prop"
  unfolding named_paper_or_def by (rule named_paper_binary_language[OF paper_logical_type.simps(3)]; assumption)
lemma named_paper_eq_language:
  "named_in_language paper_logical_type \<Sigma> G A \<sigma> \<Longrightarrow> named_in_language paper_logical_type \<Sigma> G B \<sigma> \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
  unfolding named_paper_eq_def by (rule named_paper_binary_language[OF paper_logical_type.simps(6)]; assumption)
lemma named_paper_all_language:
  "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_all \<sigma> F) Prop"
  unfolding named_paper_all_def by (rule named_paper_unary_language[OF paper_logical_type.simps(4)]; assumption)
lemma named_paper_ex_language:
  "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G (named_paper_ex \<sigma> F) Prop"
  unfolding named_paper_ex_def by (rule named_paper_unary_language[OF paper_logical_type.simps(5)]; assumption)

lemma named_paper_imp_const_language:
  assumes rich: "sg_rich G"
  shows "named_in_language paper_logical_type \<Sigma> G (named_paper_imp_const G) (Arr Prop (Arr Prop Prop))"
  unfolding named_in_language_def by (rule conjI[OF named_paper_imp_const_type[OF rich] named_paper_operator_signatures(1)])
lemma named_paper_iff_const_language:
  assumes rich: "sg_rich G"
  shows "named_in_language paper_logical_type \<Sigma> G (named_paper_iff_const G) (Arr Prop (Arr Prop Prop))"
  unfolding named_in_language_def by (rule conjI[OF named_paper_iff_const_type[OF rich] named_paper_operator_signatures(2)])

lemma named_paper_imp_language:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
  shows "named_in_language paper_logical_type \<Sigma> G (named_paper_imp G A B) Prop"
  unfolding named_paper_imp_def by (rule named_paper_app_language[OF
    named_paper_app_language[OF named_paper_imp_const_language[OF rich] A] B])
lemma named_paper_iff_language:
  assumes rich: "sg_rich G" and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
  shows "named_in_language paper_logical_type \<Sigma> G (named_paper_iff G A B) Prop"
  unfolding named_paper_iff_def by (rule named_paper_app_language[OF
    named_paper_app_language[OF named_paper_iff_const_language[OF rich] A] B])

end
