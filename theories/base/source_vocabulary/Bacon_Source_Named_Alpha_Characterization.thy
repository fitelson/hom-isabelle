theory Bacon_Source_Named_Alpha_Characterization
  imports Bacon_Source_Named_Alpha_Representation Bacon_Source_Rich_Stock
    Bacon_Source_Global_Substitution
begin

section \<open>Characterizing the generated α relation by binding representation\<close>

text \<open>
  In a rich variable stock, A ≡α B exactly when their de Bruijn encodings
  agree.  The converse uses one new variable z of the common binder type
  to compare λx.A and λy.B as λz.(x z)·A and λz.(y z)·B.
  Source role: typed named λ syntax in Bacon–Dorr §1.1, p.5, with the
  capture restriction in Figure 2, p.8.

  Isabelle representation.  named_alpha remains the independently
  generated, fresh-all-names relation.  The induction measures nodes,
  not the numerical identifiers of variables.  Its abstraction step
  chooses z outside both finite sets of names and cancels closing by
  substituting the free variable z back for slot 0.

  Status.  This is a characterization of that explicit generated relation
  on raw terms in the represented full F grammar.  It does not add an α
  rule to H or prove that named α changes are source βη conversions.
  No substitution-rule, printed-string, proof-system, or model
  correspondence is inferred from the characterization.
\<close>

fun named_nodes :: "('c, 'l) named_term \<Rightarrow> nat" where
  "named_nodes (NVar n) = 1"
| "named_nodes (NConst c \<sigma>) = 1"
| "named_nodes (NLogical l) = 1"
| "named_nodes (NApp F A) = Suc (named_nodes F + named_nodes A)"
| "named_nodes (NLam n A) = Suc (named_nodes A)"

lemma named_nodes_swap:
  "named_nodes (named_swap x y A) = named_nodes A"
  by (induction A) (simp_all only: named_swap.simps named_nodes.simps)

subsection \<open>Aligning two equal abstraction encodings at one fresh name\<close>

lemma named_equal_encoding_fresh_bodies:
  assumes rich: "sg_rich G"
    and encoded: "named_to_source G [] (NLam x A) = named_to_source G [] (NLam y B)"
  obtains z where "G x = G z" and "G y = G z"
    and "z \<notin> named_vars A" and "z \<notin> named_vars B"
    and "named_to_source G [] (named_swap x z A) = named_to_source G [] (named_swap y z B)"
proof -
  have types: "G x = G y" using encoded by simp
  have finite_names: "finite (named_vars A \<union> named_vars B \<union> {x, y})"
    by (simp add: named_vars_finite)
  obtain z where ztype: "G z = G x"
    and fresh: "z \<notin> named_vars A \<union> named_vars B \<union> {x, y}"
    using sg_rich_fresh[where \<sigma>="G x", OF rich finite_names] by (elim exE conjE)
  have xtype: "G x = G z" by (rule sym[OF ztype])
  have ytype: "G y = G z" using types xtype by simp
  have freshA: "z \<notin> named_vars A" and freshB: "z \<notin> named_vars B"
    using fresh by auto
  have left_alpha: "named_alpha G (NLam x A) (NLam z (named_swap x z A))"
    by (rule named_alpha.Fresh_Binder[OF xtype freshA])
  have right_alpha: "named_alpha G (NLam y B) (NLam z (named_swap y z B))"
    by (rule named_alpha.Fresh_Binder[OF ytype freshB])
  have left_enc: "named_to_source G [] (NLam x A) =
    named_to_source G [] (NLam z (named_swap x z A))"
    by (rule named_alpha_encoding_empty[OF left_alpha])
  have right_enc: "named_to_source G [] (NLam y B) =
    named_to_source G [] (NLam z (named_swap y z B))"
    by (rule named_alpha_encoding_empty[OF right_alpha])
  have aligned: "named_to_source G [] (NLam z (named_swap x z A)) =
    named_to_source G [] (NLam z (named_swap y z B))"
    by (rule trans[OF sym[OF left_enc] trans[OF encoded right_enc]])
  have closed_eq: "sclose z (named_to_source G [] (named_swap x z A)) =
    sclose z (named_to_source G [] (named_swap y z B))"
    using aligned by (simp add: named_to_source_close)
  have opened_eq: "ssubst0 (SVar z) (sclose z (named_to_source G [] (named_swap x z A))) =
    ssubst0 (SVar z) (sclose z (named_to_source G [] (named_swap y z B)))"
    by (rule arg_cong[where f="ssubst0 (SVar z)", OF closed_eq])
  have body_eq: "named_to_source G [] (named_swap x z A) =
    named_to_source G [] (named_swap y z B)"
    using opened_eq by (simp only: ssubst0_sclose)
  show thesis by (rule that[OF xtype ytype freshA freshB body_eq])
qed

subsection \<open>Node induction for the converse\<close>

theorem named_encoding_implies_alpha:
  fixes A B :: "('c, 'l) named_term"
  assumes rich: "sg_rich G"
    and encoded: "named_to_source G [] A = named_to_source G [] B"
  shows "named_alpha G A B"
  using encoded
proof (induction A arbitrary: B rule: measure_induct_rule[where f=named_nodes])
  case (less A)
  show ?case
  proof (cases A)
    case (NVar n)
    have same: "B = NVar n"
      using less.prems NVar by (cases B) (auto simp: named_to_source.simps)
    show ?thesis unfolding NVar same by (rule named_alpha.Refl)
  next
    case (NConst c \<sigma>)
    have same: "B = NConst c \<sigma>"
      using less.prems NConst by (cases B) (auto simp: named_to_source.simps)
    show ?thesis unfolding NConst same by (rule named_alpha.Refl)
  next
    case (NLogical l)
    have same: "B = NLogical l"
      using less.prems NLogical by (cases B) (auto simp: named_to_source.simps)
    show ?thesis unfolding NLogical same by (rule named_alpha.Refl)
  next
    case (NApp F P)
    obtain H Q where shape: "B = NApp H Q"
      using less.prems NApp by (cases B) (auto simp: named_to_source.simps)
    have f_eq: "named_to_source G [] F = named_to_source G [] H"
      and p_eq: "named_to_source G [] P = named_to_source G [] Q"
      using less.prems by (simp_all add: NApp shape)
    have f_smaller: "named_nodes F < named_nodes A"
      unfolding NApp by simp
    have p_smaller: "named_nodes P < named_nodes A"
      unfolding NApp by simp
    have f_alpha: "named_alpha G F H"
      by (rule less.IH[where y=F and B=H, OF f_smaller f_eq])
    have p_alpha: "named_alpha G P Q"
      by (rule less.IH[where y=P and B=Q, OF p_smaller p_eq])
    show ?thesis unfolding NApp shape by (rule named_alpha.App[OF f_alpha p_alpha])
  next
    case (NLam x P)
    obtain y Q where shape: "B = NLam y Q"
      using less.prems NLam by (cases B) (auto simp: named_to_source.simps)
    have enc_lam: "named_to_source G [] (NLam x P) = named_to_source G [] (NLam y Q)"
      using less.prems by (simp only: NLam shape)
    obtain z where xtype: "G x = G z" and ytype: "G y = G z"
      and freshP: "z \<notin> named_vars P" and freshQ: "z \<notin> named_vars Q"
      and body_eq: "named_to_source G [] (named_swap x z P) =
        named_to_source G [] (named_swap y z Q)"
      by (rule named_equal_encoding_fresh_bodies[OF rich enc_lam])
    have smaller: "named_nodes (named_swap x z P) < named_nodes A"
      by (simp only: named_nodes_swap NLam named_nodes.simps lessI)
    have bodies: "named_alpha G (named_swap x z P) (named_swap y z Q)"
      by (rule less.IH[where y="named_swap x z P" and B="named_swap y z Q", OF smaller body_eq])
    have left_alpha: "named_alpha G (NLam x P) (NLam z (named_swap x z P))"
      by (rule named_alpha.Fresh_Binder[OF xtype freshP])
    have middle_alpha: "named_alpha G (NLam z (named_swap x z P)) (NLam z (named_swap y z Q))"
      by (rule named_alpha.Lam[OF bodies])
    have right_alpha: "named_alpha G (NLam y Q) (NLam z (named_swap y z Q))"
      by (rule named_alpha.Fresh_Binder[OF ytype freshQ])
    have result: "named_alpha G (NLam x P) (NLam y Q)"
      by (rule named_alpha.Trans[OF left_alpha
        named_alpha.Trans[OF middle_alpha named_alpha.Sym[OF right_alpha]]])
    show ?thesis using result by (simp only: NLam shape)
  qed
qed

corollary named_alpha_iff_encoding:
  assumes rich: "sg_rich G"
  shows "named_alpha G A B \<longleftrightarrow> named_to_source G [] A = named_to_source G [] B"
proof
  assume "named_alpha G A B"
  then show "named_to_source G [] A = named_to_source G [] B"
    by (rule named_alpha_encoding_empty)
next
  assume "named_to_source G [] A = named_to_source G [] B"
  then show "named_alpha G A B" by (rule named_encoding_implies_alpha[OF rich])
qed

end
