theory Bacon_Source_Named_H_Conversion
  imports Bacon_Source_Named_H_PC_Basics Bacon_Source_Named_Conversion
begin

section \<open>Named H proves the biconditional of convertible formulas\<close>

text \<open>
  If A ≡βη B and A,B are formulas, H proves A↔B. Reflexivity,
  symmetry, and transitivity are supplied by native PC and MP; generating
  steps use the literal named H β and η rules of Figure 2, p.8.
  No source-H proof translation or model argument is used.

  Representation. The auxiliary induction explicitly retains τ = t.
  It does not assert an H biconditional theorem for arbitrary non-formula
  terms. The logical language guards use the rich variable stock and the
  literal closed → and ↔ operators of Figure 1, p.6.
\<close>

lemma paper_named_H_iff_sym:
  assumes premise: "paper_named_H \<Sigma> G (named_paper_iff G A B)"
    and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G (named_paper_iff G B A)"
  by (rule paper_named_H.MP[OF premise paper_named_H_iff_sym_schema[OF rich A B]
    named_paper_iff_language[OF rich B A]])

lemma paper_named_H_iff_trans:
  assumes first: "paper_named_H \<Sigma> G (named_paper_iff G A B)"
    and second: "paper_named_H \<Sigma> G (named_paper_iff G B C)"
    and A: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and C: "named_in_language paper_logical_type \<Sigma> G C Prop" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G (named_paper_iff G A C)"
proof -
  have ac: "named_in_language paper_logical_type \<Sigma> G (named_paper_iff G A C) Prop"
    by (rule named_paper_iff_language[OF rich A C])
  have bc: "named_in_language paper_logical_type \<Sigma> G (named_paper_iff G B C) Prop"
    by (rule named_paper_iff_language[OF rich B C])
  have implication: "paper_named_H \<Sigma> G (named_paper_imp G (named_paper_iff G B C) (named_paper_iff G A C))"
    by (rule paper_named_H.MP[OF first paper_named_H_iff_trans_schema[OF rich A B C]
      named_paper_imp_language[OF rich bc ac]])
  show ?thesis by (rule paper_named_H.MP[OF second implication ac])
qed

lemma paper_named_H_iff_conversion_at_type:
  assumes conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G \<tau> A B"
    and is_prop: "\<tau> = Prop" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G (named_paper_iff G A B)"
  using conversion is_prop
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop" using Refl.hyps Refl.prems by simp
  show ?case by (rule paper_named_H_iff_refl[OF rich al])
next
  case (Beta A \<tau> B)
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    using Beta.hyps(1,2) Beta.prems by simp_all
  have iff_language: "named_in_language paper_logical_type \<Sigma> G (named_paper_iff G A B) Prop"
    by (rule named_paper_iff_language[OF rich al bl])
  show ?case by (rule paper_named_H.Beta[OF al bl Beta.hyps(3) iff_language])
next
  case (Eta A \<tau> B)
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    using Eta.hyps(1,2) Eta.prems by simp_all
  have iff_language: "named_in_language paper_logical_type \<Sigma> G (named_paper_iff G A B) Prop"
    by (rule named_paper_iff_language[OF rich al bl])
  show ?case by (rule paper_named_H.Eta[OF al bl Eta.hyps(3) iff_language])
next
  case (Sym \<tau> A B)
  have premise: "paper_named_H \<Sigma> G (named_paper_iff G A B)" by (rule Sym.IH[OF Sym.prems])
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    using named_beta_eta_languages[OF Sym.hyps] Sym.prems by auto
  show ?case by (rule paper_named_H_iff_sym[OF premise al bl rich])
next
  case (Trans \<tau> A B C)
  have first: "paper_named_H \<Sigma> G (named_paper_iff G A B)" by (rule Trans.IH(1)[OF Trans.prems])
  have second: "paper_named_H \<Sigma> G (named_paper_iff G B C)" by (rule Trans.IH(2)[OF Trans.prems])
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    and cl: "named_in_language paper_logical_type \<Sigma> G C Prop"
    using named_beta_eta_languages[OF Trans.hyps(1)] named_beta_eta_languages[OF Trans.hyps(2)] Trans.prems by auto
  show ?case by (rule paper_named_H_iff_trans[OF first second al bl cl rich])
qed

theorem paper_named_H_iff_conversion:
  assumes conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop A B" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G (named_paper_iff G A B)"
  by (rule paper_named_H_iff_conversion_at_type[OF conversion refl rich])

theorem paper_named_H_conversion:
  assumes derivation: "paper_named_H \<Sigma> G A"
    and conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop A B" and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G B"
proof -
  have languages: "named_in_language paper_logical_type \<Sigma> G A Prop \<and>
    named_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule named_beta_eta_languages[OF conversion])
  have biconditional: "paper_named_H \<Sigma> G (named_paper_iff G A B)"
    by (rule paper_named_H_iff_conversion[OF conversion rich])
  have implication: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    by (rule paper_named_H.MP[OF biconditional
      paper_named_H_iff_elim_schema[OF rich conjunct1[OF languages] conjunct2[OF languages]]
      named_paper_imp_language[OF rich conjunct1[OF languages] conjunct2[OF languages]]])
  show ?thesis by (rule paper_named_H.MP[OF derivation implication conjunct2[OF languages]])
qed

end
