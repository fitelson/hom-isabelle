theory Bacon_Source_Named_Local_Conversion
  imports Bacon_Source_Named_H_Alpha
begin

section \<open>Native local consequence respects formula conversion and α\<close>

text \<open>
  From S ⊢H A and A ≡βη B, infer S ⊢H B. Native H proves A↔B
  and the PC implication eliminating that biconditional; its implication
  theorem is a local Theorem leaf, followed by local MP.
  Source: Bacon–Dorr Figure 2, p.8, with literal contextual β/η.

  Representation: only the existing local Assumption/Theorem/MP relation
  is used. Generated α and equality of empty-stack encodings supply the
  requisite conversion through proved syntax lemmas. Status: no semantic
  premise, reverse source proof, or new local rule is assumed.
\<close>

theorem paper_named_derivable_conversion:
  assumes derivation: "paper_named_derivable \<Sigma> G S A"
    and conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop A B"
    and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S B"
proof -
  have languages: "named_in_language paper_logical_type \<Sigma> G A Prop \<and>
    named_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule named_beta_eta_languages[OF conversion])
  have al: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule conjunct1[OF languages])
  have bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule conjunct2[OF languages])
  have biconditional: "paper_named_H \<Sigma> G (named_paper_iff G A B)"
    by (rule paper_named_H_iff_conversion[OF conversion rich])
  have implication: "paper_named_H \<Sigma> G (named_paper_imp G A B)"
    by (rule paper_named_H.MP[OF biconditional paper_named_H_iff_elim_schema[OF rich al bl]
      named_paper_imp_language[OF rich al bl]])
  have local_implication: "paper_named_derivable \<Sigma> G S (named_paper_imp G A B)"
    by (rule paper_named_derivable.Theorem[OF implication])
  show ?thesis by (rule paper_named_derivable.MP[OF derivation local_implication bl])
qed

theorem paper_named_derivable_alpha:
  assumes derivation: "paper_named_derivable \<Sigma> G S A"
    and alpha: "named_alpha G A B" and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S B"
proof -
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule paper_named_derivable_language[OF derivation])
  have conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  show ?thesis by (rule paper_named_derivable_conversion[OF derivation conversion rich])
qed

theorem paper_named_derivable_same_encoding:
  assumes derivation: "paper_named_derivable \<Sigma> G S A"
    and encodings: "named_to_source G [] A = named_to_source G [] B"
    and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S B"
  by (rule paper_named_derivable_alpha[OF derivation
    named_encoding_implies_alpha[OF rich encodings] rich])

end
