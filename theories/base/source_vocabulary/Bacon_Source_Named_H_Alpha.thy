theory Bacon_Source_Named_H_Alpha
  imports Bacon_Source_Named_H_Conversion Bacon_Source_Named_Alpha_Conversion
    Bacon_Source_Named_Alpha_Characterization
begin

section \<open>Named H is invariant under proved changes of bound names\<close>

text \<open>
  An α-variant of an H theorem is an H theorem. The α relation first
  gives a typed literal βη conversion; native H proves its biconditional
  and uses PC and MP to transport theoremhood. Source: the β/η and
  propositional rules in Bacon–Dorr Figure 2, p.8.

  This is a derived theorem, not an added α constructor. Equality of
  empty-stack encodings can supply α in a rich stock. It is not semantic
  extensionality or equality of equally true formulas.
\<close>

theorem paper_named_H_alpha:
  assumes derivation: "paper_named_H \<Sigma> G A" and alpha: "named_alpha G A B"
    and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G B"
proof -
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule paper_named_H_language[OF derivation])
  have conversion: "named_beta_eta_in_language paper_logical_type \<Sigma> G Prop A B"
    by (rule named_alpha_implies_beta_eta[OF alpha language])
  show ?thesis by (rule paper_named_H_conversion[OF derivation conversion rich])
qed

theorem paper_named_H_same_encoding:
  assumes derivation: "paper_named_H \<Sigma> G A"
    and encodings: "named_to_source G [] A = named_to_source G [] B"
    and rich: "sg_rich G"
  shows "paper_named_H \<Sigma> G B"
  by (rule paper_named_H_alpha[OF derivation named_encoding_implies_alpha[OF rich encodings] rich])

end
