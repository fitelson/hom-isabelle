theory Bacon_Source_Named_Local_Correspondence
  imports Bacon_Source_Named_Local_Conversion Bacon_Source_Named_Local_Forward
    Bacon_Source_Named_H_Correspondence
begin

section \<open>Source-local proofs over encoded assumptions have native preimages\<close>

text \<open>
  If enc(S) ⊢H M in the source-global local calculus, there is a named
  N with S ⊢H N and enc(N) = M. A used assumption is recovered from
  the exact image enc(S); a theorem leaf uses named H correspondence.
  For MP, align the implication representative with the named antecedent
  and a typed representative of the conclusion by equal-encoding transport.
  Source: finite local proofs using the Figure 2 calculus, pp.7–8.

  Representation: induction has exactly Assumption, Theorem and MP cases.
  S is arbitrary: only assumptions actually used receive language guards.
  Status: no model/completeness argument, added local inference rule, or
  typing assumption on every member of S is used.
\<close>

theorem paper_named_derivable_preimage:
  assumes derivation: "paper_global_derivable \<Sigma> G T M"
    and image_eq: "T = image (named_to_source G []) S" and rich: "sg_rich G"
  shows "\<exists>N. paper_named_derivable \<Sigma> G S N \<and> named_to_source G [] N = M"
  using derivation image_eq
proof (induction arbitrary: S rule: paper_global_derivable.induct)
  case (Assumption M T)
  obtain A where member: "A \<in> S" and encoded: "named_to_source G [] A = M"
    using Assumption.hyps(1) Assumption.prems by auto
  have encoded_language: "sgterm_in_language paper_logical_type \<Sigma> G (named_to_source G [] A) Prop"
    by (simp only: encoded; rule Assumption.hyps(2))
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule named_representation_language_reflection[OF encoded_language rich])
  have native: "paper_named_derivable \<Sigma> G S A"
    by (rule paper_named_derivable.Assumption[OF member language])
  show ?case by (rule exI[where x=A], rule conjI[OF native encoded])
next
  case (Theorem M T)
  obtain N where theorem_N: "paper_named_H \<Sigma> G N" and encoded: "named_to_source G [] N = M"
    using paper_named_H_preimage[OF Theorem.hyps rich] by (elim exE conjE)
  have native: "paper_named_derivable \<Sigma> G S N"
    by (rule paper_named_derivable.Theorem[OF theorem_N])
  show ?case by (rule exI[where x=N], rule conjI[OF native encoded])
next
  case (MP T A B)
  obtain P where left: "paper_named_derivable \<Sigma> G S P" and pe: "named_to_source G [] P = A"
    using MP.IH(1)[OF MP.prems] by (elim exE conjE)
  obtain I where right: "paper_named_derivable \<Sigma> G S I" and ie: "named_to_source G [] I = paper_imp A B"
    using MP.IH(2)[OF MP.prems] by (elim exE conjE)
  have implication_language: "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp A B) Prop"
    by (rule paper_global_derivable_language[OF MP.hyps(2)])
  have conclusion_language: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule conjunct2[OF iffD1[OF paper_global_imp_language_iff implication_language]])
  obtain Q where ql: "named_in_language paper_logical_type \<Sigma> G Q Prop"
    and qe: "named_to_source G [] Q = B"
    using source_named_representation_exists[OF conclusion_language rich] by (elim exE conjE)
  have same: "named_to_source G [] I = named_to_source G [] (named_paper_imp G P Q)"
    by (simp only: ie named_paper_imp_encoding[OF rich] pe qe)
  have native_implication: "paper_named_derivable \<Sigma> G S (named_paper_imp G P Q)"
    by (rule paper_named_derivable_same_encoding[OF right same rich])
  have native: "paper_named_derivable \<Sigma> G S Q"
    by (rule paper_named_derivable.MP[OF left native_implication ql])
  show ?case by (rule exI[where x=Q], rule conjI[OF native qe])
qed

theorem paper_named_derivable_decoding:
  assumes derivation: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
    (named_to_source G [] A)"
    and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S A"
proof -
  obtain N where native: "paper_named_derivable \<Sigma> G S N"
    and same: "named_to_source G [] N = named_to_source G [] A"
    using paper_named_derivable_preimage[OF derivation refl rich] by (elim exE conjE)
  show ?thesis by (rule paper_named_derivable_same_encoding[OF native same rich])
qed

theorem paper_named_derivable_iff:
  assumes rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S A \<longleftrightarrow>
    paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (named_to_source G [] A)"
proof
  assume derivation: "paper_named_derivable \<Sigma> G S A"
  show "paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (named_to_source G [] A)"
    by (rule paper_named_derivable_encoding[OF derivation rich])
next
  assume derivation: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (named_to_source G [] A)"
  show "paper_named_derivable \<Sigma> G S A"
    by (rule paper_named_derivable_decoding[OF derivation rich])
qed

end
