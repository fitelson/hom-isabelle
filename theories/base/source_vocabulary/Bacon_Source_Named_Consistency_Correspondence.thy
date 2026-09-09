theory Bacon_Source_Named_Consistency_Correspondence
  imports Bacon_Source_Named_Local_Correspondence Bacon_Source_Consistency_Basics
    Bacon_Source_Named_Representation_Reflection
begin

section \<open>Named consistency excludes all native contradictory pairs\<close>

text \<open>
  ConH(S) means that no formula A has both S ⊢H A and S ⊢H ¬A.
  A may be open. Source role: the consistency convention used in
  Bacon–Dorr Theorem 3.2, pp.44–45, with local consequence from the
  independently defined Figure 2 calculus.

  Isabelle representation. paper_named_consistent is defined directly
  using native paper_named_derivable and native named_paper_not.
  Derivability itself guards the formulas actually used, so S need not
  consist entirely of well-formed formulas. No falsity abbreviation,
  finite-premise restriction, or sentence-only witness is stipulated.
\<close>

definition paper_named_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_named_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> (\<exists>A. paper_named_derivable \<Sigma> G S A \<and>
      paper_named_derivable \<Sigma> G S (named_paper_not A))"

lemma paper_named_consistent_no_pair:
  assumes consistent: "paper_named_consistent \<Sigma> G S"
    and positive: "paper_named_derivable \<Sigma> G S A"
    and negative: "paper_named_derivable \<Sigma> G S (named_paper_not A)"
  shows False
  using consistent positive negative unfolding paper_named_consistent_def by blast

section \<open>Consistency is preserved and reflected by named encoding\<close>

text \<open>
  ConH(S) holds exactly when ConH(enc(S)) holds, for a rich stock G.
  Source role: the named/global representation of the same local
  consistency convention, not an appeal to model existence.

  A source contradictory witness has a language guard by derivability.
  Typed representation supplies a named preimage N of that witness.
  Literal encoding of ¬N then supplies its negative preimage. The reverse
  local proof theorem transports both derivations into the native judgment.
  The other direction uses forward local encoding on a native pair.

  Status. Arbitrary premise sets and nonlogical-name carriers, with open
  witnesses allowed throughout. No all-premises language condition,
  uniform free-variable bound, model, or completeness theorem is assumed.
\<close>

theorem paper_named_consistency_iff:
  assumes rich: "sg_rich G"
  shows "paper_named_consistent \<Sigma> G S \<longleftrightarrow>
    paper_global_consistent \<Sigma> G (image (named_to_source G []) S)"
proof
  assume native_consistent: "paper_named_consistent \<Sigma> G S"
  show "paper_global_consistent \<Sigma> G (image (named_to_source G []) S)"
    unfolding paper_global_consistent_def
  proof
    assume pair: "\<exists>M. paper_global_derivable \<Sigma> G (image (named_to_source G []) S) M \<and>
      paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (paper_not M)"
    obtain M where positive: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S) M"
      and negative: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S) (paper_not M)"
      using pair by (elim exE conjE)
    have language: "sgterm_in_language paper_logical_type \<Sigma> G M Prop"
      by (rule paper_global_derivable_language[OF positive])
    obtain N where named_language: "named_in_language paper_logical_type \<Sigma> G N Prop"
      and encoded: "named_to_source G [] N = M"
      using source_named_representation_exists[OF language rich] by (elim exE conjE)
    have encoded_positive: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
      (named_to_source G [] N)"
      using positive by (simp only: encoded)
    have encoded_negative: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
      (named_to_source G [] (named_paper_not N))"
      using negative by (simp only: named_paper_not_encoding encoded)
    have native_positive: "paper_named_derivable \<Sigma> G S N"
      by (rule paper_named_derivable_decoding[OF encoded_positive rich])
    have native_negative: "paper_named_derivable \<Sigma> G S (named_paper_not N)"
      by (rule paper_named_derivable_decoding[OF encoded_negative rich])
    show False by (rule paper_named_consistent_no_pair[OF native_consistent native_positive native_negative])
  qed
next
  assume source_consistent: "paper_global_consistent \<Sigma> G (image (named_to_source G []) S)"
  show "paper_named_consistent \<Sigma> G S" unfolding paper_named_consistent_def
  proof
    assume pair: "\<exists>A. paper_named_derivable \<Sigma> G S A \<and>
      paper_named_derivable \<Sigma> G S (named_paper_not A)"
    obtain A where positive: "paper_named_derivable \<Sigma> G S A"
      and negative: "paper_named_derivable \<Sigma> G S (named_paper_not A)"
      using pair by (elim exE conjE)
    have source_positive: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
      (named_to_source G [] A)"
      by (rule paper_named_derivable_encoding[OF positive rich])
    have source_negative: "paper_global_derivable \<Sigma> G (image (named_to_source G []) S)
      (paper_not (named_to_source G [] A))"
      using paper_named_derivable_encoding[OF negative rich]
      by (simp only: named_paper_not_encoding)
    show False by (rule paper_global_consistent_no_pair[OF source_consistent source_positive source_negative])
  qed
qed

end
