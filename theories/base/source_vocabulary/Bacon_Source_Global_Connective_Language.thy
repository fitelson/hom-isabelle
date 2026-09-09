theory Bacon_Source_Global_Connective_Language
  imports Bacon_Source_Prefix_Preservation Bacon_Source_Global_Existence
begin

section \<open>Global language guards for the literal source connectives\<close>

text \<open>
  P → Q and P ↔ Q are formulas exactly when P,Q are formulas in the
  declared language. Their heads remain Figure 1's closed λ-definitions
  (Bacon–Dorr pp.5–6).

  Isabelle representation: global typing is checked in a sufficiently
  large finite prefix, using the already proved finite connective inversions,
  then transported back to G. The prefix is a typing device, not a
  restriction on variables available in a source proof.

  Status: language introduction/elimination only, without target H proofs,
  semantic assumptions, or new source axioms.
\<close>

lemma source_prefix_language_to_global:
  assumes language: "sterm_in_language L \<Sigma> (source_prefix G m) A \<tau>"
  shows "sgterm_in_language L \<Sigma> G A \<tau>"
proof -
  note parts = language[unfolded sterm_in_language_def]
  have typed: "has_stype L (map G [0..<m]) A \<tau>"
    using conjunct1[OF parts] by (simp only: source_prefix_def)
  show ?thesis by (rule source_prefix_global_language[where G=G and N=m,
    OF typed conjunct2[OF parts]])
qed

lemma source_global_binary_language_iff:
  fixes f :: "'c paper_term \<Rightarrow> 'c paper_term \<Rightarrow> 'c paper_term"
  assumes finite_rule: "\<And>\<Gamma>. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (f A B) Prop \<longleftrightarrow>
    (sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<and>
      sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop)"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (f A B) Prop \<longleftrightarrow>
    (sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
      sgterm_in_language paper_logical_type \<Sigma> G B Prop)"
proof
  assume language: "sgterm_in_language paper_logical_type \<Sigma> G (f A B) Prop"
  have finite_language: "sterm_in_language paper_logical_type \<Sigma>
    (source_prefix G (source_free_bound (f A B))) (f A B) Prop"
    by (rule source_language_in_prefix[OF language order_refl])
  have pair: "sterm_in_language paper_logical_type \<Sigma>
      (source_prefix G (source_free_bound (f A B))) A Prop \<and>
    sterm_in_language paper_logical_type \<Sigma>
      (source_prefix G (source_free_bound (f A B))) B Prop"
    by (rule iffD1[OF finite_rule finite_language])
  show "sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
    sgterm_in_language paper_logical_type \<Sigma> G B Prop"
    by (rule conjI[OF source_prefix_language_to_global[OF conjunct1[OF pair]]
      source_prefix_language_to_global[OF conjunct2[OF pair]]])
next
  assume pair: "sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
    sgterm_in_language paper_logical_type \<Sigma> G B Prop"
  let ?m = "max (source_free_bound A) (source_free_bound B)"
  have a: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) A Prop"
    by (rule source_language_in_prefix[OF conjunct1[OF pair]]) simp
  have b: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) B Prop"
    by (rule source_language_in_prefix[OF conjunct2[OF pair]]) simp
  have whole: "sterm_in_language paper_logical_type \<Sigma> (source_prefix G ?m) (f A B) Prop"
    by (rule iffD2[OF finite_rule conjI[OF a b]])
  show "sgterm_in_language paper_logical_type \<Sigma> G (f A B) Prop"
    by (rule source_prefix_language_to_global[OF whole])
qed

theorem paper_global_imp_language_iff:
  "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp A B) Prop \<longleftrightarrow>
    (sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
      sgterm_in_language paper_logical_type \<Sigma> G B Prop)"
proof (rule source_global_binary_language_iff[where f=paper_imp])
  show "\<And>\<Gamma>. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_imp A B) Prop \<longleftrightarrow>
    (sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<and>
      sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop)"
    by (auto simp: sterm_in_language_def paper_imp_type_iff)
qed

theorem paper_global_iff_language_iff:
  "sgterm_in_language paper_logical_type \<Sigma> G (paper_iff A B) Prop \<longleftrightarrow>
    (sgterm_in_language paper_logical_type \<Sigma> G A Prop \<and>
      sgterm_in_language paper_logical_type \<Sigma> G B Prop)"
proof (rule source_global_binary_language_iff[where f=paper_iff])
  show "\<And>\<Gamma>. sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_iff A B) Prop \<longleftrightarrow>
    (sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop \<and>
      sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop)"
    by (auto simp: sterm_in_language_def paper_iff_type_iff)
qed

lemma paper_global_imp_language:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (paper_imp A B) Prop"
  by (rule iffD2[OF paper_global_imp_language_iff conjI[OF A B]])

lemma paper_global_iff_language:
  assumes A: "sgterm_in_language paper_logical_type \<Sigma> G A Prop"
    and B: "sgterm_in_language paper_logical_type \<Sigma> G B Prop"
  shows "sgterm_in_language paper_logical_type \<Sigma> G (paper_iff A B) Prop"
  by (rule iffD2[OF paper_global_iff_language_iff conjI[OF A B]])

end
