theory Bacon_Parametric_Henkin_Full_Consistency
  imports Bacon_Parametric_Henkin_Finite_Elimination
begin

section \<open>Finite support permits all witness axioms at once\<close>

text \<open>
  Conₕ(S ∪ W₀) for every finite W₀ ⊆ W implies Conₕ(S ∪ W).
  Source role: Bacon's witness-extension construction, Proposition 15.4.
  Here W contains axioms for every admissible body of the final nested-name
  language, not merely bodies from a countable or earlier stage.
\<close>

theorem phenkin_all_witness_consistency:
  assumes typed: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] S"
    and con: "pH_consistent (phenkin_full_signature \<Sigma>) [] S"
    and old: "\<And>B \<sigma> A. B \<in> S \<Longrightarrow> PFWitness \<sigma> A \<notin> phenkin_names B"
  shows "pH_consistent (phenkin_full_signature \<Sigma>) [] (S \<union> phenkin_all_witness_axioms \<Sigma>)"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable (phenkin_full_signature \<Sigma>) []
    (S \<union> phenkin_all_witness_axioms \<Sigma>) PObjFalse"
  obtain K where finite_K: "finite K" and subset_K: "K \<subseteq> S \<union> phenkin_all_witness_axioms \<Sigma>"
    and d: "pH_set_derivable (phenkin_full_signature \<Sigma>) [] K PObjFalse"
  proof (rule pH_set_finite_support[OF bad])
    fix K
    assume fk: "finite K" and sk: "K \<subseteq> S \<union> phenkin_all_witness_axioms \<Sigma>"
      and dk: "pH_set_derivable (phenkin_full_signature \<Sigma>) [] K PObjFalse"
    show thesis by (rule that[OF fk sk dk])
  qed
  have finite_extra: "finite (K - S)" by (rule finite_Diff[OF finite_K])
  have remainder: "K - S \<subseteq> phenkin_all_witness_axioms \<Sigma>"
    by (rule iffD2[OF Diff_subset_conv subset_K])
  have extra: "K - S \<subseteq> image phenkin_index_axiom (phenkin_witness_indices \<Sigma>)"
    using remainder by (simp only: phenkin_all_witness_axioms_def)
  have cover_exists: "\<exists>F. F \<subseteq> phenkin_witness_indices \<Sigma> \<and> finite F \<and>
      K - S = image phenkin_index_axiom F"
    by (rule finite_subset_image[OF finite_extra extra])
  obtain F where parts: "F \<subseteq> phenkin_witness_indices \<Sigma> \<and> finite F \<and>
      K - S = image phenkin_index_axiom F"
  proof (rule exE[OF cover_exists])
    fix F
    assume all_parts: "F \<subseteq> phenkin_witness_indices \<Sigma> \<and> finite F \<and>
      K - S = image phenkin_index_axiom F"
    show thesis by (rule that[OF all_parts])
  qed
  have admitted: "F \<subseteq> phenkin_witness_indices \<Sigma>" by (rule conjunct1[OF parts])
  have finite_F: "finite F" by (rule conjunct1[OF conjunct2[OF parts]])
  have covers: "K - S = image phenkin_index_axiom F" by (rule conjunct2[OF conjunct2[OF parts]])
  have consistent: "pH_consistent (phenkin_full_signature \<Sigma>) [] (S \<union> image phenkin_index_axiom F)"
    by (rule phenkin_finite_witness_consistency[OF typed con old finite_F admitted])
  have rest_subset: "K - S \<subseteq> image phenkin_index_axiom F" by (simp only: covers subset_refl)
  have support: "K \<subseteq> S \<union> image phenkin_index_axiom F"
    by (rule iffD1[OF Diff_subset_conv rest_subset])
  have bad_finite: "pH_set_derivable (phenkin_full_signature \<Sigma>) []
      (S \<union> image phenkin_index_axiom F) PObjFalse"
    by (rule pH_set_mono[OF d support])
  show False by (rule notE[OF consistent[unfolded pH_consistent_def] bad_finite])
qed

theorem phenkin_embedded_all_witness_consistency:
  assumes old_typed: "pH_typed_theory \<Sigma> [] S"
    and expanded_consistency: "pH_consistent (phenkin_full_signature \<Sigma>) [] (image phenkin_full_embed S)"
  shows "pH_consistent (phenkin_full_signature \<Sigma>) []
    (image phenkin_full_embed S \<union> phenkin_all_witness_axioms \<Sigma>)"
proof -
  have typed: "pH_typed_theory (phenkin_full_signature \<Sigma>) [] (image phenkin_full_embed S)"
  proof (unfold pH_typed_theory_def, intro ballI)
    fix B
    assume member: "B \<in> image phenkin_full_embed S"
    obtain A where A: "A \<in> S" and B: "B = phenkin_full_embed A"
      by (rule phenkin_pick_image[where f=phenkin_full_embed and A=S and b=B, OF member])
    have parts: "has_ptype [] A Prop \<and> pterm_in_signature \<Sigma> A"
      by (rule bspec[OF old_typed[unfolded pH_typed_theory_def] A])
    have at: "has_ptype [] (phenkin_full_embed A) Prop"
      by (rule phenkin_full_embed_type[OF conjunct1[OF parts]])
    have sa: "pterm_in_signature (phenkin_full_signature \<Sigma>) (phenkin_full_embed A)"
      using conjunct2[OF parts] by (simp only: phenkin_full_embed_signature)
    show "has_ptype [] B Prop \<and> pterm_in_signature (phenkin_full_signature \<Sigma>) B"
      unfolding B by (rule conjI[OF at sa])
  qed
  have fresh: "PFWitness \<sigma> A \<notin> phenkin_names B"
    if member: "B \<in> image phenkin_full_embed S" for B \<sigma> A
  proof -
    obtain C where C: "C \<in> S" and B: "B = phenkin_full_embed C"
      by (rule phenkin_pick_image[where f=phenkin_full_embed and A=S and b=B, OF member])
    show ?thesis unfolding B by (rule phenkin_full_witness_fresh_original)
  qed
  show ?thesis by (rule phenkin_all_witness_consistency[OF typed expanded_consistency fresh])
qed

text \<open>
  The sole outstanding premise in the final corollary is consistency after
  embedding into the final signature.  It is not replaced by the weaker
  old-signature consistency assertion.  Witness dependencies cause no
  counterpattern: an occurrence in another body would force a strict rank
  inequality contrary to maximality.  Maximal consistent completion and
  conversion of available axioms into Henkin witnesses are subsequent steps.
\<close>

end
