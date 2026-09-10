theory Bacon_Book_ZF_Countable_Nontrivial_Existence
  imports Bacon_Book_ZF_Ambient_Nontrivial_Existence
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Nontrivial_Interpretation
begin

section \<open>Model existence for the original countably declared signature\<close>

theorem book_full_C_countable_nontrivial_modal_model_exists:
  assumes rich: "sg_rich G"
    and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
proof -
  let ?\<rho> = "book_countable_signature_map \<Sigma>"
  let ?\<Omega> = "book_countable_signature_image \<Sigma>"
  let ?T = "book_typed_name_map ?\<rho> ` S"
  have maps: "?\<rho> \<sigma> c \<in> ?\<Omega> \<sigma>" if "c \<in> \<Sigma> \<sigma>" for \<sigma> c
    unfolding book_countable_signature_image_def
    by (rule book_typed_image_maps; rule that)
  have target_language: "book_theory_formula ?\<Omega> G P" if member: "P \<in> ?T" for P
  proof -
    obtain A where am: "A \<in> S" and eq: "P = book_typed_name_map ?\<rho> A"
      using member by (elim Set.imageE)
    show ?thesis unfolding eq by (rule book_typed_name_map_language[OF language[OF am] maps])
  qed
  have target_consistent: "book_full_C_theory_consistent ?\<Omega> G ?T"
    using consistent book_full_C_countable_signature_consistency_iff[OF rich small language] by blast
  interpret names: book_countable_ambient_signature ?\<Omega> "\<lambda>_. UNIV"
    by (rule book_countable_signature_has_ambient)
  obtain W R root D i I J where
    model: "book_ZF_nontrivial_modal_model W R root D i ?\<Omega> I" and
    interp: "book_ZF_modal_interpretation W R root D i ?\<Omega> I G J" and
    truth: "book_ZF_satisfies D G J root ?T"
    using names.book_full_C_ambient_nontrivial_modal_model_exists[OF rich target_language target_consistent]
    by blast
  interpret M: book_ZF_modal_interpretation W R root D i ?\<Omega> I G J
    by (rule interp)
  interpret N: book_ZF_nontrivial_modal_model W R root D i ?\<Omega> I
    by (rule model)
  let ?I = "\<lambda>c \<sigma>. I (?\<rho> \<sigma> c) \<sigma>"
  let ?J = "\<lambda>w g A. J w g (book_typed_name_map ?\<rho> A)"
  have pulled_model: "book_ZF_nontrivial_modal_model W R root D i \<Sigma> ?I"
    by (rule N.nontrivial_signature_pullback[OF maps])
  have pulled_interp: "book_ZF_modal_interpretation W R root D i \<Sigma> ?I G ?J"
    by (rule M.signature_pullback_interpretation[OF maps])
  have pulled_truth: "book_ZF_satisfies D G ?J root S"
    by (simp only: book_ZF_signature_pullback_satisfies; rule truth)
  show ?thesis
    apply (rule exI[where x=W], rule exI[where x=R], rule exI[where x=root])
    apply (rule exI[where x=D], rule exI[where x=i])
    apply (rule exI[where x="?I"], rule exI[where x="?J"])
    apply (rule conjI[OF pulled_model conjI[OF pulled_interp pulled_truth]])
    done
qed

text \<open>
  This strengthens the previous original-signature existence conclusion
  to the explicit nontrivial modal class. The assumptions on Σ, G and S
  are unchanged: only the declared constants at each type are countable;
  open formulas and arbitrary premise sets remain allowed. The same
  signature pullback preserves all worldwise nontriviality conditions.
  Generic soundness, unrestricted signatures and final modal completeness
  remain separate obligations. No claim is made that the added conditions
  are a literal transcription of every printed Definition 18.1 clause.
\<close>

end
