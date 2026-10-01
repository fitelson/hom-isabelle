theory Typed_Source_Soundness
  imports Typed_Source_Model
    "Bacon_Book_ZF_Modal_Soundness.Bacon_Book_ZF_Full_C_Soundness"
begin

section \<open>The concrete interpretation validates the book's full C\<close>

theorem src_full_C_interpretation:
  assumes rich: "sg_rich G"
  shows "\<exists>J. book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T \<Sigma> src_I G J \<and>
    (\<forall>A. book_full_C_proves \<Sigma> G A \<longrightarrow>
      book_ZF_valid_everywhere raw_W src_D G J A)"
proof -
  obtain J where interp:
    "book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T \<Sigma> src_I G J"
    using src_interpretation_exists[where \<Sigma>=\<Sigma> and G=G] by blast
  interpret model: book_ZF_nontrivial_modal_interpretation
    raw_W raw_rel raw_root src_D src_T \<Sigma> src_I G J
    by (rule book_ZF_nontrivial_modal_interpretation.intro[OF src_nontrivial_model interp])
  have valid: "\<forall>A. book_full_C_proves \<Sigma> G A \<longrightarrow>
    book_ZF_valid_everywhere raw_W src_D G J A"
    by (intro allI impI; rule model.full_C_valid_everywhere[OF rich]; assumption)
  show ?thesis by (rule exI[where x=J], rule conjI[OF interp valid])
qed

text \<open>This is an actual application of the previously verified full-C
  soundness theorem to the constructed nontrivial source model. It is not
  an assumed validity field or a theorem about an arbitrary supplied
  interpreter. It uses the book's full minimal-language C calculus.
  It does not yet encode the additional hypotheses of Proposition 2.11,
  its Rigid Comprehension conclusion, or the paper's distinct primitive
  logical vocabulary and Definition 3.20 action-model predicate.\<close>

ML \<open>
  val th = @{thm src_full_C_interpretation};
  val _ = if null (Thm_Deps.all_oracles [th]) andalso null (Thm.hyps_of th)
    andalso null (Thm.tpairs_of th) then
      writeln "SOURCE-C: concrete full-C interpretation, with only the stated rich-context guard"
    else error "Unexpected dependency or residual proof obligation";
\<close>

end
