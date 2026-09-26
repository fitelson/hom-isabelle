theory Bacon_Book_ZF_Ambient_Nontrivial_Existence
  imports Bacon_Book_ZF_Original_Theory_Truth Bacon_Book_ZF_Canonical_Nontrivial_Model
begin

context book_coded_ambient_signature
begin

theorem book_full_C_ambient_nontrivial_modal_model_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_nontrivial_modal_model W R root D i \<Sigma> I \<and>
    book_ZF_modal_interpretation W R root D i \<Sigma> I G J \<and>
    book_ZF_satisfies D G J root S"
proof -
  obtain actual where world: "actual \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and originals: "\<forall>A\<in>S. book_universal_closure G A \<in> snd actual"
    using book_full_C_canonical_world_exists[OF rich language consistent] by blast
  interpret C: book_full_C_coded_frame \<Sigma> B G actual term_code term_bound
    by (unfold_locales; rule rich world term_code_injective term_code_bound)
  have contained: "\<And>A. A \<in> S \<Longrightarrow> book_universal_closure G A \<in> snd actual"
    by (rule bspec[OF originals]; assumption)
  have satisfied: "book_ZF_satisfies C.full_ZF_D_at G C.full_ZF_J C.full_ZF_root S"
    by (rule C.full_ZF_original_theory_satisfied[OF language contained])
  show ?thesis
    apply (rule exI[where x=C.full_world_set])
    apply (rule exI[where x=C.full_ZF_R])
    apply (rule exI[where x=C.full_ZF_root])
    apply (rule exI[where x=C.full_ZF_D_at])
    apply (rule exI[where x=C.full_ZF_i_at])
    apply (rule exI[where x=C.full_ZF_constant_value])
    apply (rule exI[where x=C.full_ZF_J])
    apply (rule conjI[OF C.full_ZF_canonical_nontrivial_modal_model])
    apply (rule conjI[OF C.full_ZF_canonical_interpretation satisfied])
    done
qed

end

text \<open>
  The same canonical construction now yields the explicit nontrivial
  refinement: every type domain is inhabited and a false proposition
  exists at every world. These are proved properties of the constructed
  data, not extra hypotheses on the original theory. The coded
  ambient-signature (book_coded_ambient_signature) and rich-stock
  conditions remain; countable coding is one instance. This is forward
  existence only; generic soundness is Bacon_Book_ZF_Full_C_Soundness
  and the consistency equivalences are Bacon_Book_ZF_Full_C_Completeness
  and Bacon_Book_ZF_Full_C_Declared_Names_Completeness.
\<close>

end
