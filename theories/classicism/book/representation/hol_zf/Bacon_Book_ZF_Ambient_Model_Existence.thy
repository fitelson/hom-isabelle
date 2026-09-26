theory Bacon_Book_ZF_Ambient_Model_Existence
  imports Bacon_Book_ZF_Original_Theory_Truth
begin

context book_coded_ambient_signature
begin

theorem book_full_C_ambient_modal_model_exists:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>W R root D i I J.
    book_ZF_modal_model W R root D i \<Sigma> I \<and>
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
    apply (rule conjI[OF C.full_ZF_canonical_modal_model])
    apply (rule conjI[OF C.full_ZF_canonical_interpretation satisfied])
    done
qed

end

text \<open>
  Theorem 18.4's existence assembly is checked here in the coded
  ambient-signature locale book_coded_ambient_signature: a
  full-C-consistent set of original formulas has an actual independent
  modal model and an admissible interpretation satisfying the entire
  set. Open formulas and infinite premise sets are allowed. The ambient
  signature's infinite reserve and the bounded term code injective on
  admitted terms remain explicit through the locale; the countable
  ambient signature (book_countable_ambient_signature) is one instance
  of it. The ambient premise is removed by signature recoding and
  semantic pullback in Bacon_Book_ZF_Countable_Model_Existence,
  Bacon_Book_ZF_Small_Carrier_Existence and
  Bacon_Book_ZF_Declared_Names_Existence. This theorem is forward
  existence only; generic soundness and the completeness equivalences
  are in the Bacon_Book_ZF_Modal_Soundness session.
\<close>

end
