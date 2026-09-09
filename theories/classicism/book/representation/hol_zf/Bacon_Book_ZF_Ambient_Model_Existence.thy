theory Bacon_Book_ZF_Ambient_Model_Existence
  imports Bacon_Book_ZF_Original_Theory_Truth
begin

context book_countable_ambient_signature
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
  interpret C: book_full_C_canonical_frame \<Sigma> B G actual
    by (unfold_locales; rule rich world)
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
  Theorem 18.4's existence assembly is now checked in the fixed
  countable ambient signature: a full-C-consistent set of original
  formulas has an actual independent modal model and an admissible
  interpretation satisfying the entire set. Open formulas and infinite
  premise sets are allowed. The ambient signature's infinite reserve
  remains explicit through the locale. Removing that ambient premise
  by countable-signature recoding and semantic pullback is a further
  step; this is not yet unrestricted soundness/completeness.
\<close>

end
