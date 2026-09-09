theory Bacon_Book_Constant_Renaming_Conversion
  imports Bacon_Book_Constant_Renaming
begin

section \<open>Forward raw typed conversion under constant renaming\<close>

text \<open>
  A≡βηB implies f(A)≡βηf(B) when f changes only nonlogical
  constant names. Every intermediate term retains its type in the
  unchanged variable stock G. Source role: signature pullback for the
  environment condition of Bacon, Definition 14.13, p.302.

  The raw relation permits foreign intermediate constants but no ill-typed
  node. Neither injectivity, a rich stock, nor a model is required.
  This is forward preservation only, not conversion reflection.
\<close>

lemma book_constant_rename_universal_language:
  assumes language: "named_in_language L (\<lambda>_. UNIV) G A \<tau>"
  shows "named_in_language L (\<lambda>_. UNIV) G (book_constant_rename f A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" using language by (simp only: named_universal_language)
  show ?thesis by (simp only: named_universal_language; rule book_constant_rename_type[OF typed])
qed

theorem book_constant_rename_raw_conversion:
  assumes conversion: "named_raw_beta_eta L G \<tau> A B"
  shows "named_raw_beta_eta L G \<tau> (book_constant_rename f A) (book_constant_rename f B)"
  using conversion
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  show ?case by (rule named_beta_eta_in_language.Refl[
    OF book_constant_rename_universal_language[OF Refl.hyps]])
next
  case (Beta A \<tau> B)
  have first: "named_in_language L (\<lambda>_. UNIV) G (book_constant_rename f A) \<tau>"
    by (rule book_constant_rename_universal_language[OF Beta.hyps(1)])
  have second: "named_in_language L (\<lambda>_. UNIV) G (book_constant_rename f B) \<tau>"
    by (rule book_constant_rename_universal_language[OF Beta.hyps(2)])
  have step: "named_compatible_step named_beta_contract (book_constant_rename f A) (book_constant_rename f B)"
    by (rule book_constant_rename_beta_step[OF Beta.hyps(3)])
  show ?case by (rule named_beta_eta_in_language.Beta[OF first second step])
next
  case (Eta A \<tau> B)
  have first: "named_in_language L (\<lambda>_. UNIV) G (book_constant_rename f A) \<tau>"
    by (rule book_constant_rename_universal_language[OF Eta.hyps(1)])
  have second: "named_in_language L (\<lambda>_. UNIV) G (book_constant_rename f B) \<tau>"
    by (rule book_constant_rename_universal_language[OF Eta.hyps(2)])
  have step: "named_compatible_step named_eta_contract (book_constant_rename f A) (book_constant_rename f B)"
    by (rule book_constant_rename_eta_step[OF Eta.hyps(3)])
  show ?case by (rule named_beta_eta_in_language.Eta[OF first second step])
next
  case Sym
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule named_beta_eta_in_language.Trans[OF Trans.IH])
qed

end
