theory Bacon_Book_Lambda_I_Constant_Renaming_Conversion
  imports Bacon_Book_Lambda_I_Theory_Constant_Renaming Bacon_Book_Lambda_I_Conversion
begin

section \<open>Forward internal conversion under constant renaming\<close>

text \<open>
  If A and B are internally convertible λI terms of Σ and f maps Σ into
  Ω, then f(A) and f(B) are internally convertible λI terms of Ω: every
  node of the chain is renamed, stays a λI term, keeps its type, and the
  β/η steps are preserved by the existing renaming lemmas. Neither
  injectivity, a rich stock, nor a model is required. This is forward
  preservation only, not reflection.
\<close>

theorem book_lambda_I_constant_rename_conv:
  assumes maps: "\<And>\<tau> c. c \<in> \<Sigma> \<tau> \<Longrightarrow> f c \<in> \<Omega> \<tau>"
    and conversion: "book_lambda_I_conv \<Sigma> G \<tau> A B"
  shows "book_lambda_I_conv \<Omega> G \<tau> (book_constant_rename f A) (book_constant_rename f B)"
  using conversion
proof (induction rule: book_lambda_I_conv.induct)
  case (Refl A \<tau>)
  show ?case by (rule book_lambda_I_conv.Refl[OF book_lambda_I_constant_rename_terms[OF Refl.hyps maps]])
next
  case (Beta A \<tau> B)
  show ?case by (rule book_lambda_I_conv.Beta[OF book_lambda_I_constant_rename_terms[OF Beta.hyps(1) maps]
    book_lambda_I_constant_rename_terms[OF Beta.hyps(2) maps] book_constant_rename_beta_step[OF Beta.hyps(3)]])
next
  case (Eta A \<tau> B)
  show ?case by (rule book_lambda_I_conv.Eta[OF book_lambda_I_constant_rename_terms[OF Eta.hyps(1) maps]
    book_lambda_I_constant_rename_terms[OF Eta.hyps(2) maps] book_constant_rename_eta_step[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule book_lambda_I_conv.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule book_lambda_I_conv.Trans[OF Trans.IH])
qed

end
