theory Bacon_Book_Lambda_I_Environment_Substitution_Conversion
  imports Bacon_Book_Lambda_I_Conversion
    Bacon_Book_Environment_Development.Bacon_Book_Environment_Substitution_Conversion
begin

section \<open>Closed λI environment substitution preserves the λI property\<close>

text \<open>
  Substituting closed λI terms for the free variables outside a protected
  set keeps a λI term λI: bound occurrences are protected, so every
  binder still occurs in its body, and the closed replacements contribute
  no new binders with vacuous bodies.
\<close>

lemma book_lambda_I_environment_subst:
  assumes lambda_I: "book_lambda_I A"
    and replacements: "\<And>n. book_lambda_I (r n)"
    and closed: "\<And>n. named_fv (r n) = {}"
  shows "book_lambda_I (book_environment_subst B r A)"
  using lambda_I
proof (induction A arbitrary: B)
  case (NVar n)
  show ?case by (cases "n \<in> B"; simp add: replacements)
next
  case (NConst c \<sigma>)
  show ?case by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  show ?case using NApp.prems NApp.IH by simp
next
  case (NLam n A)
  have body: "book_lambda_I A" and occurs: "n \<in> named_fv A" using NLam.prems by simp_all
  have mapped_body: "book_lambda_I (book_environment_subst (insert n B) r A)" by (rule NLam.IH[OF body])
  have mapped_occurs: "n \<in> named_fv (book_environment_subst (insert n B) r A)"
    using occurs by (simp add: book_environment_subst_fv[OF closed])
  show ?case using mapped_body mapped_occurs by simp
qed

lemma book_lambda_I_environment_subst_LI:
  assumes member: "A \<in> book_LI \<Sigma> G \<tau>"
    and replacements: "\<And>n. r n \<in> book_LI \<Sigma> G (G n)"
    and closed: "\<And>n. named_fv (r n) = {}"
  shows "book_environment_subst B r A \<in> book_LI \<Sigma> G \<tau>"
proof (rule book_LI_I)
  show "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_environment_subst B r A) \<tau>"
    by (rule book_environment_subst_language[OF book_lambda_I_terms_language[OF member]];
      rule book_lambda_I_terms_language[OF replacements])
next
  show "book_lambda_I (book_environment_subst B r A)"
    by (rule book_lambda_I_environment_subst[OF book_lambda_I_terms_relevant[OF member]
      book_lambda_I_terms_relevant[OF replacements] closed])
qed

section \<open>Internal conversion is preserved\<close>

text \<open>
  If A and C are internally convertible at τ and every r(n) is a closed
  λI term of type G(n) in Σ, then A[r] and C[r] are internally
  convertible at τ. Each node of the chain is substituted; the β/η steps
  are preserved by the existing closed-payload step lemmas.
\<close>

theorem book_lambda_I_environment_subst_conv:
  assumes replacements: "\<And>n. r n \<in> book_LI \<Sigma> G (G n)"
    and closed: "\<And>n. named_fv (r n) = {}"
    and conversion: "book_lambda_I_conv \<Sigma> G \<tau> A C"
  shows "book_lambda_I_conv \<Sigma> G \<tau> (book_environment_subst B r A) (book_environment_subst B r C)"
  using conversion
proof (induction rule: book_lambda_I_conv.induct)
  case Refl
  show ?case by (rule book_lambda_I_conv.Refl[
    OF book_lambda_I_environment_subst_LI[OF Refl.hyps replacements closed]])
next
  case Beta
  show ?case by (rule book_lambda_I_conv.Beta[
    OF book_lambda_I_environment_subst_LI[OF Beta.hyps(1) replacements closed]
      book_lambda_I_environment_subst_LI[OF Beta.hyps(2) replacements closed]
      book_environment_subst_beta_step[OF closed Beta.hyps(3)]])
next
  case Eta
  show ?case by (rule book_lambda_I_conv.Eta[
    OF book_lambda_I_environment_subst_LI[OF Eta.hyps(1) replacements closed]
      book_lambda_I_environment_subst_LI[OF Eta.hyps(2) replacements closed]
      book_environment_subst_eta_step[OF closed Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule book_lambda_I_conv.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule book_lambda_I_conv.Trans[OF Trans.IH])
qed

end
