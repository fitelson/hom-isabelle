theory Bacon_Book_Environment_Substitution_Conversion
  imports Bacon_Book_Environment_Substitution_Contractions
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
begin

section \<open>Closed replacements preserve contextual contractions\<close>

text \<open>
  A→βC or A→ηC remains a corresponding contextual step after
  replacing free variables by closed terms. The bound-name set is
  generalized in the induction: a λn context uses B∪{n}, not B.
  Source role: contextual conversion in Bacon's β/η schemas,
  pp.97–98, and the term interpretation on p.321.

  The root-preservation hypothesis in the generic helper ranges over
  every bound-name set. The β and η specializations use the proved
  closed-payload root lemmas; no congruence property is assumed of a
  model or denotation operation.
\<close>

lemma book_environment_subst_compatible:
  assumes step: "named_compatible_step R A C"
    and roots: "\<And>B M N. R M N \<Longrightarrow>
      Q (book_environment_subst B r M) (book_environment_subst B r N)"
  shows "named_compatible_step Q (book_environment_subst B r A) (book_environment_subst B r C)"
  using step
proof (induction arbitrary: B rule: named_compatible_step.induct)
  case (root M N)
  have mapped: "Q (book_environment_subst B r M) (book_environment_subst B r N)"
    by (rule roots[OF root.hyps])
  show ?case by (rule named_compatible_step.root[where R=Q
    and M="book_environment_subst B r M" and N="book_environment_subst B r N", OF mapped])
next
  case (App_left M M' N)
  show ?case by (simp only: book_environment_subst.simps;
    rule named_compatible_step.App_left[OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: book_environment_subst.simps;
    rule named_compatible_step.App_right[OF App_right.IH])
next
  case (Lam_body M M' n)
  have body: "named_compatible_step Q (book_environment_subst (insert n B) r M)
    (book_environment_subst (insert n B) r M')"
    by (rule Lam_body.IH)
  show ?case by (simp only: book_environment_subst.simps;
    rule named_compatible_step.Lam_body[OF body])
qed

theorem book_environment_subst_beta_step:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and step: "named_compatible_step named_beta_contract A C"
  shows "named_compatible_step named_beta_contract
    (book_environment_subst B r A) (book_environment_subst B r C)"
  by (rule book_environment_subst_compatible[OF step];
    rule book_environment_subst_beta_contract[OF closed]; assumption)

theorem book_environment_subst_eta_step:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and step: "named_compatible_step named_eta_contract A C"
  shows "named_compatible_step named_eta_contract
    (book_environment_subst B r A) (book_environment_subst B r C)"
  by (rule book_environment_subst_compatible[OF step];
    rule book_environment_subst_eta_contract[OF closed]; assumption)

section \<open>Typed raw βη conversion is preserved\<close>

text \<open>
  If A≡βηC at type τ, and every r(n) is closed and has type G(n),
  then A[r]≡βηC[r] at τ. Raw conversion here retains typing at
  every intermediate node but uses the universal nonlogical signature.
  The explicit Raw_Conversion import fixes that exact meaning.

  This does not impose a declared-signature restriction on replacement
  payloads or conversion intermediates. No model, J, Functionality,
  representative-equivalence, or canonical-domain premise is used.
\<close>

lemma book_environment_subst_universal_language:
  assumes language: "named_in_language L (\<lambda>_. UNIV) G A \<tau>"
    and replacements: "\<And>n. has_ntype L G (r n) (G n)"
  shows "named_in_language L (\<lambda>_. UNIV) G (book_environment_subst B r A) \<tau>"
proof -
  have typed: "has_ntype L G A \<tau>" using language by (simp only: named_universal_language)
  have mapped: "has_ntype L G (book_environment_subst B r A) \<tau>"
    by (rule book_environment_subst_type[OF typed replacements])
  show ?thesis by (simp only: named_universal_language; rule mapped)
qed

theorem book_environment_subst_raw_conversion:
  assumes closed: "\<And>n. named_fv (r n) = {}"
    and replacements: "\<And>n. has_ntype L G (r n) (G n)"
    and conversion: "named_raw_beta_eta L G \<tau> A C"
  shows "named_raw_beta_eta L G \<tau> (book_environment_subst B r A) (book_environment_subst B r C)"
  using conversion
proof (induction rule: named_beta_eta_in_language.induct)
  case Refl
  show ?case by (rule named_beta_eta_in_language.Refl[
    OF book_environment_subst_universal_language[OF Refl.hyps replacements]])
next
  case Beta
  show ?case by (rule named_beta_eta_in_language.Beta[
    OF book_environment_subst_universal_language[OF Beta.hyps(1) replacements]
      book_environment_subst_universal_language[OF Beta.hyps(2) replacements]
      book_environment_subst_beta_step[OF closed Beta.hyps(3)]])
next
  case Eta
  show ?case by (rule named_beta_eta_in_language.Eta[
    OF book_environment_subst_universal_language[OF Eta.hyps(1) replacements]
      book_environment_subst_universal_language[OF Eta.hyps(2) replacements]
      book_environment_subst_eta_step[OF closed Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule named_beta_eta_in_language.Trans[OF Trans.IH])
qed

end
