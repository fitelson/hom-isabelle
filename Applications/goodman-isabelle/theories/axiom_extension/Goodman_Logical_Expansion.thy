theory Goodman_Logical_Expansion
  imports Goodman_Translation_Support
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Characterization
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution_Representation
    Bacon_Source_Vocabulary_Development.Bacon_Source_Vector_Syntax
begin

section \<open>Logical expansion with de Bruijn binding retained\<close>

text \<open>
  This intermediate syntax is the core's generic source grammar, with
  the book's minimal logical symbols. We retain the old slots but expand
  its primitive Boolean/equality constructors into the actual book terms.
  Re-encoding the named translation will be proved to give this expansion.
  It is an auxiliary syntactic representation, not a new object logic.
\<close>

abbreviation gi_code where "gi_code G C \<equiv> named_to_source G [] C"

lemma gi_closed_code_rename:
  "named_fv C = {} \<Longrightarrow> srename r (gi_code G C) = gi_code G C"
  by (rule srename_closed, rule named_to_source_closed; assumption)

lemma gi_closed_code_subst:
  assumes closed: "named_fv C = {}"
  shows "ssubst s (gi_code G C) = gi_code G C"
  by (rule ssubst_fv_identity; simp add: named_to_source_empty_fv closed)

lemma gi_closed_code_stack:
  assumes closed: "named_fv C = {}"
  shows "named_to_source G ns C = gi_code G C"
proof -
  have unchanged: "srename (named_index ns) (gi_code G C) = gi_code G C"
    by (rule gi_closed_code_rename[OF closed])
  show ?thesis using unchanged named_to_source_stack_from_empty[where G=G and ns=ns and A=C] by simp
qed

fun gi_expand ::
  "sgcontext \<Rightarrow> (string \<Rightarrow> otype \<Rightarrow> 'c) \<Rightarrow> oterm \<Rightarrow> ('c, book_minimal_logical) sterm" where
  "gi_expand G k (Var n) = SVar n"
| "gi_expand G k (Const c \<sigma>) = SConst (k c \<sigma>) \<sigma>"
| "gi_expand G k (App F A) = SApp (gi_expand G k F) (gi_expand G k A)"
| "gi_expand G k (Lam \<sigma> A) = SLam \<sigma> (gi_expand G k A)"
| "gi_expand G k (Eq \<sigma> A B) =
    SApp (SApp (gi_code G (book_leibniz_const G \<sigma>)) (gi_expand G k A)) (gi_expand G k B)"
| "gi_expand G k (Neg A) = SApp (gi_code G (book_not_const G)) (gi_expand G k A)"
| "gi_expand G k (Conj A B) =
    SApp (SApp (gi_code G (book_and_const G)) (gi_expand G k A)) (gi_expand G k B)"
| "gi_expand G k (Disj A B) =
    SApp (SApp (gi_code G (book_or_const G)) (gi_expand G k A)) (gi_expand G k B)"
| "gi_expand G k (Imp A B) = SApp (SApp (SLogical SImp) (gi_expand G k A)) (gi_expand G k B)"
| "gi_expand G k (Forall \<sigma> A) = SApp (SLogical (SBAll \<sigma>)) (SLam \<sigma> (gi_expand G k A))"
| "gi_expand G k (Exists \<sigma> A) = SApp (gi_code G (book_exists_const G \<sigma>)) (SLam \<sigma> (gi_expand G k A))"

lemma gi_expand_rename:
  "gi_expand G k (rename r A) = srename r (gi_expand G k A)"
  by (induction A arbitrary: r)
    (simp_all add: gi_closed_code_rename book_leibniz_const_closed book_not_const_closed
      book_and_const_closed book_or_const_closed book_exists_const_closed)

lemma gi_expand_shift:
  "gi_expand G k (shift A) = sshift (gi_expand G k A)"
  by (simp add: shift_def sshift_def gi_expand_rename)

lemma gi_expand_lift_subst:
  "(\<lambda>n. gi_expand G k (lift_subst s n)) = slift_subst (\<lambda>n. gi_expand G k (s n))"
  by (rule ext, rename_tac n, case_tac n) (simp_all add: gi_expand_rename)

theorem gi_expand_subst:
  "gi_expand G k (subst s A) = ssubst (\<lambda>n. gi_expand G k (s n)) (gi_expand G k A)"
  by (induction A arbitrary: s)
    (simp_all add: gi_closed_code_subst book_leibniz_const_closed book_not_const_closed
      book_and_const_closed book_or_const_closed book_exists_const_closed gi_expand_lift_subst)

corollary gi_expand_subst0:
  "gi_expand G k (subst0 B A) = ssubst0 (gi_expand G k B) (gi_expand G k A)"
proof -
  have replacements: "(\<lambda>n. gi_expand G k (case_nat B Var n)) = case_nat (gi_expand G k B) SVar"
    by (rule ext, rename_tac n, case_tac n) simp_all
  show ?thesis by (simp add: subst0_def ssubst0_def gi_expand_subst replacements)
qed

text \<open>
  These are syntactic identities for the intermediate expansion, including
  arbitrary simultaneous substitution. They do not yet say that literal
  named_subst commutes with the named translation; different fresh names
  generally require α-conversion there.
\<close>

end
