theory Bacon_Book_Constant_Renaming
  imports Bacon_Book_Minimal_Formula_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
begin

section \<open>Changing the carrier of nonlogical names\<close>

text \<open>
  The map f sends c:σ to f(c):σ and commutes with application and
  abstraction; variable names, their stock G, and logical symbols remain
  fixed. It sends ℒ(Λ,Σ) into ℒ(Λ,f[Σ]), where f[Σ](σ)=f[Σ(σ)].
  Source role: signature enlargement in Bacon, Proposition 15.4, p.319.
  An injection into a sum carrier can supply new names without assuming
  that the original name type has unused elements.

  Representation. We reuse the datatype-generated map_named_term,
  specializing its logical-symbol map to the identity. Source and target
  name carriers may differ and have arbitrary cardinalities. Forward
  language, substitution and conversion preservation need no injectivity;
  reflection of declared-name membership below explicitly requires it.
  This leaf is pure syntax, not theory transport or model existence.
\<close>

definition book_constant_rename ::
  "('c \<Rightarrow> 'd) \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('d,'l) named_term" where
  "book_constant_rename f A = map_named_term f id A"

lemma book_constant_rename_simps [simp]:
  "book_constant_rename f (NVar n) = NVar n"
  "book_constant_rename f (NConst c \<sigma>) = NConst (f c) \<sigma>"
  "book_constant_rename f (NLogical l) = NLogical l"
  "book_constant_rename f (NApp A B) = NApp (book_constant_rename f A) (book_constant_rename f B)"
  "book_constant_rename f (NLam n A) = NLam n (book_constant_rename f A)"
  by (simp_all add: book_constant_rename_def)

lemma book_constant_rename_id: "book_constant_rename id A = A"
  by (induction A) simp_all

lemma book_constant_rename_comp:
  "book_constant_rename g (book_constant_rename f A) = book_constant_rename (g \<circ> f) A"
  by (induction A) simp_all

lemma book_constant_rename_fv: "named_fv (book_constant_rename f A) = named_fv A"
  by (induction A) simp_all

lemma book_constant_rename_vars: "named_vars (book_constant_rename f A) = named_vars A"
  by (induction A) simp_all

lemma book_constant_rename_logicals:
  "named_logical_occurrences (book_constant_rename f A) = named_logical_occurrences A"
  by (induction A) simp_all

theorem book_constant_rename_type:
  assumes typed: "has_ntype L G A \<tau>"
  shows "has_ntype L G (book_constant_rename f A) \<tau>"
  using typed
proof (induction rule: has_ntype.induct)
  case (Var n)
  show ?case by (simp only: book_constant_rename_simps; rule has_ntype.Var)
next
  case (Const c \<sigma>)
  show ?case by (simp only: book_constant_rename_simps; rule has_ntype.Const)
next
  case (Logical l)
  show ?case by (simp only: book_constant_rename_simps; rule has_ntype.Logical)
next
  case (App F \<sigma> \<tau> A)
  show ?case by (simp only: book_constant_rename_simps; rule has_ntype.App[OF App.IH])
next
  case (Lam A \<tau> n)
  show ?case by (simp only: book_constant_rename_simps; rule has_ntype.Lam[OF Lam.IH])
qed

lemma book_constant_rename_signature_preimage:
  "named_in_signature \<Omega> (book_constant_rename f A) =
    named_in_signature (\<lambda>\<sigma>. {c. f c \<in> \<Omega> \<sigma>}) A"
  by (induction A) simp_all

lemma book_constant_rename_signature:
  assumes names: "named_in_signature \<Sigma> A"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> \<Omega> \<sigma>"
  shows "named_in_signature \<Omega> (book_constant_rename f A)"
  using names
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst c \<sigma>)
  have declared: "c \<in> \<Sigma> \<sigma>" using NConst.prems by simp
  show ?case by (simp only: book_constant_rename_simps named_in_signature.simps; rule maps[OF declared])
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fn: "named_in_signature \<Sigma> F" and an: "named_in_signature \<Sigma> A"
    using NApp.prems by simp_all
  show ?case by (simp only: book_constant_rename_simps named_in_signature.simps;
    rule conjI[OF NApp.IH(1)[OF fn] NApp.IH(2)[OF an]])
next
  case (NLam n A)
  have an: "named_in_signature \<Sigma> A" using NLam.prems by simp
  show ?case by (simp only: book_constant_rename_simps named_in_signature.simps; rule NLam.IH[OF an])
qed

theorem book_constant_rename_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    and maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> f c \<in> \<Omega> \<sigma>"
  shows "book_in_language L \<Lambda> \<Omega> G (book_constant_rename f A) \<tau>"
proof -
  have typed: "has_ntype L G (book_constant_rename f A) \<tau>"
    by (rule book_constant_rename_type[OF book_language_type[OF language]])
  have names: "named_in_signature \<Omega> (book_constant_rename f A)"
    by (rule book_constant_rename_signature[OF book_language_signature[OF language] maps])
  have logicals: "named_logical_occurrences (book_constant_rename f A) \<subseteq> \<Lambda>"
    by (simp only: book_constant_rename_logicals; rule book_language_logical_occurrences[OF language])
  show ?thesis unfolding book_in_language_def named_in_language_def
    by (rule conjI[OF conjI[OF typed names] logicals])
qed

corollary book_constant_rename_image_language:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_in_language L \<Lambda> (\<lambda>\<sigma>. image f (\<Sigma> \<sigma>)) G (book_constant_rename f A) \<tau>"
  by (rule book_constant_rename_language[OF language]; rule imageI; assumption)

lemma book_constant_rename_injective_signature:
  assumes injective: "inj f"
  shows "named_in_signature (\<lambda>\<sigma>. image f (\<Sigma> \<sigma>)) (book_constant_rename f A)
    \<longleftrightarrow> named_in_signature \<Sigma> A"
proof -
  have preimage: "(\<lambda>\<sigma>. {c. f c \<in> image f (\<Sigma> \<sigma>)}) = \<Sigma>"
    by (rule ext; rule set_eqI; use injective in \<open>auto dest: injD\<close>)
  show ?thesis by (simp only: book_constant_rename_signature_preimage preimage)
qed

section \<open>Literal replacement and contraction\<close>

lemma book_constant_rename_subst:
  "book_constant_rename f (named_subst x B A) =
    named_subst x (book_constant_rename f B) (book_constant_rename f A)"
  by (induction A) (simp_all split: if_splits)

lemma book_constant_rename_free_for:
  "named_free_for (book_constant_rename f B) x (book_constant_rename f A) = named_free_for B x A"
  by (induction A) (simp_all add: book_constant_rename_fv)

lemma book_constant_rename_beta:
  assumes step: "named_beta_contract A B"
  shows "named_beta_contract (book_constant_rename f A) (book_constant_rename f B)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  have permitted: "named_free_for (book_constant_rename f B) x (book_constant_rename f A)"
    by (simp only: book_constant_rename_free_for; rule beta.hyps)
  show ?case by (simp only: book_constant_rename_simps book_constant_rename_subst;
    rule named_beta_contract.beta[OF permitted])
qed

lemma book_constant_rename_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_constant_rename f A) (book_constant_rename f B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (book_constant_rename f F)"
    by (simp only: book_constant_rename_fv; rule eta.hyps)
  show ?case by (simp only: book_constant_rename_simps; rule named_eta_contract.eta[OF fresh])
qed

lemma book_constant_rename_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow> Q (book_constant_rename f M) (book_constant_rename f N)"
  shows "named_compatible_step Q (book_constant_rename f A) (book_constant_rename f B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  have converted: "Q (book_constant_rename f M) (book_constant_rename f N)"
    by (rule roots[OF root.hyps])
  show ?case by (rule named_compatible_step.root[where R=Q, OF converted])
next
  case (App_left M M' N)
  show ?case by (simp only: book_constant_rename_simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: book_constant_rename_simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case (Lam_body M M' n)
  show ?case by (simp only: book_constant_rename_simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

corollary book_constant_rename_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B"
  shows "named_compatible_step named_beta_contract (book_constant_rename f A) (book_constant_rename f B)"
  by (rule book_constant_rename_compatible[OF step]; rule book_constant_rename_beta; assumption)

corollary book_constant_rename_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (book_constant_rename f A) (book_constant_rename f B)"
  by (rule book_constant_rename_compatible[OF step]; rule book_constant_rename_eta; assumption)

section \<open>The book's literal abbreviations retain their shape\<close>

lemma book_constant_rename_imp:
  "book_constant_rename f (book_imp A B) = book_imp (book_constant_rename f A) (book_constant_rename f B)"
  by (simp only: book_imp_def book_constant_rename_simps)

lemma book_constant_rename_all:
  "book_constant_rename f (book_all G n A) = book_all G n (book_constant_rename f A)"
  by (simp only: book_all_def book_constant_rename_simps)

lemma book_constant_rename_bottom:
  "book_constant_rename f (book_bottom G) = book_bottom G"
  by (simp only: book_bottom_def book_constant_rename_simps)

lemma book_constant_rename_not:
  "book_constant_rename f (book_not G A) = book_not G (book_constant_rename f A)"
  by (simp only: book_not_def book_not_const_def book_constant_rename_simps
    book_constant_rename_imp book_constant_rename_bottom)

text \<open>
  Next proof obligations are transport of the nine theory constructors,
  then a conservativity argument for injective signature enlargement.
  The present forward map alone establishes neither of those results.
\<close>

end
