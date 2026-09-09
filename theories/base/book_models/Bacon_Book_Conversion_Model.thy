theory Bacon_Book_Conversion_Model
  imports Bacon_Book_Conversion_Closed_Values Bacon_Book_Conversion_Universal_Valuation
    Bacon_Book_Full_Minimal_Model
begin

section \<open>The constructed conversion classes satisfy the minimal model interface\<close>

text \<open>
  In the full witness signature Σ∞, take Dτ to be the βη classes of
  typed closed terms, application to be application of representatives,
  J to be the constructed closed-substitution denotation, v to be the
  characteristic valuation of M, and κ(l)=[l]type(l).
  If M is maximal closed-consistent and closed constant-witness complete,
  these ACTUAL functions form a full minimal model.

  Source role: the term-model assembly on Bacon pp.320–321, using the
  explicitly repaired closed-decision construction. The environment
  theorem, typed assignment witnessing logical closed values, and all
  logical truth clauses are proved ingredients, not model premises.
  No Functionality, separation, alternative function-space carrier, or
  pointwise abstraction extensionality is assumed.

  Scope: full typed language, minimal logical basis, full witness
  signature, and the stated syntactic hypotheses on M. This assembly
  theorem does not itself prove that such an M exists or identify this
  model class with every arbitrary admitted-language version of the book.
\<close>

theorem book_henkin_conversion_model:
  assumes rich: "sg_rich G"
    and maximal: "book_closed_maximal_extension (book_henkin_full_signature \<Sigma> G) G S M"
    and witnesses: "book_closed_constant_witness_complete (book_henkin_full_signature \<Sigma> G) G M"
  shows "book_full_minimal_model
    (book_conversion_domain (book_henkin_full_signature \<Sigma> G) G)
    (book_conversion_app (book_henkin_full_signature \<Sigma> G) G)
    (book_henkin_full_signature \<Sigma> G) G
    (book_conversion_denote (book_henkin_full_signature \<Sigma> G) G)
    (book_conversion_valuation M)
    (book_conversion_logical_value (book_henkin_full_signature \<Sigma> G) G)"
proof -
  let ?\<Omega> = "book_henkin_full_signature \<Sigma> G"
  let ?D = "book_conversion_domain ?\<Omega> G"
  let ?app = "book_conversion_app ?\<Omega> G"
  let ?J = "book_conversion_denote ?\<Omega> G"
  let ?V = "book_conversion_valuation M"
  let ?k = "book_conversion_logical_value ?\<Omega> G"
  interpret Book: book_full_environment ?D ?app book_minimal_logical_type UNIV ?\<Omega> G ?J
    by (rule book_conversion_full_environment)
  have logicals: "Book.book_closed_value (book_minimal_logical_type l) (NLogical l) (?k l)" for l
    by (rule book_henkin_conversion_logical_closed_value[OF rich])
  show ?thesis
  proof (unfold book_full_minimal_model_def,
      rule conjI[OF Book.book_full_environment_axioms], unfold_locales)
    fix l
    show "Book.book_closed_value (book_minimal_logical_type l) (NLogical l) (?k l)"
      by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> ?D Prop" and qm: "q \<in> ?D Prop"
    show "?V (?app Prop Prop (?app Prop (Arr Prop Prop) (?k SImp) p) q) =
      (?V p \<longrightarrow> ?V q)"
      by (rule book_conversion_implication_truth[OF rich maximal pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> ?D (Arr \<sigma> Prop)"
    show "?V (?app (Arr \<sigma> Prop) Prop (?k (SBAll \<sigma>)) f) =
      (\<forall>a\<in>?D \<sigma>. ?V (?app \<sigma> Prop f a))"
      by (rule book_conversion_forall_truth[OF rich maximal witnesses fm])
  next
    show "\<exists>f\<in>?D Prop. \<not> ?V f"
      by (rule book_conversion_false_exists[OF rich maximal])
  qed
qed

end
