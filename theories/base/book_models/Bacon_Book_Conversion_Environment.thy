theory Bacon_Book_Conversion_Environment
  imports Bacon_Book_Conversion_Denotation
    Bacon_Book_Environment_Substitution_Conversion
    Bacon_Book_Environment_Equivalence Bacon_Book_Full_Environment
begin

section \<open>The conversion classes form an actual interpretation\<close>

text \<open>
  Dτ consists of βη classes of closed Σ-terms, App([F],[A])=[FA],
  and Jg(A)=[A[rep∘g]]. Closed substitution preserves every contextual
  β/η step and the typing of its intermediate terms. Consequently J
  respects raw typed βη conversion at each typed assignment.

  Source role: the quotient permitted on p.320 and the interpretation
  on p.321, checked against Definition 14.13, p.302. We use the proved
  equivalence of its intersection condition with locality plus conversion.
  No model, consistency, Functionality or domain-nonemptiness premise is
  assumed. Empty domains remain possible at an arbitrary signature; the
  Henkin-signature inhabitation result is separate. Valuation and its
  universal-quantifier clause are not part of this interpretation theorem.
\<close>

theorem book_conversion_denote_conversion:
  assumes al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and typed: "book_env_typed (book_conversion_domain \<Sigma> G) G g"
  shows "book_conversion_denote \<Sigma> G g A = book_conversion_denote \<Sigma> G g B"
proof -
  have substituted: "named_raw_beta_eta book_minimal_logical_type G \<tau>
      (book_environment_subst {} (book_conversion_representatives g) A)
      (book_environment_subst {} (book_conversion_representatives g) B)"
    by (rule book_environment_subst_raw_conversion[OF _ _ conversion];
        rule book_conversion_representatives_closed[OF typed]
          book_conversion_representatives_type[OF typed])
  show ?thesis
    by (simp only: book_conversion_denote_eq[OF book_language_type[OF al]]
        book_conversion_denote_eq[OF book_language_type[OF bl]];
        rule book_conversion_class_eq[OF substituted])
qed

theorem book_conversion_separated_environment:
  "book_environment_separated (book_conversion_domain \<Sigma> G)
    (book_conversion_app \<Sigma> G) book_minimal_logical_type UNIV \<Sigma> G UNIV
    (book_conversion_denote \<Sigma> G)"
  apply unfold_locales
       apply (rule book_conversion_app_type; assumption)
      apply (rule book_conversion_denote_type; assumption)
     apply (rule book_conversion_denote_var; assumption)
    apply (rule book_conversion_denote_app; assumption)
   apply (rule book_conversion_denote_locality; assumption)
  apply (rule book_conversion_denote_conversion; assumption)
  done

theorem book_conversion_full_environment:
  "book_full_environment (book_conversion_domain \<Sigma> G)
    (book_conversion_app \<Sigma> G) book_minimal_logical_type UNIV \<Sigma> G
    (book_conversion_denote \<Sigma> G)"
proof -
  interpret Sep: book_environment_separated "book_conversion_domain \<Sigma> G"
    "book_conversion_app \<Sigma> G" book_minimal_logical_type UNIV \<Sigma> G UNIV
    "book_conversion_denote \<Sigma> G"
    by (rule book_conversion_separated_environment)
  interpret Env: book_environment_conditions "book_conversion_domain \<Sigma> G"
    "book_conversion_app \<Sigma> G" book_minimal_logical_type UNIV \<Sigma> G UNIV
    "book_conversion_denote \<Sigma> G"
    by (rule Sep.book_separated_to_environment)
  show ?thesis by unfold_locales
qed

end
