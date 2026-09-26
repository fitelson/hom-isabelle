theory Bacon_Book_Lambda_I_Conversion_Model
  imports Bacon_Book_Lambda_I_Conversion_Closed_Values Bacon_Book_Lambda_I_Conversion_Universal_Valuation
    Bacon_Book_Lambda_I_Models
begin

section \<open>The constructed λI conversion classes form a λI model\<close>

text \<open>
  In the full λI witness signature Σ∞, take Dτ to be the internal
  conversion classes of closed λI terms of type τ, application to be
  application of representatives, J to be the constructed closed
  substitution denotation, v to be the characteristic valuation of M,
  and κ(l)=[l]type(l). If M is maximal closed-consistent for the λI
  calculus and closed constant-witness complete for λI predicates, these
  ACTUAL functions form a λI model in the sense of the independently
  defined model class (Definition 14.13 read through Proposition 9.1).

  The environment clause is the internal one: denotation is invariant
  under finite chains of β/η steps whose nodes are λI terms. Membership
  of the term model in the raw-invariant class is exactly the
  internalization theorem and is not claimed.
\<close>

theorem book_lambda_I_henkin_conversion_model:
  assumes rich: "sg_rich G"
    and maximal: "book_lambda_I_closed_maximal_extension (book_lambda_I_henkin_full_signature \<Sigma> G) G S M"
    and witnesses: "book_lambda_I_closed_constant_witness_complete (book_lambda_I_henkin_full_signature \<Sigma> G) G M"
  shows "book_lambda_I_model
    (book_lambda_I_conversion_domain (book_lambda_I_henkin_full_signature \<Sigma> G) G)
    (book_lambda_I_conversion_app (book_lambda_I_henkin_full_signature \<Sigma> G) G)
    (book_lambda_I_henkin_full_signature \<Sigma> G) G
    (book_lambda_I_conversion_denote (book_lambda_I_henkin_full_signature \<Sigma> G) G)
    (book_lambda_I_conversion_valuation M)
    (book_lambda_I_conversion_logical_value (book_lambda_I_henkin_full_signature \<Sigma> G) G)"
proof -
  let ?\<Omega> = "book_lambda_I_henkin_full_signature \<Sigma> G"
  show ?thesis
  proof (unfold_locales)
    fix \<sigma> \<tau> f a
    assume "f \<in> book_lambda_I_conversion_domain ?\<Omega> G (Arr \<sigma> \<tau>)"
      and "a \<in> book_lambda_I_conversion_domain ?\<Omega> G \<sigma>"
    then show "book_lambda_I_conversion_app ?\<Omega> G \<sigma> \<tau> f a \<in> book_lambda_I_conversion_domain ?\<Omega> G \<tau>"
      by (rule book_lambda_I_conversion_app_type)
  next
    fix A \<sigma> g
    assume "A \<in> book_LI ?\<Omega> G \<sigma>" and "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
    then show "book_lambda_I_conversion_denote ?\<Omega> G g A \<in> book_lambda_I_conversion_domain ?\<Omega> G \<sigma>"
      by (rule book_lambda_I_conversion_denote_type)
  next
    fix g n
    assume "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
    then show "book_lambda_I_conversion_denote ?\<Omega> G g (NVar n) = g n"
      by (rule book_lambda_I_conversion_denote_var)
  next
    fix F \<sigma> \<tau> A g
    assume "F \<in> book_LI ?\<Omega> G (Arr \<sigma> \<tau>)" and "A \<in> book_LI ?\<Omega> G \<sigma>"
      and "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
    then show "book_lambda_I_conversion_denote ?\<Omega> G g (NApp F A) =
      book_lambda_I_conversion_app ?\<Omega> G \<sigma> \<tau> (book_lambda_I_conversion_denote ?\<Omega> G g F)
        (book_lambda_I_conversion_denote ?\<Omega> G g A)"
      by (rule book_lambda_I_conversion_denote_app)
  next
    fix \<sigma> A B g h
    assume "book_lambda_I_conv ?\<Omega> G \<sigma> A B"
      and "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
      and "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G h"
      and "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
    then show "book_lambda_I_conversion_denote ?\<Omega> G g A = book_lambda_I_conversion_denote ?\<Omega> G h B"
      by (rule book_lambda_I_conversion_environment)
  next
    fix g l
    assume "book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
    show "book_lambda_I_conversion_denote ?\<Omega> G g (NLogical l) = book_lambda_I_conversion_logical_value ?\<Omega> G l"
      by (rule book_lambda_I_conversion_logical_denote)
  next
    show "\<exists>g. book_env_typed (book_lambda_I_conversion_domain ?\<Omega> G) G g"
      by (rule book_lambda_I_henkin_conversion_assignment_exists[OF rich])
  next
    fix p q
    assume pm: "p \<in> book_lambda_I_conversion_domain ?\<Omega> G Prop"
      and qm: "q \<in> book_lambda_I_conversion_domain ?\<Omega> G Prop"
    show "book_lambda_I_conversion_valuation M
      (book_lambda_I_conversion_app ?\<Omega> G Prop Prop
        (book_lambda_I_conversion_app ?\<Omega> G Prop (Arr Prop Prop)
          (book_lambda_I_conversion_logical_value ?\<Omega> G SImp) p) q) =
      (book_lambda_I_conversion_valuation M p \<longrightarrow> book_lambda_I_conversion_valuation M q)"
      by (rule book_lambda_I_conversion_implication_truth[OF rich maximal pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> book_lambda_I_conversion_domain ?\<Omega> G (Arr \<sigma> Prop)"
    show "book_lambda_I_conversion_valuation M
      (book_lambda_I_conversion_app ?\<Omega> G (Arr \<sigma> Prop) Prop
        (book_lambda_I_conversion_logical_value ?\<Omega> G (SBAll \<sigma>)) f) =
      (\<forall>a\<in>book_lambda_I_conversion_domain ?\<Omega> G \<sigma>.
        book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app ?\<Omega> G \<sigma> Prop f a))"
      by (rule book_lambda_I_conversion_forall_truth[OF rich maximal witnesses fm])
  next
    show "\<exists>f\<in>book_lambda_I_conversion_domain ?\<Omega> G Prop. \<not> book_lambda_I_conversion_valuation M f"
      by (rule book_lambda_I_conversion_false_exists[OF rich maximal])
  qed
qed

end
