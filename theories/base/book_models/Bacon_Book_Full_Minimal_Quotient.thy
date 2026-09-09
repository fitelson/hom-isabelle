theory Bacon_Book_Full_Minimal_Quotient
  imports Bacon_Book_Full_Minimal_Model Bacon_Book_Quotient_Environment
    Bacon_Book_Quotient_Logical_Clauses
begin

section \<open>The quotient is again a full-language minimal-basis model\<close>

text \<open>
  Replace Dσ by Dσ/≈ᴸᴱσ, application by its quotient, valuation by
  V̄([p]) = V(p), and each logical value κ(l) by [κ(l)]. The quotient
  interpretation supplies those closed logical values and satisfies the
  environment condition. Implication, universal quantification, and the
  required false proposition pass to this same quotient.

  Source role: assembling the full-language, minimal-basis case of
  Bacon's Proposition 15.5, p.322. All fields of the qualified
  book_full_minimal_model are verified, rather than merely assuming
  that a typed quotient structure is a logical model. This does not
  settle the arbitrary general-language/partial-signature scope or
  remove the explicitly witnessed closed-value convention.
\<close>

context book_full_minimal_model
begin

theorem book_full_minimal_quotient_model:
  assumes rich: "sg_rich stock"
  shows "book_full_minimal_model (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) signature stock
    (book_leibniz_quotient_denote V) (book_leibniz_quotient_valuation V)
    (\<lambda>l. book_leibniz_class domain app V (book_minimal_logical_type l) (\<kappa> l))"
proof -
  let ?D = "book_leibniz_quotient_domain domain app V"
  let ?App = "book_leibniz_quotient_app domain app V"
  let ?J = "book_leibniz_quotient_denote V"
  let ?Val = "book_leibniz_quotient_valuation V"
  let ?K = "\<lambda>l. book_leibniz_class domain app V (book_minimal_logical_type l) (\<kappa> l)"
  obtain g0 where gt: "book_env_typed domain stock g0"
    using book_minimal_assignment_exists by (elim exE)
  interpret Q: book_full_environment ?D ?App book_minimal_logical_type UNIV signature stock ?J
    by (rule book_leibniz_quotient_environment[OF rich gt])
  let ?q0 = "\<lambda>n. book_leibniz_class domain app V (stock n) (g0 n)"
  have qt: "book_env_typed ?D stock ?q0"
  proof (unfold book_env_typed_def, rule allI)
    fix n
    have member: "g0 n \<in> domain (stock n)" by (rule book_env_at[where n=n, OF gt])
    show "book_leibniz_class domain app V (stock n) (g0 n) \<in> ?D (stock n)"
      by (rule book_leibniz_quotient_domainI[where D=domain and \<sigma>="stock n", OF member])
  qed
  have lifted: "book_env_typed domain stock (book_leibniz_lift_assignment ?q0)"
    by (rule book_leibniz_lift_assignment_typed[OF qt])
  have logicals: "Q.book_closed_value (book_minimal_logical_type l) (NLogical l) (?K l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV signature stock
      (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have original: "denote (book_leibniz_lift_assignment ?q0) (NLogical l) = \<kappa> l"
      by (rule book_minimal_logical_value_at[OF lifted])
    have projected: "?J ?q0 (NLogical l) = ?K l"
      by (simp only: book_leibniz_quotient_denote_eq[OF language] original)
    have witnessed: "Q.book_closed_value (book_minimal_logical_type l) (NLogical l) (?J ?q0 (NLogical l))"
      by (rule Q.book_closed_value_intro[OF UNIV_I language closed qt])
    show ?thesis using witnessed by (simp only: projected)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def, rule conjI[OF Q.book_full_environment_axioms], unfold_locales)
    fix l
    show "Q.book_closed_value (book_minimal_logical_type l) (NLogical l) (?K l)"
      by (rule logicals)
  next
    fix X Y
    assume xm: "X \<in> ?D Prop" and ym: "Y \<in> ?D Prop"
    show "?Val (?App Prop Prop (?App Prop (Arr Prop Prop) (?K SImp) X) Y) = (?Val X \<longrightarrow> ?Val Y)"
      by (simp only: book_minimal_logical_type.simps;
        rule book_quotient_implication_clause[OF rich gt book_minimal_implication_value_type implication_truth xm ym])
  next
    fix \<sigma> F
    assume fm: "F \<in> ?D (Arr \<sigma> Prop)"
    show "?Val (?App (Arr \<sigma> Prop) Prop (?K (SBAll \<sigma>)) F) =
      (\<forall>A \<in> ?D \<sigma>. ?Val (?App \<sigma> Prop F A))"
      by (simp only: book_minimal_logical_type.simps;
        rule book_quotient_forall_clause[OF rich gt book_minimal_forall_value_type forall_truth fm])
  next
    obtain p where pm: "p \<in> domain Prop" and pf: "\<not> V p"
      using false_proposition by (elim bexE)
    show "\<exists>X \<in> ?D Prop. \<not> ?Val X" by (rule book_quotient_false_value[where V=V, OF rich gt pm pf])
  qed
qed

end

end
