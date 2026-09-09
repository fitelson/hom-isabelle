theory Bacon_Book_Leibniz_Valuation
  imports Bacon_Book_Leibniz_Equivalence Bacon_Book_Identity_Predicate
begin

section \<open>Leibniz-equivalent propositions have equal valuations\<close>

text \<open>
  If a ≈ᴸᴱt b, every available unary predicate gives applications with
  the same valuation. Test with the denotation of λp:t.p to obtain
  V(a) = V(b). This is the valuation part of Bacon's Exercise 15.5,
  p.321, here proved for full book environments with an explicitly
  available typed assignment and rich variable stock.

  V is arbitrary and Boolean-valued: logical truth clauses are not needed
  for this implication. The premises do not identify a and b as objects;
  separation and the quotient construction remain different claims.
\<close>

lemma book_leibniz_valuation_from_identity:
  assumes equivalent: "book_leibniz_equiv D app V Prop a b"
    and identity_member: "i \<in> D (Arr Prop Prop)"
    and identity_action: "\<And>p. p \<in> D Prop \<Longrightarrow> app Prop Prop i p = p"
  shows "V a = V b"
proof -
  have test: "V (app Prop Prop i a) = V (app Prop Prop i b)"
    by (rule book_leibniz_test[where f=i, OF equivalent identity_member])
  have at: "app Prop Prop i a = a" by (rule identity_action[OF book_leibniz_left[OF equivalent]])
  have bt: "app Prop Prop i b = b" by (rule identity_action[OF book_leibniz_right[OF equivalent]])
  show ?thesis using test by (simp only: at bt)
qed

text \<open>
  When a negation operation has the required truth clause, it is already
  a sufficient test. This second proof needs no abstraction or environment
  condition, only the displayed typed negation value and valuation law.
  It is an algebraic consequence of the corresponding Definition 15.1
  clause; identifying that value with a defined logical denotation remains
  the responsibility of the logical-model construction.
\<close>

lemma book_leibniz_valuation_from_negation:
  assumes equivalent: "book_leibniz_equiv D app V Prop a b"
    and negation_member: "n \<in> D (Arr Prop Prop)"
    and negation_truth: "\<And>p. p \<in> D Prop \<Longrightarrow> V (app Prop Prop n p) = (\<not> V p)"
  shows "V a = V b"
proof -
  have test: "V (app Prop Prop n a) = V (app Prop Prop n b)"
    by (rule book_leibniz_test[where f=n, OF equivalent negation_member])
  have at: "V (app Prop Prop n a) = (\<not> V a)"
    by (rule negation_truth[OF book_leibniz_left[OF equivalent]])
  have bt: "V (app Prop Prop n b) = (\<not> V b)"
    by (rule negation_truth[OF book_leibniz_right[OF equivalent]])
  show ?thesis using test at bt by blast
qed

context book_full_environment
begin

theorem book_leibniz_valuation_invariant:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and equivalent: "book_leibniz_equiv domain app V Prop a b"
  shows "V a = V b"
proof -
  obtain i where member: "i \<in> domain (Arr Prop Prop)"
    and action: "\<forall>p \<in> domain Prop. app Prop Prop i p = p"
    using book_identity_operation_exists[where \<sigma>=Prop, OF rich typed] by (elim bexE)
  show ?thesis
  proof (rule book_leibniz_valuation_from_identity[OF equivalent member])
    fix p
    assume pm: "p \<in> domain Prop"
    show "app Prop Prop i p = p" by (rule bspec[where x=p, OF action pm])
  qed
qed

end

end
