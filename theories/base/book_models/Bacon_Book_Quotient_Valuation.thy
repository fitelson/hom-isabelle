theory Bacon_Book_Quotient_Valuation
  imports Bacon_Book_Quotient_Application Bacon_Book_Leibniz_Valuation
begin

section \<open>Valuation on typed Leibniz classes\<close>

text \<open>
  Define V̄(X) = V(rep X). For a ∈ Dt, valuation invariance under
  Leibniz equivalence gives V̄([a]t) = V(a). The representative of a
  legitimate class is typed and Leibniz-equivalent to its members;
  nothing is asserted about the representative of an empty off-domain set.
  Source role: the valuation part of Exercise 15.5, p.321, and the
  quotient in Proposition 15.5, p.322.

  Status: the first lemmas retain the precise valuation-invariance
  premise. The full-environment corollary discharges it using a rich
  stock and an explicitly given typed total assignment. No logical truth
  clause, original separation, Functionality or quotient model is assumed.
\<close>

definition book_leibniz_quotient_valuation :: "('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> bool" where
  "book_leibniz_quotient_valuation V X = V (book_leibniz_rep X)"

lemma book_leibniz_quotient_valuation_class:
  assumes member: "a \<in> D Prop"
    and invariant: "\<And>p q. book_leibniz_equiv D app V Prop p q \<Longrightarrow> V p = V q"
  shows "book_leibniz_quotient_valuation V (book_leibniz_class D app V Prop a) = V a"
proof -
  have related: "book_leibniz_equiv D app V Prop
    (book_leibniz_rep (book_leibniz_class D app V Prop a)) a"
    by (rule book_leibniz_rep_equiv[where D=D and \<sigma>=Prop, OF member])
  show ?thesis unfolding book_leibniz_quotient_valuation_def by (rule invariant[OF related])
qed

lemma book_leibniz_quotient_valuation_member:
  assumes quotient: "X \<in> book_leibniz_quotient_domain D app V Prop" and member: "a \<in> X"
    and invariant: "\<And>p q. book_leibniz_equiv D app V Prop p q \<Longrightarrow> V p = V q"
  shows "book_leibniz_quotient_valuation V X = V a"
proof -
  have related: "book_leibniz_equiv D app V Prop (book_leibniz_rep X) a"
    by (rule book_leibniz_quotient_rep_equiv[OF quotient member])
  show ?thesis unfolding book_leibniz_quotient_valuation_def by (rule invariant[OF related])
qed

context book_full_environment
begin

theorem book_leibniz_quotient_valuation_projection:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and member: "a \<in> domain Prop"
  shows "book_leibniz_quotient_valuation V (book_leibniz_class domain app V Prop a) = V a"
proof (rule book_leibniz_quotient_valuation_class[where D=domain, OF member])
  fix p q
  assume equivalent: "book_leibniz_equiv domain app V Prop p q"
  show "V p = V q" by (rule book_leibniz_valuation_invariant[OF rich typed equivalent])
qed

end

end
