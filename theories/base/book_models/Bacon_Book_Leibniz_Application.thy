theory Bacon_Book_Leibniz_Application
  imports Bacon_Book_Leibniz_Application_Tests
    Bacon_Book_Argument_Test Bacon_Book_Head_Test
begin

section \<open>Application respects Leibniz equivalence in full environments\<close>

text \<open>
  If F ≈ᴸᴱσ→τ G and a ≈ᴸᴱσ b, then Fa ≈ᴸᴱτ Gb.
  The two λ-defined testing predicates transfer a test on the result
  to a test on either the head or the argument of the application.

  Source: the congruence part of Bacon's Exercise 15.5, p.321.
  This proof supplies the full-language case with a rich variable stock
  and a given typed assignment. It does not silently replace the book's
  general 𝒥(Σ) by full grammar: supplying the tests in the more general
  source setting remains a separate language obligation. No Functionality,
  separation, logical valuation law, or quotient is assumed.
\<close>

context book_full_environment
begin

theorem book_leibniz_argument_cong:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and equivalent: "book_leibniz_equiv domain app V \<sigma> a b"
    and operation: "f \<in> domain (Arr \<sigma> \<tau>)"
  shows "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> f b)"
proof (rule book_leibniz_argument_from_tests[OF equivalent operation])
  fix P
  assume predicate: "P \<in> domain (Arr \<tau> Prop)"
  obtain h where hm: "h \<in> domain (Arr \<sigma> Prop)"
    and action: "\<forall>x \<in> domain \<sigma>. app \<sigma> Prop h x = app \<tau> Prop P (app \<sigma> \<tau> f x)"
    using book_argument_test_exists[OF rich typed operation predicate] by (elim bexE)
  show "\<exists>h \<in> domain (Arr \<sigma> Prop). \<forall>x \<in> domain \<sigma>.
    V (app \<sigma> Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> f x))"
  proof (rule bexI[where x=h])
    show "\<forall>x \<in> domain \<sigma>. V (app \<sigma> Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> f x))"
      using action by simp
    show "h \<in> domain (Arr \<sigma> Prop)" by (rule hm)
  qed
qed

theorem book_leibniz_head_cong:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock k"
    and equivalent: "book_leibniz_equiv domain app V (Arr \<sigma> \<tau>) f g"
    and argument: "a \<in> domain \<sigma>"
  shows "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g a)"
proof (rule book_leibniz_head_from_tests[OF equivalent argument])
  fix P
  assume predicate: "P \<in> domain (Arr \<tau> Prop)"
  obtain h where hm: "h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop)"
    and action: "\<forall>x \<in> domain (Arr \<sigma> \<tau>).
      app (Arr \<sigma> \<tau>) Prop h x = app \<tau> Prop P (app \<sigma> \<tau> x a)"
    using book_head_test_exists[OF rich typed argument predicate] by (elim bexE)
  show "\<exists>h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop). \<forall>x \<in> domain (Arr \<sigma> \<tau>).
    V (app (Arr \<sigma> \<tau>) Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> x a))"
  proof (rule bexI[where x=h])
    show "\<forall>x \<in> domain (Arr \<sigma> \<tau>).
      V (app (Arr \<sigma> \<tau>) Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> x a))"
      using action by simp
    show "h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop)" by (rule hm)
  qed
qed

theorem book_leibniz_application_cong:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock k"
    and heads: "book_leibniz_equiv domain app V (Arr \<sigma> \<tau>) f g"
    and arguments: "book_leibniz_equiv domain app V \<sigma> a b"
  shows "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g b)"
proof -
  have first: "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g a)"
    by (rule book_leibniz_head_cong[OF rich typed heads book_leibniz_left[OF arguments]])
  have second: "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> g a) (app \<sigma> \<tau> g b)"
    by (rule book_leibniz_argument_cong[OF rich typed arguments book_leibniz_right[OF heads]])
  show ?thesis by (rule book_leibniz_trans[OF first second])
qed

end

end
