theory Bacon_Book_Leibniz_Application_Tests
  imports Bacon_Book_Leibniz_Equivalence
begin

section \<open>Testing predicates suffice for Leibniz application congruence\<close>

text \<open>
  To prove Fa ≈ᴸᴱτ Fb from a ≈ᴸᴱσ b, fix a predicate P:τ→t.
  A predicate on Dσ with the truth behaviour of λx.P(Fx) transfers
  the test back to a and b. For equivalent operations F,G, use instead
  a predicate with the truth behaviour of λX.P(Xa).

  These are the two testing steps in the congruence part of Bacon's
  Exercise 15.5, p.321. The present algebraic lemmas state the testing
  hypotheses explicitly. They do not assume them to hold in arbitrary
  applicative structures or general λ-languages. Separate denotation
  constructions will supply the tests where the relevant terms are
  interpreted. No Functionality, separation, or logical truth clause
  is used here.
\<close>

context book_applicative_structure
begin

lemma book_leibniz_argument_from_tests:
  assumes equivalent: "book_leibniz_equiv domain app V \<sigma> a b"
    and operation: "f \<in> domain (Arr \<sigma> \<tau>)"
    and tests: "\<And>P. P \<in> domain (Arr \<tau> Prop) \<Longrightarrow>
      \<exists>h \<in> domain (Arr \<sigma> Prop). \<forall>x \<in> domain \<sigma>.
        V (app \<sigma> Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> f x))"
  shows "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> f b)"
proof (rule book_leibniz_equivI)
  show "app \<sigma> \<tau> f a \<in> domain \<tau>"
    by (rule app_type[OF operation book_leibniz_left[OF equivalent]])
  show "app \<sigma> \<tau> f b \<in> domain \<tau>"
    by (rule app_type[OF operation book_leibniz_right[OF equivalent]])
  fix P
  assume predicate: "P \<in> domain (Arr \<tau> Prop)"
  obtain h where hm: "h \<in> domain (Arr \<sigma> Prop)"
    and behavior: "\<forall>x \<in> domain \<sigma>.
      V (app \<sigma> Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> f x))"
    using tests[OF predicate] by (elim bexE)
  have same: "V (app \<sigma> Prop h a) = V (app \<sigma> Prop h b)"
    by (rule book_leibniz_test[where f=h, OF equivalent hm])
  have at: "V (app \<sigma> Prop h a) = V (app \<tau> Prop P (app \<sigma> \<tau> f a))"
    by (rule bspec[where x=a, OF behavior book_leibniz_left[OF equivalent]])
  have bt: "V (app \<sigma> Prop h b) = V (app \<tau> Prop P (app \<sigma> \<tau> f b))"
    by (rule bspec[where x=b, OF behavior book_leibniz_right[OF equivalent]])
  show "V (app \<tau> Prop P (app \<sigma> \<tau> f a)) = V (app \<tau> Prop P (app \<sigma> \<tau> f b))"
    using same by (simp only: at bt)
qed

lemma book_leibniz_head_from_tests:
  assumes equivalent: "book_leibniz_equiv domain app V (Arr \<sigma> \<tau>) f g"
    and argument: "a \<in> domain \<sigma>"
    and tests: "\<And>P. P \<in> domain (Arr \<tau> Prop) \<Longrightarrow>
      \<exists>h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop). \<forall>x \<in> domain (Arr \<sigma> \<tau>).
        V (app (Arr \<sigma> \<tau>) Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> x a))"
  shows "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g a)"
proof (rule book_leibniz_equivI)
  show "app \<sigma> \<tau> f a \<in> domain \<tau>"
    by (rule app_type[OF book_leibniz_left[OF equivalent] argument])
  show "app \<sigma> \<tau> g a \<in> domain \<tau>"
    by (rule app_type[OF book_leibniz_right[OF equivalent] argument])
  fix P
  assume predicate: "P \<in> domain (Arr \<tau> Prop)"
  obtain h where hm: "h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop)"
    and behavior: "\<forall>x \<in> domain (Arr \<sigma> \<tau>).
      V (app (Arr \<sigma> \<tau>) Prop h x) = V (app \<tau> Prop P (app \<sigma> \<tau> x a))"
    using tests[OF predicate] by (elim bexE)
  have same: "V (app (Arr \<sigma> \<tau>) Prop h f) = V (app (Arr \<sigma> \<tau>) Prop h g)"
    by (rule book_leibniz_test[where f=h, OF equivalent hm])
  have ft: "V (app (Arr \<sigma> \<tau>) Prop h f) = V (app \<tau> Prop P (app \<sigma> \<tau> f a))"
    by (rule bspec[where x=f, OF behavior book_leibniz_left[OF equivalent]])
  have gt: "V (app (Arr \<sigma> \<tau>) Prop h g) = V (app \<tau> Prop P (app \<sigma> \<tau> g a))"
    by (rule bspec[where x=g, OF behavior book_leibniz_right[OF equivalent]])
  show "V (app \<tau> Prop P (app \<sigma> \<tau> f a)) = V (app \<tau> Prop P (app \<sigma> \<tau> g a))"
    using same by (simp only: ft gt)
qed

end

end
