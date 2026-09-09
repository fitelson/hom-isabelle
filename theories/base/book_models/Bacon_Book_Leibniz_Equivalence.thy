theory Bacon_Book_Leibniz_Equivalence
  imports Bacon_Book_Applicative_Structure
begin

section \<open>Typed Leibniz equivalence as agreement on every predicate test\<close>

text \<open>
  For a,b ∈ Dσ, define a ≈ᴸᴱσ b when every f ∈ Dσ→t satisfies
  V(Appσt(f,a)) = V(Appσt(f,b)). Source: Bacon, Definition 15.5, p.321.
  With Boolean-valued V, this is exactly agreement on whether each
  predicate application is true.

  Isabelle representation. The relation includes both domain-membership
  guards. Its set form is therefore an equivalence relation on Dσ, not
  an assertion of reflexivity on the entire ambient HOL carrier. Empty
  domains and a vacuous predicate-test family cause no difficulty for
  these elementary results. Neither separation, Functionality, domain
  nonemptiness, application congruence, nor valuation invariance is assumed.
  The latter two are separate obligations from Exercise 15.5. No BBK,
  H/C calculus, old general-model locale, or quotient is used here.
\<close>

definition book_leibniz_equiv ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> (otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    ('v \<Rightarrow> bool) \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "book_leibniz_equiv D app V \<sigma> a b \<longleftrightarrow>
    a \<in> D \<sigma> \<and> b \<in> D \<sigma> \<and>
    (\<forall>f \<in> D (Arr \<sigma> Prop). V (app \<sigma> Prop f a) = V (app \<sigma> Prop f b))"

lemma book_leibniz_equivI:
  assumes left: "a \<in> D \<sigma>" and right: "b \<in> D \<sigma>"
    and tests: "\<And>f. f \<in> D (Arr \<sigma> Prop) \<Longrightarrow> V (app \<sigma> Prop f a) = V (app \<sigma> Prop f b)"
  shows "book_leibniz_equiv D app V \<sigma> a b"
  unfolding book_leibniz_equiv_def
  by (rule conjI[OF left], rule conjI[OF right], intro ballI, rule tests, assumption)

lemma book_leibniz_left:
  "book_leibniz_equiv D app V \<sigma> a b \<Longrightarrow> a \<in> D \<sigma>"
  unfolding book_leibniz_equiv_def by (rule conjunct1)

lemma book_leibniz_right:
  assumes equivalent: "book_leibniz_equiv D app V \<sigma> a b"
  shows "b \<in> D \<sigma>"
  using equivalent unfolding book_leibniz_equiv_def by (rule conjunct1[OF conjunct2])

lemma book_leibniz_test:
  assumes equivalent: "book_leibniz_equiv D app V \<sigma> a b" and predicate: "f \<in> D (Arr \<sigma> Prop)"
  shows "V (app \<sigma> Prop f a) = V (app \<sigma> Prop f b)"
proof -
  have tests: "\<forall>f \<in> D (Arr \<sigma> Prop). V (app \<sigma> Prop f a) = V (app \<sigma> Prop f b)"
    using equivalent unfolding book_leibniz_equiv_def by (rule conjunct2[OF conjunct2])
  show ?thesis by (rule bspec[where x=f, OF tests predicate])
qed

lemma book_leibniz_refl:
  assumes member: "a \<in> D \<sigma>"
  shows "book_leibniz_equiv D app V \<sigma> a a"
  by (rule book_leibniz_equivI[where D=D and \<sigma>=\<sigma>, OF member member]) (rule refl)

lemma book_leibniz_sym:
  assumes equivalent: "book_leibniz_equiv D app V \<sigma> a b"
  shows "book_leibniz_equiv D app V \<sigma> b a"
proof (rule book_leibniz_equivI[where D=D and \<sigma>=\<sigma>, OF book_leibniz_right[OF equivalent] book_leibniz_left[OF equivalent]])
  fix f
  assume predicate: "f \<in> D (Arr \<sigma> Prop)"
  show "V (app \<sigma> Prop f b) = V (app \<sigma> Prop f a)"
    by (rule sym[OF book_leibniz_test[where f=f, OF equivalent predicate]])
qed

lemma book_leibniz_trans:
  assumes first: "book_leibniz_equiv D app V \<sigma> a b" and second: "book_leibniz_equiv D app V \<sigma> b c"
  shows "book_leibniz_equiv D app V \<sigma> a c"
proof (rule book_leibniz_equivI[where D=D and \<sigma>=\<sigma>, OF book_leibniz_left[OF first] book_leibniz_right[OF second]])
  fix f
  assume predicate: "f \<in> D (Arr \<sigma> Prop)"
  have ab: "V (app \<sigma> Prop f a) = V (app \<sigma> Prop f b)"
    by (rule book_leibniz_test[where f=f, OF first predicate])
  have bc: "V (app \<sigma> Prop f b) = V (app \<sigma> Prop f c)"
    by (rule book_leibniz_test[where f=f, OF second predicate])
  show "V (app \<sigma> Prop f a) = V (app \<sigma> Prop f c)" by (rule trans[OF ab bc])
qed

lemma book_leibniz_self_iff:
  "book_leibniz_equiv D app V \<sigma> a a \<longleftrightarrow> a \<in> D \<sigma>"
  by (rule iffI, rule book_leibniz_left, assumption, rule book_leibniz_refl, assumption)

definition book_leibniz_relation ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> (otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
    ('v \<Rightarrow> bool) \<Rightarrow> otype \<Rightarrow> ('v \<times> 'v) set" where
  "book_leibniz_relation D app V \<sigma> = {(a,b). book_leibniz_equiv D app V \<sigma> a b}"

lemma book_leibniz_relation_iff:
  "(a,b) \<in> book_leibniz_relation D app V \<sigma> \<longleftrightarrow> book_leibniz_equiv D app V \<sigma> a b"
  by (simp only: book_leibniz_relation_def mem_Collect_eq case_prod_conv)

theorem book_leibniz_equiv_on_domain:
  "equiv (D \<sigma>) (book_leibniz_relation D app V \<sigma>)"
proof (rule equivI)
  show "book_leibniz_relation D app V \<sigma> \<subseteq> D \<sigma> \<times> D \<sigma>"
    by (auto simp: book_leibniz_relation_def book_leibniz_equiv_def)
next
  show "refl_on (D \<sigma>) (book_leibniz_relation D app V \<sigma>)"
  proof (rule refl_onI)
    fix a
    assume member: "a \<in> D \<sigma>"
    show "(a,a) \<in> book_leibniz_relation D app V \<sigma>"
      by (simp only: book_leibniz_relation_iff; rule book_leibniz_refl[where D=D and \<sigma>=\<sigma>, OF member])
  qed
next
  show "sym (book_leibniz_relation D app V \<sigma>)"
  proof (rule symI)
    fix a b
    assume member: "(a,b) \<in> book_leibniz_relation D app V \<sigma>"
    have equivalent: "book_leibniz_equiv D app V \<sigma> a b" using member by (simp only: book_leibniz_relation_iff)
    show "(b,a) \<in> book_leibniz_relation D app V \<sigma>"
      by (simp only: book_leibniz_relation_iff; rule book_leibniz_sym[OF equivalent])
  qed
next
  show "trans (book_leibniz_relation D app V \<sigma>)"
  proof (rule transI)
    fix a b c
    assume ab: "(a,b) \<in> book_leibniz_relation D app V \<sigma>"
      and bc: "(b,c) \<in> book_leibniz_relation D app V \<sigma>"
    have first: "book_leibniz_equiv D app V \<sigma> a b" using ab by (simp only: book_leibniz_relation_iff)
    have second: "book_leibniz_equiv D app V \<sigma> b c" using bc by (simp only: book_leibniz_relation_iff)
    show "(a,c) \<in> book_leibniz_relation D app V \<sigma>"
      by (simp only: book_leibniz_relation_iff; rule book_leibniz_trans[OF first second])
  qed
qed

end
