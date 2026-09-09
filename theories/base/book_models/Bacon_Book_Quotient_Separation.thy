theory Bacon_Book_Quotient_Separation
  imports Bacon_Book_Quotient_Valuation
begin

section \<open>Predicate tests separate distinct quotient classes\<close>

text \<open>
  Each original predicate P yields the quotient predicate [P]σ→t.
  Its truth on a quotient class X is V(Appσt(P,rep X)). Thus
  Leibniz-equivalence of quotient values forces equivalence of their
  representatives, and hence equality of the classes.
  Source role: Leibnizian separation in Definition 15.6 and
  Proposition 15.5, p.322.

  Status: this is quotient algebra. Application compatibility and
  proposition-valuation invariance are explicit in the general lemmas;
  the full-environment theorem proves both from its stated premises.
  No original separation, Functionality, new PER, or logical-model
  interpretation/valuation clauses are assumed or assembled.
\<close>

context book_applicative_structure
begin

lemma book_leibniz_quotient_test_projection:
  assumes predicate: "P \<in> domain (Arr \<sigma> Prop)"
    and argument: "X \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    and compatible: "\<And>f h a b.
      book_leibniz_equiv domain app V (Arr \<sigma> Prop) f h \<Longrightarrow>
      book_leibniz_equiv domain app V \<sigma> a b \<Longrightarrow>
      book_leibniz_equiv domain app V Prop (app \<sigma> Prop f a) (app \<sigma> Prop h b)"
    and invariant: "\<And>p q. book_leibniz_equiv domain app V Prop p q \<Longrightarrow> V p = V q"
  shows "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) P) X) =
    V (app \<sigma> Prop P (book_leibniz_rep X))"
proof -
  have xt: "book_leibniz_rep X \<in> domain \<sigma>" by (rule book_leibniz_rep_type[OF argument])
  have reconstruction: "book_leibniz_class domain app V \<sigma> (book_leibniz_rep X) = X"
    by (rule book_leibniz_rep_reconstruct[OF argument])
  have application: "book_leibniz_quotient_app domain app V \<sigma> Prop
    (book_leibniz_class domain app V (Arr \<sigma> Prop) P) X =
    book_leibniz_class domain app V Prop (app \<sigma> Prop P (book_leibniz_rep X))"
    using book_leibniz_quotient_projection_from_congruence[OF predicate xt compatible]
    by (simp only: reconstruction)
  have result_type: "app \<sigma> Prop P (book_leibniz_rep X) \<in> domain Prop"
    by (rule app_type[OF predicate xt])
  show ?thesis by (simp only: application;
    rule book_leibniz_quotient_valuation_class[where D=domain, OF result_type invariant])
qed

theorem book_leibniz_quotient_separation_from_conditions:
  assumes left: "X \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    and right: "Y \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    and compatible: "\<And>f h a b.
      book_leibniz_equiv domain app V (Arr \<sigma> Prop) f h \<Longrightarrow>
      book_leibniz_equiv domain app V \<sigma> a b \<Longrightarrow>
      book_leibniz_equiv domain app V Prop (app \<sigma> Prop f a) (app \<sigma> Prop h b)"
    and invariant: "\<And>p q. book_leibniz_equiv domain app V Prop p q \<Longrightarrow> V p = V q"
  shows "book_leibniz_equiv (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V) \<sigma> X Y
    \<longleftrightarrow> X = Y"
proof
  let ?Q = "book_leibniz_quotient_domain domain app V"
  let ?App = "book_leibniz_quotient_app domain app V"
  let ?Val = "book_leibniz_quotient_valuation V"
  assume quotient_equiv: "book_leibniz_equiv ?Q ?App ?Val \<sigma> X Y"
  have xt: "book_leibniz_rep X \<in> domain \<sigma>" by (rule book_leibniz_rep_type[OF left])
  have yt: "book_leibniz_rep Y \<in> domain \<sigma>" by (rule book_leibniz_rep_type[OF right])
  have original_equiv: "book_leibniz_equiv domain app V \<sigma> (book_leibniz_rep X) (book_leibniz_rep Y)"
  proof (rule book_leibniz_equivI[where D=domain and \<sigma>=\<sigma>, OF xt yt])
    fix P
    assume predicate: "P \<in> domain (Arr \<sigma> Prop)"
    let ?C = "book_leibniz_class domain app V (Arr \<sigma> Prop) P"
    have quotient_predicate: "?C \<in> ?Q (Arr \<sigma> Prop)"
      by (rule book_leibniz_quotient_domainI[where D=domain and \<sigma>="Arr \<sigma> Prop", OF predicate])
    have test: "?Val (?App \<sigma> Prop ?C X) = ?Val (?App \<sigma> Prop ?C Y)"
      by (rule book_leibniz_test[where f="?C", OF quotient_equiv quotient_predicate])
    have left_value: "?Val (?App \<sigma> Prop ?C X) = V (app \<sigma> Prop P (book_leibniz_rep X))"
      by (rule book_leibniz_quotient_test_projection[OF predicate left compatible invariant])
    have right_value: "?Val (?App \<sigma> Prop ?C Y) = V (app \<sigma> Prop P (book_leibniz_rep Y))"
      by (rule book_leibniz_quotient_test_projection[OF predicate right compatible invariant])
    show "V (app \<sigma> Prop P (book_leibniz_rep X)) = V (app \<sigma> Prop P (book_leibniz_rep Y))"
      using test by (simp only: left_value right_value)
  qed
  have classes: "book_leibniz_class domain app V \<sigma> (book_leibniz_rep X) =
    book_leibniz_class domain app V \<sigma> (book_leibniz_rep Y)"
    by (rule book_leibniz_class_eq[OF original_equiv])
  show "X = Y" using classes
    by (simp only: book_leibniz_rep_reconstruct[OF left] book_leibniz_rep_reconstruct[OF right])
next
  assume equal: "X = Y"
  show "book_leibniz_equiv (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V) \<sigma> X Y"
    using book_leibniz_refl[where D="book_leibniz_quotient_domain domain app V"
      and app="book_leibniz_quotient_app domain app V" and V="book_leibniz_quotient_valuation V"
      and \<sigma>=\<sigma>, OF left] by (simp only: equal)
qed

end

context book_full_environment
begin

theorem book_leibniz_quotient_separation:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and left: "X \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    and right: "Y \<in> book_leibniz_quotient_domain domain app V \<sigma>"
  shows "book_leibniz_equiv (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) (book_leibniz_quotient_valuation V) \<sigma> X Y
    \<longleftrightarrow> X = Y"
proof (rule book_leibniz_quotient_separation_from_conditions[OF left right])
  fix f h a b
  assume heads: "book_leibniz_equiv domain app V (Arr \<sigma> Prop) f h"
    and arguments: "book_leibniz_equiv domain app V \<sigma> a b"
  show "book_leibniz_equiv domain app V Prop (app \<sigma> Prop f a) (app \<sigma> Prop h b)"
    by (rule book_leibniz_application_cong[OF rich typed heads arguments])
next
  fix p q
  assume equivalent: "book_leibniz_equiv domain app V Prop p q"
  show "V p = V q" by (rule book_leibniz_valuation_invariant[OF rich typed equivalent])
qed

end

end
