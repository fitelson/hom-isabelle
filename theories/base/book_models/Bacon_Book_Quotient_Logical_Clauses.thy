theory Bacon_Book_Quotient_Logical_Clauses
  imports Bacon_Book_Quotient_Separation
begin

section \<open>Operation-level implication and universal truth pass to the quotient\<close>

text \<open>
  If a typed operation κ has the original implication or universal
  quantifier truth clause, its class [κ] has the same clause with
  quotient application and valuation. Every quotient argument is an
  original class, so the universal clause ranges over all and only
  original predicate tests. Source role: the corresponding clauses of
  Bacon's Definition 15.1, pp.314–315, in the Proposition 15.5 quotient.

  Status: κ is a typed semantic value with an explicitly assumed truth
  law, not yet a named logical constant's proved denotation. The full
  environment, rich stock and given typed assignment supply application
  compatibility and valuation projection. No original separation,
  Functionality, false proposition, or new logical-model premise is added.
\<close>

context book_full_environment
begin

lemma book_quotient_predicate_class_value:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and predicate: "P \<in> domain (Arr \<sigma> Prop)" and argument: "a \<in> domain \<sigma>"
  shows "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) P)
      (book_leibniz_class domain app V \<sigma> a)) = V (app \<sigma> Prop P a)"
proof -
  have projection: "book_leibniz_quotient_app domain app V \<sigma> Prop
    (book_leibniz_class domain app V (Arr \<sigma> Prop) P)
    (book_leibniz_class domain app V \<sigma> a) =
    book_leibniz_class domain app V Prop (app \<sigma> Prop P a)"
    by (rule book_leibniz_quotient_application_projection[OF rich typed predicate argument])
  have result_type: "app \<sigma> Prop P a \<in> domain Prop"
    by (rule app_type[OF predicate argument])
  show ?thesis by (simp only: projection;
    rule book_leibniz_quotient_valuation_projection[OF rich typed result_type])
qed

lemma book_quotient_all_predicate_tests:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and predicate: "f \<in> domain (Arr \<sigma> Prop)"
  shows "(\<forall>X \<in> book_leibniz_quotient_domain domain app V \<sigma>.
    book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) f) X)) =
    (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
proof
  assume all_classes: "\<forall>X \<in> book_leibniz_quotient_domain domain app V \<sigma>.
    book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) f) X)"
  show "\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a)"
  proof (rule ballI)
    fix a
    assume member: "a \<in> domain \<sigma>"
    have class_member: "book_leibniz_class domain app V \<sigma> a \<in>
      book_leibniz_quotient_domain domain app V \<sigma>"
      by (rule book_leibniz_quotient_domainI[where D=domain and \<sigma>=\<sigma>, OF member])
    have class_truth: "book_leibniz_quotient_valuation V
      (book_leibniz_quotient_app domain app V \<sigma> Prop
        (book_leibniz_class domain app V (Arr \<sigma> Prop) f)
        (book_leibniz_class domain app V \<sigma> a))"
      by (rule bspec[OF all_classes class_member])
    show "V (app \<sigma> Prop f a)" using class_truth
      by (simp only: book_quotient_predicate_class_value[OF rich typed predicate member])
  qed
next
  assume all_original: "\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a)"
  show "\<forall>X \<in> book_leibniz_quotient_domain domain app V \<sigma>.
    book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) f) X)"
  proof (rule ballI)
    fix X
    assume member: "X \<in> book_leibniz_quotient_domain domain app V \<sigma>"
    obtain a where at: "a \<in> domain \<sigma>"
      and class_eq: "X = book_leibniz_class domain app V \<sigma> a"
      by (rule book_leibniz_quotient_domainE[OF member])
    have original_truth: "V (app \<sigma> Prop f a)" by (rule bspec[OF all_original at])
    show "book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop
      (book_leibniz_class domain app V (Arr \<sigma> Prop) f) X)"
      by (simp only: class_eq book_quotient_predicate_class_value[OF rich typed predicate at];
        rule original_truth)
  qed
qed

theorem book_quotient_implication_clause:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and operation: "k \<in> domain (Arr Prop (Arr Prop Prop))"
    and implication: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
    and left: "X \<in> book_leibniz_quotient_domain domain app V Prop"
    and right: "Y \<in> book_leibniz_quotient_domain domain app V Prop"
  shows "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V Prop Prop
      (book_leibniz_quotient_app domain app V Prop (Arr Prop Prop)
        (book_leibniz_class domain app V (Arr Prop (Arr Prop Prop)) k) X) Y) =
    (book_leibniz_quotient_valuation V X \<longrightarrow> book_leibniz_quotient_valuation V Y)"
proof -
  let ?x = "book_leibniz_rep X"
  let ?y = "book_leibniz_rep Y"
  have xt: "?x \<in> domain Prop" by (rule book_leibniz_rep_type[OF left])
  have yt: "?y \<in> domain Prop" by (rule book_leibniz_rep_type[OF right])
  have x_class: "book_leibniz_class domain app V Prop ?x = X"
    by (rule book_leibniz_rep_reconstruct[OF left])
  have y_class: "book_leibniz_class domain app V Prop ?y = Y"
    by (rule book_leibniz_rep_reconstruct[OF right])
  have first: "book_leibniz_quotient_app domain app V Prop (Arr Prop Prop)
    (book_leibniz_class domain app V (Arr Prop (Arr Prop Prop)) k) X =
    book_leibniz_class domain app V (Arr Prop Prop) (app Prop (Arr Prop Prop) k ?x)"
    using book_leibniz_quotient_application_projection[where V=V, OF rich typed operation xt]
    by (simp only: x_class)
  have partial_type: "app Prop (Arr Prop Prop) k ?x \<in> domain (Arr Prop Prop)"
    by (rule app_type[OF operation xt])
  have second: "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V Prop Prop
      (book_leibniz_class domain app V (Arr Prop Prop) (app Prop (Arr Prop Prop) k ?x)) Y) =
    V (app Prop Prop (app Prop (Arr Prop Prop) k ?x) ?y)"
    using book_quotient_predicate_class_value[where V=V, OF rich typed partial_type yt]
    by (simp only: y_class)
  have original: "V (app Prop Prop (app Prop (Arr Prop Prop) k ?x) ?y) = (V ?x \<longrightarrow> V ?y)"
    by (rule implication[OF xt yt])
  have right_values:
    "(book_leibniz_quotient_valuation V X \<longrightarrow> book_leibniz_quotient_valuation V Y) =
     (V ?x \<longrightarrow> V ?y)"
    by (simp only: book_leibniz_quotient_valuation_def)
  show ?thesis by (simp only: first second original right_values)
qed

theorem book_quotient_forall_clause:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and operation: "k \<in> domain (Arr (Arr \<sigma> Prop) Prop)"
    and universal: "\<And>f. f \<in> domain (Arr \<sigma> Prop) \<Longrightarrow>
      V (app (Arr \<sigma> Prop) Prop k f) = (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
    and predicate: "F \<in> book_leibniz_quotient_domain domain app V (Arr \<sigma> Prop)"
  shows "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V (Arr \<sigma> Prop) Prop
      (book_leibniz_class domain app V (Arr (Arr \<sigma> Prop) Prop) k) F) =
    (\<forall>X \<in> book_leibniz_quotient_domain domain app V \<sigma>.
      book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop F X))"
proof -
  obtain f where ft: "f \<in> domain (Arr \<sigma> Prop)"
    and class_eq: "F = book_leibniz_class domain app V (Arr \<sigma> Prop) f"
    by (rule book_leibniz_quotient_domainE[OF predicate])
  have applied_value: "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_app domain app V (Arr \<sigma> Prop) Prop
      (book_leibniz_class domain app V (Arr (Arr \<sigma> Prop) Prop) k) F) =
    V (app (Arr \<sigma> Prop) Prop k f)"
    by (simp only: class_eq; rule book_quotient_predicate_class_value[OF rich typed operation ft])
  have quantified:
    "(\<forall>X \<in> book_leibniz_quotient_domain domain app V \<sigma>.
      book_leibniz_quotient_valuation V (book_leibniz_quotient_app domain app V \<sigma> Prop F X)) =
     (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
    by (simp only: class_eq; rule book_quotient_all_predicate_tests[OF rich typed ft])
  show ?thesis by (simp only: applied_value quantified; rule universal[OF ft])
qed

lemma book_quotient_false_value:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and member: "p \<in> domain Prop" and falsehood: "\<not> V p"
  shows "\<exists>X \<in> book_leibniz_quotient_domain domain app V Prop.
    \<not> book_leibniz_quotient_valuation V X"
proof -
  have class_member: "book_leibniz_class domain app V Prop p \<in>
    book_leibniz_quotient_domain domain app V Prop"
    by (rule book_leibniz_quotient_domainI[where D=domain and \<sigma>=Prop, OF member])
  have class_false: "\<not> book_leibniz_quotient_valuation V (book_leibniz_class domain app V Prop p)"
    by (simp only: book_leibniz_quotient_valuation_projection[OF rich typed member]; rule falsehood)
  show ?thesis by (rule bexI[where x="book_leibniz_class domain app V Prop p"],
    rule class_false, rule class_member)
qed

end

end
