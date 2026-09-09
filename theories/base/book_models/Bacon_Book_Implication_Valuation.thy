theory Bacon_Book_Implication_Valuation
  imports Bacon_Book_Leibniz_Equivalence
begin

section \<open>Material implication supplies a valuation-preserving predicate\<close>

text \<open>
  Let k have the type and truth behaviour of implication. From a false
  proposition f, form t = (k f) f and i = k t. Then t is true and
  V(i p) = V(p) for every proposition p. Hence Leibniz-equivalent
  propositions have the same valuation. Source: the implication and
  false-point clauses of Definition 15.1, pp.314–315, and Exercise 15.5,
  p.321, in Bacon's book.

  Representation. Only typed application is used. The truth-test actually
  needs just one proposition, since p→p is true regardless of V(p).
  Falsity is used below to certify that the constructed true point is
  distinct from the supplied false point. The predicate i preserves
  valuation; it is not asserted to be a denotational identity operation.
  No λ interpretation, total assignment, full environment, separation,
  global nonemptiness, or new logical-model locale is assumed.
\<close>

context book_applicative_structure
begin

lemma book_implication_true_point:
  fixes V :: "'v \<Rightarrow> bool"
  assumes implication: "k \<in> domain (Arr Prop (Arr Prop Prop))" and point: "f \<in> domain Prop"
    and material: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
  shows "app Prop Prop (app Prop (Arr Prop Prop) k f) f \<in> domain Prop \<and>
    V (app Prop Prop (app Prop (Arr Prop Prop) k f) f)"
proof -
  have partial: "app Prop (Arr Prop Prop) k f \<in> domain (Arr Prop Prop)"
    by (rule app_type[where \<sigma>=Prop and \<tau>="Arr Prop Prop", OF implication point])
  have typed: "app Prop Prop (app Prop (Arr Prop Prop) k f) f \<in> domain Prop"
    by (rule app_type[where \<sigma>=Prop and \<tau>=Prop, OF partial point])
  have truth: "V (app Prop Prop (app Prop (Arr Prop Prop) k f) f)"
    using material[OF point point] by simp
  show ?thesis by (rule conjI[OF typed truth])
qed

lemma book_implication_true_test:
  fixes V :: "'v \<Rightarrow> bool"
  assumes implication: "k \<in> domain (Arr Prop (Arr Prop Prop))"
    and truth_type: "t \<in> domain Prop" and truth: "V t"
    and material: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
  shows "app Prop (Arr Prop Prop) k t \<in> domain (Arr Prop Prop) \<and>
    (\<forall>p \<in> domain Prop. V (app Prop Prop (app Prop (Arr Prop Prop) k t) p) = V p)"
proof -
  have typed: "app Prop (Arr Prop Prop) k t \<in> domain (Arr Prop Prop)"
    by (rule app_type[where \<sigma>=Prop and \<tau>="Arr Prop Prop", OF implication truth_type])
  have test: "V (app Prop Prop (app Prop (Arr Prop Prop) k t) p) = V p" if pt: "p \<in> domain Prop" for p
    using material[OF truth_type pt] truth by simp
  show ?thesis by (rule conjI[OF typed], intro ballI, rule test, assumption)
qed

lemma book_implication_truth_test:
  fixes V :: "'v \<Rightarrow> bool"
  assumes implication: "k \<in> domain (Arr Prop (Arr Prop Prop))" and point: "f \<in> domain Prop"
    and material: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
  obtains i where "i \<in> domain (Arr Prop Prop)" and "\<And>p. p \<in> domain Prop \<Longrightarrow> V (app Prop Prop i p) = V p"
proof -
  let ?t = "app Prop Prop (app Prop (Arr Prop Prop) k f) f"
  let ?i = "app Prop (Arr Prop Prop) k ?t"
  have t: "?t \<in> domain Prop \<and> V ?t" by (rule book_implication_true_point[OF implication point material])
  have i: "?i \<in> domain (Arr Prop Prop) \<and> (\<forall>p \<in> domain Prop. V (app Prop Prop ?i p) = V p)"
    by (rule book_implication_true_test[OF implication conjunct1[OF t] conjunct2[OF t] material])
  have tests: "\<And>p. p \<in> domain Prop \<Longrightarrow> V (app Prop Prop ?i p) = V p"
    by (rule bspec[OF conjunct2[OF i]], assumption)
  show thesis by (rule that[OF conjunct1[OF i] tests])
qed

theorem book_implication_false_point_witnesses:
  fixes V :: "'v \<Rightarrow> bool"
  assumes implication: "k \<in> domain (Arr Prop (Arr Prop Prop))"
    and point: "f \<in> domain Prop" and false_point: "\<not> V f"
    and material: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
  shows "\<exists>t i. t = app Prop Prop (app Prop (Arr Prop Prop) k f) f \<and>
    i = app Prop (Arr Prop Prop) k t \<and> t \<in> domain Prop \<and> V t \<and> t \<noteq> f \<and>
    i \<in> domain (Arr Prop Prop) \<and> (\<forall>p \<in> domain Prop. V (app Prop Prop i p) = V p)"
proof -
  let ?t = "app Prop Prop (app Prop (Arr Prop Prop) k f) f"
  let ?i = "app Prop (Arr Prop Prop) k ?t"
  have t: "?t \<in> domain Prop \<and> V ?t" by (rule book_implication_true_point[OF implication point material])
  have distinct: "?t \<noteq> f" using conjunct2[OF t] false_point by auto
  have i: "?i \<in> domain (Arr Prop Prop) \<and> (\<forall>p \<in> domain Prop. V (app Prop Prop ?i p) = V p)"
    by (rule book_implication_true_test[OF implication conjunct1[OF t] conjunct2[OF t] material])
  show ?thesis by (rule exI[where x="?t"], rule exI[where x="?i"],
    rule conjI[OF refl], rule conjI[OF refl], rule conjI[OF conjunct1[OF t]],
    rule conjI[OF conjunct2[OF t]], rule conjI[OF distinct], rule i)
qed

theorem book_leibniz_valuation_from_implication:
  fixes V :: "'v \<Rightarrow> bool"
  assumes implication: "k \<in> domain (Arr Prop (Arr Prop Prop))"
    and material: "\<And>p q. p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      V (app Prop Prop (app Prop (Arr Prop Prop) k p) q) = (V p \<longrightarrow> V q)"
    and equivalent: "book_leibniz_equiv domain app V Prop a b"
  shows "V a = V b"
proof -
  have at: "a \<in> domain Prop" by (rule book_leibniz_left[OF equivalent])
  have bt: "b \<in> domain Prop" by (rule book_leibniz_right[OF equivalent])
  obtain i where it: "i \<in> domain (Arr Prop Prop)"
    and test: "\<And>p. p \<in> domain Prop \<Longrightarrow> V (app Prop Prop i p) = V p"
  proof -
    show thesis
    proof (rule book_implication_truth_test[OF implication at material])
      fix i
      assume im: "i \<in> domain (Arr Prop Prop)"
        and behavior: "\<And>p. p \<in> domain Prop \<Longrightarrow> V (app Prop Prop i p) = V p"
      show thesis by (rule that[OF im behavior])
    qed
  qed
  have same: "V (app Prop Prop i a) = V (app Prop Prop i b)"
    by (rule book_leibniz_test[where D=domain and app=app and V=V and \<sigma>=Prop and f=i, OF equivalent it])
  show ?thesis using same by (simp only: test[OF at] test[OF bt])
qed

end

end
