theory Bacon_Book_Quotient_Truth
  imports Bacon_Book_Quotient_Environment Bacon_Book_Leibniz_Assignments Bacon_Book_Quotient_Valuation
begin

section \<open>Projecting assignments and preserving truth in the Leibniz quotient\<close>

text \<open>
  Project g pointwise by qg(n) = [g(n)]G(n). Then J̄qg(M) = [Jg(M)]τ
  for M:τ. For formulas, V̄(J̄qg(A)) = V(Jg(A)); every typed quotient
  assignment also lifts to an original assignment with that truth value.
  Source role: truth preservation in Bacon's Proposition 15.5, p.322,
  using Exercise 15.5, p.321, and the full environment specialization.

  Representation. A chosen representative of [g(n)] need not equal g(n),
  so projection uses the proved denotation invariance up to Leibniz
  equivalence, not an assumed equality of assignments. The following
  validity equivalence ranges over all typed total assignments. It applies
  also to open formulas but assumes the displayed language, full environment
  and rich stock. V is an arbitrary Boolean valuation: no logical truth
  clauses, separation, Functionality or completed logical model are used.
\<close>

definition book_leibniz_project_assignment where
  "book_leibniz_project_assignment D app V G g n = book_leibniz_class D app V (G n) (g n)"

lemma book_leibniz_project_assignment_typed:
  assumes typed: "book_env_typed D G g"
  shows "book_env_typed (book_leibniz_quotient_domain D app V) G (book_leibniz_project_assignment D app V G g)"
proof (unfold book_env_typed_def, rule allI)
  fix n
  have member: "g n \<in> D (G n)" by (rule book_env_at[where n=n, OF typed])
  show "book_leibniz_project_assignment D app V G g n \<in> book_leibniz_quotient_domain D app V (G n)"
    unfolding book_leibniz_project_assignment_def
    by (rule book_leibniz_quotient_domainI[where D=D and \<sigma>="G n", OF member])
qed

lemma book_leibniz_lift_project_equiv:
  assumes typed: "book_env_typed D G g"
  shows "book_leibniz_equiv D app V (G n)
    (book_leibniz_lift_assignment (book_leibniz_project_assignment D app V G g) n) (g n)"
  unfolding book_leibniz_lift_assignment_def book_leibniz_project_assignment_def
  by (rule book_leibniz_rep_equiv[where D=D and \<sigma>="G n", OF book_env_at[where n=n, OF typed]])

lemma book_leibniz_project_lift_assignment:
  assumes typed: "book_env_typed (book_leibniz_quotient_domain D app V) G q"
  shows "book_leibniz_project_assignment D app V G (book_leibniz_lift_assignment q) = q"
  by (rule ext, simp only: book_leibniz_project_assignment_def;
    rule book_leibniz_lift_assignment_projection[OF typed])

context book_full_environment
begin

theorem book_leibniz_quotient_denote_projection:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_in_language logical_type logical_signature signature stock M \<tau>"
  shows "book_leibniz_quotient_denote V (book_leibniz_project_assignment domain app V stock g) M =
    book_leibniz_class domain app V \<tau> (denote g M)"
proof -
  let ?q = "book_leibniz_project_assignment domain app V stock g"
  let ?h = "book_leibniz_lift_assignment ?q"
  have qt: "book_env_typed (book_leibniz_quotient_domain domain app V) stock ?q"
    by (rule book_leibniz_project_assignment_typed[OF typed])
  have ht: "book_env_typed domain stock ?h" by (rule book_leibniz_lift_assignment_typed[OF qt])
  have related: "book_leibniz_equiv domain app V (stock n) (?h n) (g n)" if "n \<in> named_fv M" for n
    by (rule book_leibniz_lift_project_equiv[where n=n, OF typed])
  have denotations: "book_leibniz_equiv domain app V \<tau> (denote ?h M) (denote g M)"
    by (rule book_leibniz_denote_assignments[OF rich ht typed language related])
  have classes: "book_leibniz_class domain app V \<tau> (denote ?h M) = book_leibniz_class domain app V \<tau> (denote g M)"
    by (rule book_leibniz_class_eq[OF denotations])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF language]; rule classes)
qed

theorem book_leibniz_quotient_truth_projection:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_in_language logical_type logical_signature signature stock A Prop"
  shows "book_leibniz_quotient_valuation V
    (book_leibniz_quotient_denote V (book_leibniz_project_assignment domain app V stock g) A) = V (denote g A)"
proof -
  have member: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I language typed])
  show ?thesis by (simp only: book_leibniz_quotient_denote_projection[OF rich typed language];
    rule book_leibniz_quotient_valuation_projection[OF rich typed member])
qed

theorem book_leibniz_quotient_truth_lift:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock"
    and typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
    and language: "book_in_language logical_type logical_signature signature stock A Prop"
  shows "book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A) =
    V (denote (book_leibniz_lift_assignment q) A)"
proof -
  have ht: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
    by (rule book_leibniz_lift_assignment_typed[OF typed])
  have member: "denote (book_leibniz_lift_assignment q) A \<in> domain Prop"
    by (rule denote_type[OF UNIV_I language ht])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF language];
    rule book_leibniz_quotient_valuation_projection[OF rich ht member])
qed

theorem book_leibniz_quotient_validity_iff:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock" and language: "book_in_language logical_type logical_signature signature stock A Prop"
  shows "(\<forall>q. book_env_typed (book_leibniz_quotient_domain domain app V) stock q \<longrightarrow>
      book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)) \<longleftrightarrow>
    (\<forall>g. book_env_typed domain stock g \<longrightarrow> V (denote g A))"
proof
  assume quotient_truth: "\<forall>q. book_env_typed (book_leibniz_quotient_domain domain app V) stock q \<longrightarrow>
    book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)"
  show "\<forall>g. book_env_typed domain stock g \<longrightarrow> V (denote g A)"
  proof (intro allI impI)
    fix g
    assume typed: "book_env_typed domain stock g"
    let ?q = "book_leibniz_project_assignment domain app V stock g"
    have qt: "book_env_typed (book_leibniz_quotient_domain domain app V) stock ?q"
      by (rule book_leibniz_project_assignment_typed[OF typed])
    have truth: "book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V ?q A)"
      by (rule mp[OF spec[where x="?q", OF quotient_truth] qt])
    show "V (denote g A)" using truth by (simp only: book_leibniz_quotient_truth_projection[OF rich typed language])
  qed
next
  assume original_truth: "\<forall>g. book_env_typed domain stock g \<longrightarrow> V (denote g A)"
  show "\<forall>q. book_env_typed (book_leibniz_quotient_domain domain app V) stock q \<longrightarrow>
    book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)"
  proof (intro allI impI)
    fix q
    assume typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
    have ht: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
      by (rule book_leibniz_lift_assignment_typed[OF typed])
    have truth: "V (denote (book_leibniz_lift_assignment q) A)"
      by (rule mp[OF spec[where x="book_leibniz_lift_assignment q", OF original_truth] ht])
    show "book_leibniz_quotient_valuation V (book_leibniz_quotient_denote V q A)"
      by (simp only: book_leibniz_quotient_truth_lift[OF rich typed language]; rule truth)
  qed
qed

end

end
