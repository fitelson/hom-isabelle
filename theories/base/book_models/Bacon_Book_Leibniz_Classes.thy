theory Bacon_Book_Leibniz_Classes
  imports Bacon_Book_Leibniz_Equivalence
begin

section \<open>Typed Leibniz classes and their guarded representatives\<close>

text \<open>
  Write [a]σ = {b | a ≈ᴸᴱσ b} and Dσ/≈ᴸᴱσ = {[a]σ | a ∈ Dσ}.
  Source role: the typed equivalence classes for Bacon's Proposition 15.5,
  pp.321–322. The preceding leaf proves equivalence on Dσ, including
  when Dσ is empty.

  Isabelle representation. Classes are ordinary sets of values. A class
  belonging to the quotient domain has an original member a ∈ Dσ,
  so it is nonempty and contained in Dσ. Its representative is selected
  by SOME; only guarded lemmas assert properties of that total choice.
  No behavior of a representative of the empty set is stipulated.

  Status. Set-theoretic quotient groundwork, not a quotient application
  or model construction. No global domain nonemptiness, Functionality,
  separation, PER, BBK model, or logical valuation clause is assumed.
  Application compatibility remains a separate prerequisite.
\<close>

definition book_leibniz_class where
  "book_leibniz_class D app V \<sigma> a = {b. book_leibniz_equiv D app V \<sigma> a b}"

definition book_leibniz_quotient_domain where
  "book_leibniz_quotient_domain D app V \<sigma> =
    image (book_leibniz_class D app V \<sigma>) (D \<sigma>)"

definition book_leibniz_rep :: "'v set \<Rightarrow> 'v" where
  "book_leibniz_rep X = (SOME a. a \<in> X)"

lemma book_leibniz_class_iff:
  "b \<in> book_leibniz_class D app V \<sigma> a \<longleftrightarrow> book_leibniz_equiv D app V \<sigma> a b"
  by (simp only: book_leibniz_class_def mem_Collect_eq)

lemma book_leibniz_class_self:
  assumes member: "a \<in> D \<sigma>"
  shows "a \<in> book_leibniz_class D app V \<sigma> a"
  by (simp only: book_leibniz_class_iff;
    rule book_leibniz_refl[where D=D and \<sigma>=\<sigma>, OF member])

lemma book_leibniz_class_subset:
  "book_leibniz_class D app V \<sigma> a \<subseteq> D \<sigma>"
proof
  fix b
  assume member: "b \<in> book_leibniz_class D app V \<sigma> a"
  have equivalent: "book_leibniz_equiv D app V \<sigma> a b"
    using member by (simp only: book_leibniz_class_iff)
  show "b \<in> D \<sigma>" by (rule book_leibniz_right[OF equivalent])
qed

lemma book_leibniz_class_nonempty:
  assumes member: "a \<in> D \<sigma>"
  shows "book_leibniz_class D app V \<sigma> a \<noteq> {}"
proof
  assume empty: "book_leibniz_class D app V \<sigma> a = {}"
  have self: "a \<in> book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_class_self[where D=D and \<sigma>=\<sigma>, OF member])
  show False using self by (simp only: empty; simp)
qed

lemma book_leibniz_class_eq:
  assumes equivalent: "book_leibniz_equiv D app V \<sigma> a b"
  shows "book_leibniz_class D app V \<sigma> a = book_leibniz_class D app V \<sigma> b"
proof (rule set_eqI, rule iffI)
  fix c
  assume member: "c \<in> book_leibniz_class D app V \<sigma> a"
  have ac: "book_leibniz_equiv D app V \<sigma> a c"
    using member by (simp only: book_leibniz_class_iff)
  have ba: "book_leibniz_equiv D app V \<sigma> b a"
    by (rule book_leibniz_sym[OF equivalent])
  show "c \<in> book_leibniz_class D app V \<sigma> b"
    by (simp only: book_leibniz_class_iff; rule book_leibniz_trans[OF ba ac])
next
  fix c
  assume member: "c \<in> book_leibniz_class D app V \<sigma> b"
  have bc: "book_leibniz_equiv D app V \<sigma> b c"
    using member by (simp only: book_leibniz_class_iff)
  show "c \<in> book_leibniz_class D app V \<sigma> a"
    by (simp only: book_leibniz_class_iff; rule book_leibniz_trans[OF equivalent bc])
qed

theorem book_leibniz_class_eq_iff:
  assumes left: "a \<in> D \<sigma>" and right: "b \<in> D \<sigma>"
  shows "book_leibniz_class D app V \<sigma> a = book_leibniz_class D app V \<sigma> b \<longleftrightarrow>
    book_leibniz_equiv D app V \<sigma> a b"
proof
  assume equal: "book_leibniz_class D app V \<sigma> a = book_leibniz_class D app V \<sigma> b"
  have bm: "b \<in> book_leibniz_class D app V \<sigma> b"
    by (rule book_leibniz_class_self[where D=D and \<sigma>=\<sigma>, OF right])
  have ba: "b \<in> book_leibniz_class D app V \<sigma> a" using bm by (simp only: equal)
  show "book_leibniz_equiv D app V \<sigma> a b" using ba by (simp only: book_leibniz_class_iff)
next
  assume equivalent: "book_leibniz_equiv D app V \<sigma> a b"
  show "book_leibniz_class D app V \<sigma> a = book_leibniz_class D app V \<sigma> b"
    by (rule book_leibniz_class_eq[OF equivalent])
qed

lemma book_leibniz_quotient_domainI:
  assumes member: "a \<in> D \<sigma>"
  shows "book_leibniz_class D app V \<sigma> a \<in> book_leibniz_quotient_domain D app V \<sigma>"
  unfolding book_leibniz_quotient_domain_def by (rule imageI[OF member])

lemma book_leibniz_quotient_domainE:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  obtains a where "a \<in> D \<sigma>" and "X = book_leibniz_class D app V \<sigma> a"
proof -
  obtain a where typed: "a \<in> D \<sigma>" and class_eq: "X = book_leibniz_class D app V \<sigma> a"
    using member unfolding book_leibniz_quotient_domain_def by (elim imageE) blast
  show thesis by (rule that[OF typed class_eq])
qed

lemma book_leibniz_quotient_class_nonempty:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  shows "X \<noteq> {}"
proof -
  obtain a where typed: "a \<in> D \<sigma>" and class_eq: "X = book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_quotient_domainE[OF member])
  show ?thesis by (simp only: class_eq;
    rule book_leibniz_class_nonempty[where D=D and \<sigma>=\<sigma>, OF typed])
qed

lemma book_leibniz_quotient_class_subset:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  shows "X \<subseteq> D \<sigma>"
proof -
  obtain a where typed: "a \<in> D \<sigma>" and class_eq: "X = book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_quotient_domainE[OF member])
  show ?thesis by (simp only: class_eq; rule book_leibniz_class_subset)
qed

lemma book_leibniz_rep_member:
  assumes nonempty: "X \<noteq> {}"
  shows "book_leibniz_rep X \<in> X"
  unfolding book_leibniz_rep_def
proof (rule someI_ex)
  show "\<exists>a. a \<in> X" using nonempty by blast
qed

lemma book_leibniz_quotient_rep_member:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  shows "book_leibniz_rep X \<in> X"
  by (rule book_leibniz_rep_member[OF book_leibniz_quotient_class_nonempty[OF member]])

lemma book_leibniz_rep_type:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  shows "book_leibniz_rep X \<in> D \<sigma>"
  by (rule subsetD[OF book_leibniz_quotient_class_subset[OF member]
    book_leibniz_quotient_rep_member[OF member]])

lemma book_leibniz_rep_equiv:
  assumes member: "a \<in> D \<sigma>"
  shows "book_leibniz_equiv D app V \<sigma> (book_leibniz_rep (book_leibniz_class D app V \<sigma> a)) a"
proof -
  have chosen: "book_leibniz_rep (book_leibniz_class D app V \<sigma> a) \<in>
    book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_rep_member[OF
      book_leibniz_class_nonempty[where D=D and \<sigma>=\<sigma>, OF member]])
  have forward: "book_leibniz_equiv D app V \<sigma> a
    (book_leibniz_rep (book_leibniz_class D app V \<sigma> a))"
    using chosen by (simp only: book_leibniz_class_iff)
  show ?thesis by (rule book_leibniz_sym[OF forward])
qed

theorem book_leibniz_rep_reconstruct:
  assumes member: "X \<in> book_leibniz_quotient_domain D app V \<sigma>"
  shows "book_leibniz_class D app V \<sigma> (book_leibniz_rep X) = X"
proof -
  obtain a where typed: "a \<in> D \<sigma>" and class_eq: "X = book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_quotient_domainE[OF member])
  have related: "book_leibniz_equiv D app V \<sigma> (book_leibniz_rep X) a"
    by (simp only: class_eq; rule book_leibniz_rep_equiv[where D=D and \<sigma>=\<sigma>, OF typed])
  have equal: "book_leibniz_class D app V \<sigma> (book_leibniz_rep X) = book_leibniz_class D app V \<sigma> a"
    by (rule book_leibniz_class_eq[OF related])
  show ?thesis by (rule trans[OF equal sym[OF class_eq]])
qed

lemma book_leibniz_quotient_rep_equiv:
  assumes quotient: "X \<in> book_leibniz_quotient_domain D app V \<sigma>" and member: "a \<in> X"
  shows "book_leibniz_equiv D app V \<sigma> (book_leibniz_rep X) a"
proof -
  have in_class: "a \<in> book_leibniz_class D app V \<sigma> (book_leibniz_rep X)"
    by (simp only: book_leibniz_rep_reconstruct[OF quotient]; rule member)
  show ?thesis using in_class by (simp only: book_leibniz_class_iff)
qed

end
