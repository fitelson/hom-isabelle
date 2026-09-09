theory Bacon_Book_Witness_Family_Syntax
  imports Bacon_Book_Conditional_Witness
begin

section \<open>Signatures and axioms indexed by a witness family\<close>

text \<open>
  Σ[I] adds cᵢ:τᵢ for i∈I, and W[I] contains (∃τᵢFᵢ)→Fᵢcᵢ.
  The index type and constant-name type are arbitrary. These definitions
  impose neither finiteness nor freshness; those hypotheses belong to
  the later consistency theorem. Source role: organizing the fresh
  witnesses of Bacon's Proposition 15.4, p.319.
\<close>

definition book_witness_family_signature ::
  "'c ssignature \<Rightarrow> ('i \<Rightarrow> otype) \<Rightarrow> ('i \<Rightarrow> 'c) \<Rightarrow> 'i set \<Rightarrow> 'c ssignature" where
  "book_witness_family_signature \<Sigma> \<tau> c I \<sigma> = \<Sigma> \<sigma> \<union> image c {i\<in>I. \<tau> i = \<sigma>}"

definition book_witness_family_axioms ::
  "sgcontext \<Rightarrow> ('i \<Rightarrow> otype) \<Rightarrow> ('i \<Rightarrow> 'c book_named_term) \<Rightarrow>
    ('i \<Rightarrow> 'c) \<Rightarrow> 'i set \<Rightarrow> 'c book_named_term set" where
  "book_witness_family_axioms G \<tau> F c I = image (\<lambda>i. book_witness_axiom G (\<tau> i) (F i) (c i)) I"

lemma book_witness_family_signature_empty:
  "book_witness_family_signature \<Sigma> \<tau> c {} = \<Sigma>"
  by (rule ext, simp add: book_witness_family_signature_def)

lemma book_witness_family_signature_insert:
  "book_witness_family_signature \<Sigma> \<tau> c (insert i I) =
    book_add_constant (book_witness_family_signature \<Sigma> \<tau> c I) (c i) (\<tau> i)"
  by (rule ext, auto simp: book_witness_family_signature_def book_add_constant_def)

lemma book_witness_family_signature_inclusion:
  "\<Sigma> \<sigma> \<subseteq> book_witness_family_signature \<Sigma> \<tau> c I \<sigma>"
  by (auto simp: book_witness_family_signature_def)

lemma book_witness_family_signature_member:
  assumes member: "i \<in> I"
  shows "c i \<in> book_witness_family_signature \<Sigma> \<tau> c I (\<tau> i)"
  using member by (auto simp: book_witness_family_signature_def)

lemma book_witness_family_axioms_empty:
  "book_witness_family_axioms G \<tau> F c {} = {}"
  by (simp add: book_witness_family_axioms_def)

lemma book_witness_family_axioms_insert:
  "book_witness_family_axioms G \<tau> F c (insert i I) =
    insert (book_witness_axiom G (\<tau> i) (F i) (c i)) (book_witness_family_axioms G \<tau> F c I)"
  by (simp add: book_witness_family_axioms_def)

lemma book_witness_family_axiom_language:
  assumes rich: "sg_rich G" and member: "i \<in> I"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
  shows "book_theory_formula (book_witness_family_signature \<Sigma> \<tau> c I) G
    (book_witness_axiom G (\<tau> i) (F i) (c i))"
proof -
  have enlarged: "book_in_language book_minimal_logical_type UNIV
    (book_witness_family_signature \<Sigma> \<tau> c I) G (F i) (Arr (\<tau> i) Prop)"
    by (rule book_language_signature_mono[OF predicate]; rule book_witness_family_signature_inclusion)
  show ?thesis by (rule book_witness_axiom_language[
    OF rich enlarged book_witness_family_signature_member[OF member]])
qed

lemma book_witness_family_premises_language:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and member: "A \<in> S \<union> book_witness_family_axioms G \<tau> F c I"
  shows "book_theory_formula (book_witness_family_signature \<Sigma> \<tau> c I) G A"
proof (cases "A \<in> S")
  case True
  show ?thesis by (rule book_language_signature_mono[OF language[OF True]];
    rule book_witness_family_signature_inclusion)
next
  case False
  obtain i where index: "i \<in> I" and shape: "A = book_witness_axiom G (\<tau> i) (F i) (c i)"
    using member False unfolding book_witness_family_axioms_def by blast
  show ?thesis by (simp only: shape,
    rule book_witness_family_axiom_language[where \<Sigma>=\<Sigma> and G=G and \<tau>=\<tau>
      and F=F and c=c and I=I and i=i, OF rich index predicates[OF index]])
qed

end
