theory Bacon_Book_Printed_Conversion
  imports Bacon_Book_Source_Reduction
begin

section \<open>Language-guarded conversion using the printed β proviso\<close>

text \<open>
  A≡βηB is generated here by the printed-free-for β contractions
  and η contractions in term contexts, with reflexivity, symmetry, and
  transitivity. Each node has the indicated type and belongs to the
  declared logical and nonlogical language.
  Source: Definitions 3.7–3.10, pp.70–73, with the printed β proviso.

  This is an independent conversion relation. There is NO α constructor.
  In particular, bound-variable relettering must be derived by actual
  printed βη steps, not inserted through the α-inclusive reduction
  relation or borrowed from the older exact-capture conversion judgment.
  No proof-calculus, semantics, richness, or confluence premise is used.
\<close>

inductive book_printed_conversion ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'l set \<Rightarrow> 'c ssignature \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow>
    ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> bool"
  for L :: "'l \<Rightarrow> otype" and \<Lambda> :: "'l set" and \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Refl: "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow> book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A A"
| PrintedBeta: "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow>
    book_in_language L \<Lambda> \<Sigma> G B \<tau> \<Longrightarrow>
    named_compatible_step book_printed_beta_contract A B \<Longrightarrow>
    book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
| Eta: "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<Longrightarrow>
    book_in_language L \<Lambda> \<Sigma> G B \<tau> \<Longrightarrow>
    named_compatible_step named_eta_contract A B \<Longrightarrow>
    book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
| Sym: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B \<Longrightarrow>
    book_printed_conversion L \<Lambda> \<Sigma> G \<tau> B A"
| Trans: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B \<Longrightarrow>
    book_printed_conversion L \<Lambda> \<Sigma> G \<tau> B C \<Longrightarrow>
    book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A C"

lemma book_printed_conversion_languages:
  assumes conversion: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  shows "book_in_language L \<Lambda> \<Sigma> G A \<tau> \<and> book_in_language L \<Lambda> \<Sigma> G B \<tau>"
  using conversion by (induction rule: book_printed_conversion.induct) blast+

end
