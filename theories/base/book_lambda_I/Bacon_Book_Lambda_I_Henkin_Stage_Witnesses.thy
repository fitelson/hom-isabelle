theory Bacon_Book_Lambda_I_Henkin_Stage_Witnesses
  imports Bacon_Book_Lambda_I_Henkin_Name_Stages Bacon_Book_Lambda_I_Witness_Family_Syntax
    Bacon_Book_Lambda_I_Closed_Maximal_Extension
begin

section \<open>The closed-predicate family at one signature stage\<close>

text \<open>
  Iₙ consists of pairs (σ,F) with F:σ→t a closed λI predicate of Σₙ;
  relevance of F is part of the definition of the index set.
  Its assigned name is cₙ(σ,F)=Witness(n,σ,F), and its axiom is
  (∃σF)→Fcₙ(σ,F). Source role: the witness-family organization of
  Bacon, Proposition 15.4, p.319.

  Representation. This is an instance of book_witness_family_axioms,
  using fst for the type and snd for the predicate. The family may be
  infinite, even uncountable. The payload stored in a name remains opaque
  to object-language syntax. We prove freshness, injectivity, the exact
  next-stage signature, and typed closedness of the displayed axioms.
  No consistency or model assertion is made.
\<close>

type_synonym 'c book_lambda_I_henkin_index =
  "otype \<times> ('c book_henkin_name) book_named_term"

definition book_lambda_I_henkin_stage_indices ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> 'c book_lambda_I_henkin_index set" where
  "book_lambda_I_henkin_stage_indices \<Sigma> G n =
    {i. named_fv (snd i) = {} \<and> book_lambda_I (snd i) \<and>
      book_in_language book_minimal_logical_type UNIV
        (book_lambda_I_henkin_signature \<Sigma> G n) G (snd i) (Arr (fst i) Prop)}"

definition book_lambda_I_henkin_stage_name ::
  "nat \<Rightarrow> 'c book_lambda_I_henkin_index \<Rightarrow> 'c book_henkin_name" where
  "book_lambda_I_henkin_stage_name n i = BookWitness n (fst i) (snd i)"

definition book_lambda_I_henkin_stage_axioms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c book_henkin_name) book_named_term set" where
  "book_lambda_I_henkin_stage_axioms \<Sigma> G n =
    book_witness_family_axioms G fst snd (book_lambda_I_henkin_stage_name n) (book_lambda_I_henkin_stage_indices \<Sigma> G n)"

lemma book_lambda_I_henkin_stage_index_closed:
  assumes member: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
  shows "named_fv (snd i) = {}"
  using member unfolding book_lambda_I_henkin_stage_indices_def by blast

lemma book_lambda_I_henkin_stage_index_lambda_I:
  assumes member: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
  shows "book_lambda_I (snd i)"
  using member unfolding book_lambda_I_henkin_stage_indices_def by blast

lemma book_lambda_I_henkin_stage_index_language:
  assumes member: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
  shows "book_in_language book_minimal_logical_type UNIV
    (book_lambda_I_henkin_signature \<Sigma> G n) G (snd i) (Arr (fst i) Prop)"
  using member unfolding book_lambda_I_henkin_stage_indices_def by blast

theorem book_lambda_I_henkin_stage_name_inj: "inj (book_lambda_I_henkin_stage_name n)"
proof (rule injI)
  fix i j
  assume equality: "book_lambda_I_henkin_stage_name n i = book_lambda_I_henkin_stage_name n j"
  show "i = j" using equality by (cases i; cases j; simp add: book_lambda_I_henkin_stage_name_def)
qed

corollary book_lambda_I_henkin_stage_name_inj_on:
  "inj_on (book_lambda_I_henkin_stage_name n) (book_lambda_I_henkin_stage_indices \<Sigma> G n)"
  by (rule inj_on_subset[OF book_lambda_I_henkin_stage_name_inj subset_UNIV])

lemma book_lambda_I_henkin_stage_name_fresh:
  "book_lambda_I_henkin_stage_name n i \<notin> book_lambda_I_henkin_signature \<Sigma> G n \<tau>"
  unfolding book_lambda_I_henkin_stage_name_def by (rule book_lambda_I_henkin_signature_witness_fresh)

section \<open>The family signature is exactly the next stage\<close>

lemma book_lambda_I_henkin_stage_name_image:
  "image (book_lambda_I_henkin_stage_name n) {i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n. fst i = \<tau>} =
    {BookWitness n \<tau> F |F. named_fv F = {} \<and> book_lambda_I F \<and>
      book_in_language book_minimal_logical_type UNIV (book_lambda_I_henkin_signature \<Sigma> G n) G F (Arr \<tau> Prop)}"
proof (rule set_eqI, rule iffI)
  fix c
  assume member: "c \<in> image (book_lambda_I_henkin_stage_name n)
    {i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n. fst i = \<tau>}"
  obtain i where index: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
    and itype: "fst i = \<tau>" and shape: "c = book_lambda_I_henkin_stage_name n i"
    using member by blast
  have closed: "named_fv (snd i) = {}" by (rule book_lambda_I_henkin_stage_index_closed[OF index])
  have lambda_I: "book_lambda_I (snd i)" by (rule book_lambda_I_henkin_stage_index_lambda_I[OF index])
  have language: "book_in_language book_minimal_logical_type UNIV
    (book_lambda_I_henkin_signature \<Sigma> G n) G (snd i) (Arr \<tau> Prop)"
    using book_lambda_I_henkin_stage_index_language[OF index] by (simp only: itype)
  show "c \<in> {BookWitness n \<tau> F |F. named_fv F = {} \<and> book_lambda_I F \<and>
    book_in_language book_minimal_logical_type UNIV (book_lambda_I_henkin_signature \<Sigma> G n) G F (Arr \<tau> Prop)}"
    using closed lambda_I language by (auto simp: shape book_lambda_I_henkin_stage_name_def itype)
next
  fix c
  assume member: "c \<in> {BookWitness n \<tau> F |F. named_fv F = {} \<and> book_lambda_I F \<and>
    book_in_language book_minimal_logical_type UNIV (book_lambda_I_henkin_signature \<Sigma> G n) G F (Arr \<tau> Prop)}"
  obtain F where closed: "named_fv F = {}" and lambda_I: "book_lambda_I F"
    and language: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_signature \<Sigma> G n) G F (Arr \<tau> Prop)"
    and shape: "c = BookWitness n \<tau> F" using member by blast
  have index: "(\<tau>,F) \<in> {i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n. fst i = \<tau>}"
    using closed lambda_I language by (simp add: book_lambda_I_henkin_stage_indices_def)
  have mapped: "book_lambda_I_henkin_stage_name n (\<tau>,F) \<in>
    image (book_lambda_I_henkin_stage_name n) {i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n. fst i = \<tau>}"
    by (rule imageI[OF index])
  show "c \<in> image (book_lambda_I_henkin_stage_name n)
    {i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n. fst i = \<tau>}"
    using mapped by (simp only: shape book_lambda_I_henkin_stage_name_def fst_conv snd_conv)
qed

theorem book_lambda_I_henkin_signature_family:
  "book_lambda_I_henkin_signature \<Sigma> G (Suc n) =
    book_witness_family_signature (book_lambda_I_henkin_signature \<Sigma> G n) fst
      (book_lambda_I_henkin_stage_name n) (book_lambda_I_henkin_stage_indices \<Sigma> G n)"
  by (rule ext; simp only: book_lambda_I_henkin_signature.simps
      book_witness_family_signature_def book_lambda_I_henkin_stage_name_image)

section \<open>Typed closed witness axioms\<close>

lemma book_lambda_I_henkin_stage_axiom_language:
  assumes rich: "sg_rich G" and index: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
  shows "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G
    (book_witness_axiom G (fst i) (snd i) (book_lambda_I_henkin_stage_name n i))"
proof -
  have predicate: "book_in_language book_minimal_logical_type UNIV
    (book_lambda_I_henkin_signature \<Sigma> G n) G (snd i) (Arr (fst i) Prop)"
    by (rule book_lambda_I_henkin_stage_index_language[OF index])
  have lambda_I: "book_lambda_I (snd i)" by (rule book_lambda_I_henkin_stage_index_lambda_I[OF index])
  show ?thesis by (simp only: book_lambda_I_henkin_signature_family;
    rule book_lambda_I_witness_family_axiom_language[where \<Sigma>="book_lambda_I_henkin_signature \<Sigma> G n"
      and G=G and \<tau>=fst and F=snd and c="book_lambda_I_henkin_stage_name n"
      and I="book_lambda_I_henkin_stage_indices \<Sigma> G n" and i=i, OF rich index predicate lambda_I])
qed

lemma book_lambda_I_henkin_stage_axiom_closed:
  assumes index: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
  shows "named_fv (book_witness_axiom G (fst i) (snd i) (book_lambda_I_henkin_stage_name n i)) = {}"
  by (rule book_witness_axiom_closed[OF book_lambda_I_henkin_stage_index_closed[OF index]])

theorem book_lambda_I_henkin_stage_axioms_member:
  assumes rich: "sg_rich G" and member: "A \<in> book_lambda_I_henkin_stage_axioms \<Sigma> G n"
  shows "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G A \<and> named_fv A = {}"
proof -
  obtain i where index: "i \<in> book_lambda_I_henkin_stage_indices \<Sigma> G n"
    and shape: "A = book_witness_axiom G (fst i) (snd i) (book_lambda_I_henkin_stage_name n i)"
    using member unfolding book_lambda_I_henkin_stage_axioms_def book_witness_family_axioms_def by blast
  show ?thesis by (simp only: shape; rule conjI[
    OF book_lambda_I_henkin_stage_axiom_language[OF rich index] book_lambda_I_henkin_stage_axiom_closed[OF index]])
qed

corollary book_lambda_I_henkin_stage_axioms_closed_set:
  assumes rich: "sg_rich G"
  shows "book_lambda_I_closed_formula_set (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G (book_lambda_I_henkin_stage_axioms \<Sigma> G n)"
  unfolding book_lambda_I_closed_formula_set_def
  by (intro ballI; rule book_lambda_I_henkin_stage_axioms_member[OF rich]; assumption)

end
