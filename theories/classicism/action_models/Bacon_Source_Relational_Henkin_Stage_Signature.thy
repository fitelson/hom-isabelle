theory Bacon_Source_Relational_Henkin_Stage_Signature
  imports Bacon_Source_Relational_Henkin_Name_Stages Bacon_Source_Relational_Witness_Family_Syntax
begin

section \<open>The exact old-stage predicate family and its constructed names\<close>

text \<open>
  Iₖ={(σ,F) | F is closed and F:σ→t in Σₖ}.
  Its name map sends (σ,F) to Witness(k,σ,F). The datatype
  constructors prove injectivity and freshness; neither is assumed.
  The family signature Σₖ[Iₖ] is exactly the recursively defined
  successor Σₖ₊₁, so the supplied-family machinery can later be
  instantiated with these actual names.

  Source role: Theorem 3.2, footnote 64, p.45. The index set includes
  ALL old-stage closed R predicates, without countability or an
  enumeration. These are signature facts only, not consistency,
  accumulated premise sets or witness completeness.
\<close>

type_synonym 'c paper_R_henkin_index =
  "otype \<times> ('c paper_R_henkin_name) paper_named_term"

definition paper_R_henkin_stage_indices ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> 'c paper_R_henkin_index set" where
  "paper_R_henkin_stage_indices \<Sigma> G k =
    {i. named_fv (snd i) = {} \<and>
      paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G (snd i) (Arr (fst i) Prop)}"

definition paper_R_henkin_stage_name ::
  "nat \<Rightarrow> 'c paper_R_henkin_index \<Rightarrow> 'c paper_R_henkin_name" where
  "paper_R_henkin_stage_name k i = RWitness k (fst i) (snd i)"

lemma paper_R_henkin_stage_indexI:
  assumes closed: "named_fv F = {}"
    and predicate: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<sigma> Prop)"
  shows "(\<sigma>,F) \<in> paper_R_henkin_stage_indices \<Sigma> G k"
  using assms by (simp add: paper_R_henkin_stage_indices_def)

lemma paper_R_henkin_stage_index_closed:
  "i \<in> paper_R_henkin_stage_indices \<Sigma> G k \<Longrightarrow> named_fv (snd i) = {}"
  unfolding paper_R_henkin_stage_indices_def by blast

lemma paper_R_henkin_stage_index_language:
  "i \<in> paper_R_henkin_stage_indices \<Sigma> G k \<Longrightarrow>
    paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G (snd i) (Arr (fst i) Prop)"
  unfolding paper_R_henkin_stage_indices_def by blast

theorem paper_R_henkin_stage_name_inj:
  "inj (paper_R_henkin_stage_name k)"
proof (rule injI)
  fix i j
  assume equality: "paper_R_henkin_stage_name k i = paper_R_henkin_stage_name k j"
  show "i = j" using equality by (cases i; cases j; simp add: paper_R_henkin_stage_name_def)
qed

theorem paper_R_henkin_stage_typed_names_inj_on:
  "inj_on (\<lambda>i. (fst i,paper_R_henkin_stage_name k i)) (paper_R_henkin_stage_indices \<Sigma> G k)"
proof (rule inj_onI)
  fix i j
  assume "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" "j \<in> paper_R_henkin_stage_indices \<Sigma> G k"
    and equality: "(fst i,paper_R_henkin_stage_name k i) = (fst j,paper_R_henkin_stage_name k j)"
  have names: "paper_R_henkin_stage_name k i = paper_R_henkin_stage_name k j" using equality by simp
  show "i = j" by (rule injD[OF paper_R_henkin_stage_name_inj names])
qed

lemma paper_R_henkin_stage_name_fresh:
  "paper_R_henkin_stage_name k i \<notin> paper_R_henkin_signature \<Sigma> G k \<tau>"
  unfolding paper_R_henkin_stage_name_def by (rule paper_R_henkin_signature_witness_fresh)

section \<open>The family image is precisely the new part of the next signature\<close>

lemma paper_R_henkin_stage_name_image:
  "image (paper_R_henkin_stage_name k) {i\<in>paper_R_henkin_stage_indices \<Sigma> G k. fst i = \<tau>} =
    {RWitness k \<tau> F |F. named_fv F = {} \<and>
      paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<tau> Prop)}"
proof (rule set_eqI, rule iffI)
  fix c
  assume member: "c \<in> image (paper_R_henkin_stage_name k)
    {i\<in>paper_R_henkin_stage_indices \<Sigma> G k. fst i = \<tau>}"
  obtain i where index: "i \<in> paper_R_henkin_stage_indices \<Sigma> G k"
    and itype: "fst i = \<tau>" and shape: "c = paper_R_henkin_stage_name k i" using member by blast
  have closed: "named_fv (snd i) = {}" by (rule paper_R_henkin_stage_index_closed[OF index])
  have predicate: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G (snd i) (Arr \<tau> Prop)"
    using paper_R_henkin_stage_index_language[OF index] by (simp only: itype)
  show "c \<in> {RWitness k \<tau> F |F. named_fv F = {} \<and>
    paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<tau> Prop)}"
    using closed predicate by (auto simp: shape paper_R_henkin_stage_name_def itype)
next
  fix c
  assume member: "c \<in> {RWitness k \<tau> F |F. named_fv F = {} \<and>
    paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<tau> Prop)}"
  obtain F where closed: "named_fv F = {}"
    and predicate: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G F (Arr \<tau> Prop)"
    and shape: "c = RWitness k \<tau> F" using member by blast
  have index: "(\<tau>,F) \<in> {i\<in>paper_R_henkin_stage_indices \<Sigma> G k. fst i = \<tau>}"
    using paper_R_henkin_stage_indexI[OF closed predicate] by simp
  have mapped: "paper_R_henkin_stage_name k (\<tau>,F) \<in> image (paper_R_henkin_stage_name k)
      {i\<in>paper_R_henkin_stage_indices \<Sigma> G k. fst i = \<tau>}"
    by (rule imageI[OF index])
  show "c \<in> image (paper_R_henkin_stage_name k) {i\<in>paper_R_henkin_stage_indices \<Sigma> G k. fst i = \<tau>}"
    using mapped by (simp only: shape paper_R_henkin_stage_name_def fst_conv snd_conv)
qed

theorem paper_R_henkin_signature_family:
  "paper_R_henkin_signature \<Sigma> G (Suc k) =
    paper_R_witness_family_signature (paper_R_henkin_signature \<Sigma> G k) fst
      (paper_R_henkin_stage_name k) (paper_R_henkin_stage_indices \<Sigma> G k)"
  by (rule ext; simp only: paper_R_henkin_signature.simps
    paper_R_witness_family_signature_def paper_R_henkin_stage_name_image)

end
