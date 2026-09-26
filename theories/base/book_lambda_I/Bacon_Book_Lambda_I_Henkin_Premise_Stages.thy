theory Bacon_Book_Lambda_I_Henkin_Premise_Stages
  imports Bacon_Book_Lambda_I_Henkin_Stage_Consistency Bacon_Book_Lambda_I_Constant_Renaming_Reflection
begin

section \<open>Premises accompanying the successive witness signatures\<close>

text \<open>
  S₀ is the image of S under c↦Original(c), and
  Sₙ₊₁=Sₙ∪Wₙ, where Wₙ contains the conditional witness axioms
  for all closed λI predicates of Σₙ (not all closed unrestricted
  predicates). Stage zero uses the exact image
  signature; later stages use the already checked witness extension.
  Source role: iteration of the construction in Proposition 15.4, p.319.

  One stage may contain arbitrarily many axioms. This development proves
  language membership and consistency at each stage, not consistency of
  a union, witness completeness, or model existence. The original S
  may be open and infinite. Closedness is a separate optional property.
\<close>

primrec book_lambda_I_henkin_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> nat \<Rightarrow>
    ('c book_henkin_name) book_named_term set" where
  "book_lambda_I_henkin_premises \<Sigma> G S 0 = image (book_constant_rename BookOriginal) S"
| "book_lambda_I_henkin_premises \<Sigma> G S (Suc n) =
    book_lambda_I_henkin_premises \<Sigma> G S n \<union> book_lambda_I_henkin_stage_axioms \<Sigma> G n"

lemma book_lambda_I_henkin_premises_step:
  "book_lambda_I_henkin_premises \<Sigma> G S n \<subseteq> book_lambda_I_henkin_premises \<Sigma> G S (Suc n)"
  by (simp only: book_lambda_I_henkin_premises.simps; rule Un_upper1)

theorem book_lambda_I_henkin_premises_mono:
  assumes order: "m \<le> n"
  shows "book_lambda_I_henkin_premises \<Sigma> G S m \<subseteq> book_lambda_I_henkin_premises \<Sigma> G S n"
  using order
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  have equality: "m = 0" using zero.prems by simp
  show ?case by (simp only: equality; rule subset_refl)
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True
    show ?thesis by (simp only: True; rule subset_refl)
  next
    case False
    have earlier: "m \<le> n" using Suc.prems False by arith
    have included: "book_lambda_I_henkin_premises \<Sigma> G S m \<subseteq> book_lambda_I_henkin_premises \<Sigma> G S n"
      by (rule Suc.IH[OF earlier])
    show ?thesis by (rule subset_trans[OF included book_lambda_I_henkin_premises_step])
  qed
qed

lemma book_lambda_I_henkin_premises_original_inclusion:
  "image (book_constant_rename BookOriginal) S \<subseteq> book_lambda_I_henkin_premises \<Sigma> G S n"
proof -
  have initial: "book_lambda_I_henkin_premises \<Sigma> G S 0 \<subseteq> book_lambda_I_henkin_premises \<Sigma> G S n"
    by (rule book_lambda_I_henkin_premises_mono, rule zero_le)
  show ?thesis using initial by (simp only: book_lambda_I_henkin_premises.simps)
qed

section \<open>Every stage has its corresponding language\<close>

theorem book_lambda_I_henkin_premises_language:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and member: "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n"
  shows "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G n) G A"
  using member
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  obtain B where original: "B \<in> S" and shape: "A = book_constant_rename BookOriginal B"
    using zero.prems by auto
  have renamed: "book_lambda_I_formula (\<lambda>\<tau>. image BookOriginal (\<Sigma> \<tau>)) G
    (book_constant_rename BookOriginal B)"
    by (rule book_lambda_I_constant_rename_formula[OF language[OF original]]; rule imageI; assumption)
  show ?case using renamed by (simp only: book_lambda_I_henkin_signature.simps shape)
next
  case (Suc n)
  show ?case
  proof (cases "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n")
    case True
    have previous: "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G n) G A"
      by (rule Suc.IH[OF True])
    show ?thesis by (rule book_lambda_I_formula_signature_mono[OF previous]; rule book_lambda_I_henkin_signature_step)
  next
    case False
    have axiom_member: "A \<in> book_lambda_I_henkin_stage_axioms \<Sigma> G n"
      using Suc.prems False by simp
    show ?thesis by (rule conjunct1[OF book_lambda_I_henkin_stage_axioms_member[OF rich axiom_member]])
  qed
qed

section \<open>Consistency of every stage\<close>

lemma book_lambda_I_henkin_original_injective:
  "inj (BookOriginal :: 'c \<Rightarrow> 'c book_henkin_name)"
  by (rule injI, simp)

theorem book_lambda_I_henkin_premises_consistent:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and consistent: "book_lambda_I_consistent \<Sigma> G S"
  shows "book_lambda_I_consistent (book_lambda_I_henkin_signature \<Sigma> G n) G (book_lambda_I_henkin_premises \<Sigma> G S n)"
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  have initial: "book_lambda_I_consistent (\<lambda>\<tau>. image BookOriginal (\<Sigma> \<tau>)) G
    (image (book_constant_rename BookOriginal) S)"
    by (rule iffD1[OF book_lambda_I_consistent_constant_rename_iff[
      where f=BookOriginal and \<Sigma>=\<Sigma> and G=G and S=S,
      OF book_lambda_I_henkin_original_injective] consistent])
  show ?case using initial by (simp only: book_lambda_I_henkin_signature.simps book_lambda_I_henkin_premises.simps)
next
  case (Suc n)
  have stage_language: "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G n) G A"
    if "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n" for A
    by (rule book_lambda_I_henkin_premises_language[OF rich language that])
  have next_stage: "book_lambda_I_consistent (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G
    (book_lambda_I_henkin_premises \<Sigma> G S n \<union> book_lambda_I_henkin_stage_axioms \<Sigma> G n)"
    by (rule book_lambda_I_henkin_stage_consistent[where \<Sigma>=\<Sigma> and G=G and n=n
      and S="book_lambda_I_henkin_premises \<Sigma> G S n", OF rich Suc.IH stage_language])
  show ?case using next_stage by (simp only: book_lambda_I_henkin_premises.simps)
qed

section \<open>Closedness is preserved when present initially\<close>

lemma book_lambda_I_henkin_premises_closed:
  assumes rich: "sg_rich G"
    and closed: "\<And>A. A \<in> S \<Longrightarrow> named_fv A = {}"
    and member: "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n"
  shows "named_fv A = {}"
  using member
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  obtain B where original: "B \<in> S" and shape: "A = book_constant_rename BookOriginal B"
    using zero.prems by auto
  show ?case by (simp only: shape book_constant_rename_fv; rule closed[OF original])
next
  case (Suc n)
  show ?case
  proof (cases "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n")
    case True
    show ?thesis by (rule Suc.IH[OF True])
  next
    case False
    have axiom_member: "A \<in> book_lambda_I_henkin_stage_axioms \<Sigma> G n"
      using Suc.prems False by simp
    show ?thesis by (rule conjunct2[OF book_lambda_I_henkin_stage_axioms_member[OF rich axiom_member]])
  qed
qed

corollary book_lambda_I_henkin_premises_closed_set:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
    and closed: "\<And>A. A \<in> S \<Longrightarrow> named_fv A = {}"
  shows "book_lambda_I_closed_formula_set (book_lambda_I_henkin_signature \<Sigma> G n) G (book_lambda_I_henkin_premises \<Sigma> G S n)"
proof (unfold book_lambda_I_closed_formula_set_def, rule ballI)
  fix A
  assume member: "A \<in> book_lambda_I_henkin_premises \<Sigma> G S n"
  show "book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G n) G A \<and> named_fv A = {}"
    by (rule conjI[OF book_lambda_I_henkin_premises_language[OF rich language member]
      book_lambda_I_henkin_premises_closed[OF rich closed member]])
qed

end
