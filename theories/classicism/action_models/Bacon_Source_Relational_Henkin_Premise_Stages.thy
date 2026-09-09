theory Bacon_Source_Relational_Henkin_Premise_Stages
  imports Bacon_Source_Relational_Henkin_Stage_Signature Bacon_Source_Relational_Constant_Map
begin

section \<open>Actual accumulated witness premises\<close>

text \<open>
  T₀ is the Original-name image of S, and Tₖ₊₁=Tₖ∪W[Iₖ].
  The index set and name map are the constructed stage-k objects:
  no supplied fresh-name family is substituted for them.
  Source: the Henkin extension of Theorem 3.2, footnote 64, p.45.
  This leaf proves stage inclusion and closedness; consistency is
  established separately. No union or maximal theory is defined yet.
\<close>

definition paper_R_henkin_stage_axioms ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set" where
  "paper_R_henkin_stage_axioms \<Sigma> G k =
    paper_R_witness_family_axioms G fst snd (paper_R_henkin_stage_name k) (paper_R_henkin_stage_indices \<Sigma> G k)"

primrec paper_R_henkin_premises ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> nat \<Rightarrow>
    ('c paper_R_henkin_name) paper_named_term set" where
  "paper_R_henkin_premises \<Sigma> G S 0 = image (paper_R_constant_map ROriginal) S"
| "paper_R_henkin_premises \<Sigma> G S (Suc k) =
    paper_R_henkin_premises \<Sigma> G S k \<union> paper_R_henkin_stage_axioms \<Sigma> G k"

lemma paper_R_henkin_premises_step:
  "paper_R_henkin_premises \<Sigma> G S k \<subseteq> paper_R_henkin_premises \<Sigma> G S (Suc k)"
  by (simp only: paper_R_henkin_premises.simps; rule Un_upper1)

theorem paper_R_henkin_premises_mono:
  assumes order: "j \<le> k"
  shows "paper_R_henkin_premises \<Sigma> G S j \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
  using order
proof (induction k rule: nat.induct[case_names zero Suc])
  case zero
  have same: "j = 0" using zero.prems by simp
  show ?case by (simp only: same; rule subset_refl)
next
  case (Suc k)
  show ?case
  proof (cases "j = Suc k")
    case True
    show ?thesis by (simp only: True; rule subset_refl)
  next
    case False
    have previous: "j \<le> k" using Suc.prems False by arith
    have inclusion: "paper_R_henkin_premises \<Sigma> G S j \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
      by (rule Suc.IH[OF previous])
    show ?thesis by (rule subset_trans[OF inclusion paper_R_henkin_premises_step])
  qed
qed

lemma paper_R_henkin_premises_original_inclusion:
  "image (paper_R_constant_map ROriginal) S \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
proof -
  have inclusion: "paper_R_henkin_premises \<Sigma> G S 0 \<subseteq> paper_R_henkin_premises \<Sigma> G S k"
    by (rule paper_R_henkin_premises_mono; simp)
  show ?thesis using inclusion by (simp only: paper_R_henkin_premises.simps)
qed

lemma paper_R_henkin_original_closed:
  assumes source: "paper_R_closed_theory \<Sigma> G S"
  shows "paper_R_closed_theory (paper_R_henkin_signature \<Sigma> G 0) G
    (image (paper_R_constant_map ROriginal) S)"
proof (unfold paper_R_closed_theory_def, intro ballI)
  fix B
  assume member: "B \<in> image (paper_R_constant_map ROriginal) S"
  obtain A where original: "A \<in> S" and shape: "B = paper_R_constant_map ROriginal A" using member by blast
  have sentence: "paper_R_sentence \<Sigma> G A" by (rule paper_R_closed_theory_member[OF source original])
  have language: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G 0) G
    (paper_R_constant_map ROriginal A) Prop"
    by (rule paper_R_constant_map_language[OF paper_R_sentence_language[OF sentence]];
      rule paper_R_henkin_signature_original; assumption)
  have closed: "named_fv (paper_R_constant_map ROriginal A) = {}"
    by (simp only: paper_R_constant_map_fv; rule paper_R_sentence_closed[OF sentence])
  show "paper_R_sentence (paper_R_henkin_signature \<Sigma> G 0) G B"
    by (simp only: shape; rule paper_R_sentenceI[OF language closed])
qed

theorem paper_R_henkin_premises_closed:
  assumes rich: "paper_R_rich G" and source: "paper_R_closed_theory \<Sigma> G S"
  shows "paper_R_closed_theory (paper_R_henkin_signature \<Sigma> G k) G (paper_R_henkin_premises \<Sigma> G S k)"
proof (induction k rule: nat.induct[case_names zero Suc])
  case zero
  show ?case by (simp only: paper_R_henkin_premises.simps; rule paper_R_henkin_original_closed[OF source])
next
  case (Suc k)
  have predicates: "paper_R_in_language (paper_R_henkin_signature \<Sigma> G k) G (snd i) (Arr (fst i) Prop)"
    if "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" for i
    by (rule paper_R_henkin_stage_index_language[OF that])
  have closed: "named_fv (snd i) = {}" if "i \<in> paper_R_henkin_stage_indices \<Sigma> G k" for i
    by (rule paper_R_henkin_stage_index_closed[OF that])
  show ?case by (simp only: paper_R_henkin_signature_family paper_R_henkin_premises.simps paper_R_henkin_stage_axioms_def;
    rule paper_R_witness_family_closed_theory[OF rich Suc.IH predicates closed])
qed

end
