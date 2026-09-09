theory Bacon_Book_Classicism_Henkin_Stages
  imports Bacon_Book_Classicism_Infinite_Witness_Family Bacon_Book_Classicism_Theory_Renaming
    Bacon_Book_Environment_Development.Bacon_Book_Henkin_Premise_Stages
begin

section \<open>Each actual Henkin stage preserves the changing C theory\<close>

theorem book_C_henkin_stage_consistent:
  assumes rich: "sg_rich G"
    and consistent: "book_C_theory_consistent (book_henkin_signature \<Sigma> G n) G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow>
      book_theory_formula (book_henkin_signature \<Sigma> G n) G A"
  shows "book_C_theory_consistent (book_henkin_signature \<Sigma> G (Suc n)) G
    (S \<union> book_henkin_stage_axioms \<Sigma> G n)"
proof -
  let ?I = "book_henkin_stage_indices \<Sigma> G n"
  let ?c = "book_henkin_stage_name n"
  have predicates: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G n) G (snd i) (Arr (fst i) Prop)"
    if "i \<in> ?I" for i
    by (rule book_henkin_stage_index_language[OF that])
  have closed: "named_fv (snd i) = {}" if "i \<in> ?I" for i
    by (rule book_henkin_stage_index_closed[OF that])
  have fresh: "?c i \<notin> book_henkin_signature \<Sigma> G n (fst i)" if "i \<in> ?I" for i
    by (rule book_henkin_stage_name_fresh)
  have injective: "inj_on ?c ?I" by (rule book_henkin_stage_name_inj_on)
  have family: "book_C_theory_consistent
      (book_witness_family_signature (book_henkin_signature \<Sigma> G n) fst ?c ?I) G
      (S \<union> book_witness_family_axioms G fst snd ?c ?I)"
    by (rule book_C_consistent_witness_family[where \<Sigma>="book_henkin_signature \<Sigma> G n"
      and G=G and S=S and \<tau>=fst and F=snd and c="?c" and I="?I",
      OF rich consistent language predicates closed fresh injective])
  show ?thesis using family
    by (simp only: book_henkin_signature_family book_henkin_stage_axioms_def)
qed


theorem book_C_henkin_premises_consistent:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_C_theory_consistent \<Sigma> G S"
  shows "book_C_theory_consistent (book_henkin_signature \<Sigma> G n) G (book_henkin_premises \<Sigma> G S n)"
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  have initial: "book_C_theory_consistent (\<lambda>\<tau>. BookOriginal ` \<Sigma> \<tau>) G (book_constant_rename BookOriginal ` S)"
    by (rule iffD1[OF book_C_consistent_constant_rename_iff[
      where f=BookOriginal and \<Sigma>=\<Sigma> and G=G and S=S,
      OF rich book_henkin_original_injective language] consistent])
  show ?case using initial by (simp only: book_henkin_signature.simps book_henkin_premises.simps)
next
  case (Suc n)
  have stage_language: "book_theory_formula (book_henkin_signature \<Sigma> G n) G A"
    if "A \<in> book_henkin_premises \<Sigma> G S n" for A
    by (rule book_henkin_premises_language[OF rich language that])
  have next_stage: "book_C_theory_consistent (book_henkin_signature \<Sigma> G (Suc n)) G
    (book_henkin_premises \<Sigma> G S n \<union> book_henkin_stage_axioms \<Sigma> G n)"
    by (rule book_C_henkin_stage_consistent[where \<Sigma>=\<Sigma> and G=G and n=n
      and S="book_henkin_premises \<Sigma> G S n", OF rich Suc.IH stage_language])
  show ?case using next_stage by (simp only: book_henkin_premises.simps)
qed

text \<open>
  The existing datatype and signatures supply the witnesses; freshness
  and injectivity are proved properties, not new premises. Stage zero
  uses the checked C consistency transport to the Original-name image.
  Each later stage includes C of its own signature and all witnesses
  for closed predicates of the preceding language. The union and the
  eventual reserve are separate obligations.
\<close>

end

