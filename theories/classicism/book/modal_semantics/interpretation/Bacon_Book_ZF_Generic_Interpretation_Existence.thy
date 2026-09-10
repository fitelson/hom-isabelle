theory Bacon_Book_ZF_Generic_Interpretation_Existence
  imports Bacon_Book_ZF_Generic_Abstraction Bacon_Book_ZF_Model_Interpretation_Uniqueness
begin

section \<open>Existence of the interpretation for every independent modal model\<close>

context book_ZF_modal_model
begin

definition generic_interpretation where
  "generic_interpretation G w g A =
    generic_comb_eval G w g (book_combinatory_translation G A)"

theorem generic_interpretation_model:
  "book_ZF_modal_interpretation W R root D i signature I G (generic_interpretation G)"
  unfolding generic_interpretation_def
proof (rule book_ZF_modal_interpretation.intro[OF book_ZF_modal_model_axioms],
    rule book_ZF_modal_interpretation_axioms.intro)
  fix w g A \<tau>
  assume ww: "w \<in> explode W"
    and language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G A) \<in> explode (D \<tau> w)"
    by (rule generic_comb_eval_type[OF book_combinatory_translation_language[OF language] ww env])
next
  fix w g n
  assume "w \<in> explode W" "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G (NVar n)) = g n"
    by (simp only: book_combinatory_translation.simps generic_comb_eval.simps)
next
  fix w g c \<sigma>
  assume "w \<in> explode W" "c \<in> signature \<sigma>" "book_env_typed (\<lambda>\<tau>. explode (D \<tau> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G (NConst c \<sigma>)) = i \<sigma> root w (I c \<sigma>)"
    by (simp only: book_combinatory_translation.simps generic_comb_eval.simps)
next
  fix w g l
  assume "w \<in> explode W" "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G (NLogical l)) =
    i (book_minimal_logical_type l) root w (book_ZF_logical_root W R D i root l)"
    by (simp only: book_combinatory_translation.simps generic_comb_eval.simps)
next
  fix w g F A \<sigma> \<tau>
  assume "w \<in> explode W"
    "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>)"
    "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
    "book_env_typed (\<lambda>\<rho>. explode (D \<rho> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G (NApp F A)) =
    app (generic_comb_eval G w g (book_combinatory_translation G F))
      (Opair w (generic_comb_eval G w g (book_combinatory_translation G A)))"
    by (simp only: book_combinatory_translation.simps generic_comb_eval_apply)
next
  fix w g n A \<tau>
  assume ww: "w \<in> explode W"
    and language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  show "generic_comb_eval G w g (book_combinatory_translation G (NLam n A)) =
    Lambda (book_ZF_pairs W R (D (G n)) w)
      (\<lambda>p. generic_comb_eval G (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p))
        (book_combinatory_translation G A))"
    by (simp only: book_combinatory_translation.simps;
      rule generic_comb_abstract_graph[OF book_combinatory_translation_language[OF language] ww env])
qed

theorem generic_interpretation_exists:
  "\<exists>J. book_ZF_modal_interpretation W R root D i signature I G J"
  by (rule exI[where x="generic_interpretation G"]; rule generic_interpretation_model)

theorem generic_interpretation_natural:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "i \<tau> w v (generic_interpretation G w g A) =
    generic_interpretation G v (book_ZF_move i G w v g) A"
  unfolding generic_interpretation_def
  by (rule generic_comb_eval_natural[OF book_combinatory_translation_language[OF language] ww vw wv env])

end

text \<open>
  Every model satisfying the independent Definition 18.1 predicate has
  an interpretation satisfying all the independent Definition 17.13
  clauses. The explicit construction first eliminates abstraction using
  typed K/S combinators, and its value is proved equal to the required
  future Lambda graph. No supplied interpreter, canonical construction,
  countability, rich variable stock, full function space or additional
  domain-nonemptiness premise is used. Typing guards remain on assignments
  and terms; no behavior on inadmissible inputs is claimed to be unique.
  The existing future-restricted implication convention is unchanged.
  This is interpretation existence, not generic full-C soundness.
  Source: Definition 17.13 and the interpretation-existence component
  of Theorem 17.1, p.367, specialized to the full minimal language in
  the independently defined modal models of Definition 18.1.
\<close>

end
