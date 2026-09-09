theory Bacon_Book_ZF_Future_Abstraction
  imports Bacon_Book_ZF_Interpretation_Naturality
begin

section \<open>Abstraction denotes its function on every future world\<close>

context book_full_C_canonical_frame
begin

theorem full_ZF_denote_lambda_future:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
    and am: "a \<in> explode (full_ZF_D (G n) v)"
  shows "app (full_ZF_denote w g (NLam n A)) (Opair (book_ZF_world_code v) a) =
    full_ZF_denote v ((full_ZF_assignment_move w v g)(n := a)) A"
proof -
  interpret V: book_C_identity_world "fst v" G "snd v"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF vw]])
  let ?k = "full_ZF_assignment_decode w g"
  let ?h = "full_term_assignment_move w v ?k"
  let ?Jw = "book_C_term_denote (fst w) G (snd w)"
  let ?Jv = "book_C_term_denote (fst v) G (snd v)"
  have kt: "book_env_typed (book_C_identity_domain (fst w) G (snd w)) G ?k"
    by (rule full_ZF_assignment_decode_typed[OF typed])
  have ht: "book_env_typed (book_C_identity_domain (fst v) G (snd v)) G ?h"
    by (rule full_term_assignment_move_typed[OF ww vw access kt])
  have inclusion: "\<And>\<sigma>. fst w \<sigma> \<subseteq> fst v \<sigma>"
    by (rule book_C_canonical_le_language[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access])
  have target_language: "book_in_language book_minimal_logical_type UNIV (fst v) G A \<tau>"
    by (rule book_language_signature_mono[OF language inclusion])
  have lambda_language: "book_in_language book_minimal_logical_type UNIV (fst w) G (NLam n A) (Arr (G n) \<tau>)"
    by (rule book_language_Lam[OF language])
  have natural: "book_C_term_counterpart G w v (Arr (G n) \<tau>) (?Jw ?k (NLam n A)) = ?Jv ?h (NLam n A)"
    by (rule full_term_denote_natural[OF ww vw access lambda_language kt])
  have inverse: "full_ZF_j (G n) v a \<in> book_C_identity_domain (fst v) G (snd v) (G n)"
    by (rule full_ZF_j_type[OF am])
  have body: "book_C_term_app (fst v) G (snd v) (G n) \<tau> (?Jv ?h (NLam n A)) (full_ZF_j (G n) v a) =
    ?Jv (?h(n := full_ZF_j (G n) v a)) A"
    by (rule V.book_C_term_lambda_application[OF target_language ht inverse])
  show ?thesis by (simp only: full_ZF_denote_eq[OF book_language_type[OF lambda_language]]
    full_ZF_denote_eq[OF book_language_type[OF language]]
    full_ZF_arrow_value[OF vw access am] natural body
    full_ZF_assignment_decode_update full_ZF_assignment_decode_move[OF ww vw access typed])
qed

theorem full_ZF_denote_lambda_homomorphism:
  assumes ww: "w \<in> worlds"
    and language: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<tau>"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) G g"
  shows "full_ZF_arrow_decode (G n) w (full_ZF_denote w g (NLam n A)) \<in>
    book_modalized_exponential worlds le (\<lambda>v. explode (full_ZF_D (G n) v)) (full_ZF_i (G n))
      (\<lambda>v. explode (full_ZF_D \<tau> v)) (full_ZF_i \<tau>) w"
  by (rule full_ZF_arrow_domain_homomorphisms[OF ww
    full_ZF_denote_type[OF ww book_language_Lam[OF language] typed]])

end

text \<open>
  The value of λn.A at w sends every admissible future pair (v,a)
  to the value of A at v under the transported assignment updated
  with a. Naturality of the term interpretation moves the abstraction
  to v; its ordinary abstraction equation then evaluates it. Both
  steps are proved for the actual canonical interpretation.

  The result is a genuine future homomorphism in the represented
  function domain, not merely a function at the present world.
  Primitive truth clauses and the complete Definition 18.1 model
  certificate remain separate; no modal-model premise is used here.
\<close>

end
