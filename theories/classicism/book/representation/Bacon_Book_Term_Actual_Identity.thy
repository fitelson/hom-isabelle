theory Bacon_Book_Term_Actual_Identity
  imports Bacon_Book_Term_General_Model
begin

section \<open>Leibniz equivalence is actual identity in the canonical term domains\<close>

context book_full_C_canonical_frame
begin

theorem full_term_leibniz_iff_equal:
  assumes ww: "w \<in> worlds"
    and xm: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
    and ym: "Y \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_leibniz_equiv (book_C_identity_domain (fst w) G (snd w))
    (book_C_term_app (fst w) G (snd w)) (book_C_term_valuation (snd w)) \<sigma> X Y \<longleftrightarrow> X = Y"
proof -
  let ?D = "book_C_identity_domain (fst w) G (snd w)"
  let ?app = "book_C_term_app (fst w) G (snd w)"
  let ?J = "book_C_term_denote (fst w) G (snd w)"
  let ?V = "book_C_term_valuation (snd w)"
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  interpret M: book_full_minimal_model ?D ?app "fst w" G ?J ?V "book_C_term_logical_value (fst w) G (snd w)"
    by (rule full_term_general_model[OF ww])
  obtain g where typed: "book_env_typed ?D G g" using M.book_minimal_assignment_exists by blast
  let ?A = "book_C_identity_rep X"
  let ?C = "book_C_identity_rep Y"
  let ?E = "book_leibniz G \<sigma> ?A ?C"
  have am: "?A \<in> book_closed_terms (fst w) G \<sigma>" by (rule T.identity_rep_typed[OF xm])
  have cm: "?C \<in> book_closed_terms (fst w) G \<sigma>" by (rule T.identity_rep_typed[OF ym])
  have al: "book_in_language book_minimal_logical_type UNIV (fst w) G ?A \<sigma>" by (rule book_closed_terms_language[OF am])
  have cl: "book_in_language book_minimal_logical_type UNIV (fst w) G ?C \<sigma>" by (rule book_closed_terms_language[OF cm])
  have ac: "named_fv ?A = {}" by (rule book_closed_terms_closed[OF am])
  have cc: "named_fv ?C = {}" by (rule book_closed_terms_closed[OF cm])
  have ax: "?J g ?A = X" by (simp only: T.book_C_term_denote_closed[OF al ac]; rule T.identity_rep_class[OF xm])
  have cy: "?J g ?C = Y" by (simp only: T.book_C_term_denote_closed[OF cl cc]; rule T.identity_rep_class[OF ym])
  have el: "book_theory_formula (fst w) G ?E" by (rule book_leibniz_language[OF rich al cl])
  have ec: "named_fv ?E = {}" by (simp only: book_leibniz_fv ac cc Un_empty)
  have em: "?E \<in> book_closed_terms (fst w) G Prop" by (rule book_closed_termsI[OF el ec])
  have truth: "?V (?J g ?E) \<longleftrightarrow> ?E \<in> snd w"
    by (simp only: T.book_C_term_denote_closed[OF el ec] T.term_valuation_class[OF em])
  have classes: "?E \<in> snd w \<longleftrightarrow> X = Y"
    using T.identity_class_eq_iff[OF am cm]
    by (simp only: T.identity_rep_class[OF xm] T.identity_rep_class[OF ym])
  have semantic: "?V (?J g ?E) = book_leibniz_equiv ?D ?app ?V \<sigma> X Y"
    by (simp only: M.book_leibniz_truth[OF rich typed al cl] ax cy)
  show ?thesis using truth classes semantic by blast
qed

end

text \<open>
  Choose closed representatives A,C of X,Y. In the actual term
  general model, the formula A=σC expresses semantic Leibniz
  equivalence. Its characteristic truth is membership in w, which
  the identity-class equality theorem identifies with X=Y.
  All three links are proved; no separation or actual-identity
  clause is assumed of the general-model interface.
\<close>

end
