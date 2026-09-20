theory Goodman_Vector_Translation
  imports Goodman_Vector_Charts
begin

definition gi_order where "gi_order b xs = (if b then rev xs else xs)"
lemma gi_map_rev: "map f (rev xs) = rev (map f xs)"
  by (induction xs) simp_all
definition gi_vec_body where
  "gi_vec_body b \<Delta> F H =
    (app_vec (shift_by (length \<Delta>) F) (gi_order b (fresh_vars (length \<Delta>)))
      \<longleftrightarrow>\<^sub>o
     app_vec (shift_by (length \<Delta>) H) (gi_order b (fresh_vars (length \<Delta>))))"

lemma gi_ordered_arguments:
  "map (gi_to_book G (ps @ ns) k) (gi_order b (fresh_vars (length ps))) = map NVar (gi_order b ps)"
  by (cases b) (simp_all add: gi_order_def gi_map_rev gi_translate_fresh_vars)

lemma gi_ordered_application_alpha:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> F : \<tau>"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct (ps @ ns)"
  shows "named_alpha G
    (gi_to_book G (ps @ ns) k (app_vec (shift_by (length ps) F) (gi_order b (fresh_vars (length ps)))))
    (book_vector_application (gi_to_book G ns k F) (gi_order b ps))"
  using gi_alpha_fold_app[OF gi_shift_by_prefix_alpha[OF rich typed chart distinct],
    where As="map NVar (gi_order b ps)"]
  by (simp only: gi_translate_app_vec gi_ordered_arguments book_vector_application_def)

lemma gi_book_vector_language:
  assumes head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G vs) \<tau>)"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_vector_application R vs) \<tau>"
  using head
proof (induction vs arbitrary: R)
  case Nil
  then show ?case by (simp add: book_vector_application_def)
next
  case (Cons n vs)
  have app: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NApp R (NVar n)) (foldr Arr (map G vs) \<tau>)"
    by (rule book_language_App[OF Cons.prems[simplified] book_language_Var])
  show ?case using Cons.IH[OF app] by (simp add: book_vector_application_def)
qed

theorem gi_ordered_vector_rule:
  assumes rich: "sg_rich G"
    and f: "\<Gamma> \<turnstile> F : arrow_type (gi_order b \<Delta>) Prop"
    and h: "\<Gamma> \<turnstile> H : arrow_type (gi_order b \<Delta>) Prop"
    and chart: "map G ns = \<Gamma>" and distinct: "distinct ns"
    and fc: "gi_constants_admitted k \<Sigma> F" and hc: "gi_constants_admitted k \<Sigma> H"
    and premise: "goodman_book_proves \<Sigma> G T
      (gi_to_book G (gi_prefix G \<Delta> ns @ ns) k (gi_vec_body b \<Delta> F H))"
  shows "goodman_book_proves \<Sigma> G T
    (gi_to_book G ns k (Eq (arrow_type (gi_order b \<Delta>) Prop) F H))"
proof -
  let ?ps = "gi_prefix G \<Delta> ns"
  let ?vs = "gi_order b ?ps"
  let ?F = "gi_to_book G ns k F"
  let ?H = "gi_to_book G ns k H"
  let ?FA = "book_vector_application ?F ?vs"
  let ?HA = "book_vector_application ?H ?vs"
  have d: "distinct (?ps @ ns)" by (rule gi_prefix_distinct[OF rich distinct])
  have order_type: "foldr Arr (map G ?vs) Prop = arrow_type (gi_order b \<Delta>) Prop"
    by (simp add: gi_order_def gi_map_rev gi_prefix_types[OF rich] gi_arrow_fold)
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?F (foldr Arr (map G ?vs) Prop)"
    unfolding order_type by (rule gi_to_book_language[OF rich f chart fc])
  have hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?H (foldr Arr (map G ?vs) Prop)"
    unfolding order_type by (rule gi_to_book_language[OF rich h chart hc])
  have fresh: "set ?vs \<inter> (named_fv ?F \<union> named_fv ?H) = {}"
    using d gi_to_book_fv_subset[OF rich f chart, where k=k]
      gi_to_book_fv_subset[OF rich h chart, where k=k]
    by (auto simp: gi_order_def)
  have vd: "distinct ?vs" using d by (simp add: gi_order_def)
  have instance_ok: "book_equivalence_rule_instance \<Sigma> G ?vs ?F ?H"
    using vd fresh fl hl unfolding book_equivalence_rule_instance_def by blast
  have af: "named_alpha G
    (gi_to_book G (?ps @ ns) k (app_vec (shift_by (length \<Delta>) F) (gi_order b (fresh_vars (length \<Delta>))))) ?FA"
    using gi_ordered_application_alpha[OF rich f chart d, where b=b and k=k] by simp
  have ah: "named_alpha G
    (gi_to_book G (?ps @ ns) k (app_vec (shift_by (length \<Delta>) H) (gi_order b (fresh_vars (length \<Delta>))))) ?HA"
    using gi_ordered_application_alpha[OF rich h chart d, where b=b and k=k] by simp
  have alpha: "named_alpha G (gi_to_book G (?ps @ ns) k (gi_vec_body b \<Delta> F H))
    (book_and G (book_imp ?FA ?HA) (book_imp ?HA ?FA))"
    unfolding gi_vec_body_def gi_to_book.simps by (rule gi_alpha_expanded_iff[OF af ah])
  have expanded: "goodman_book_proves \<Sigma> G T (book_and G (book_imp ?FA ?HA) (book_imp ?HA ?FA))"
    by (rule gi_goodman_alpha_transport[OF rich alpha premise])
  have fal: "book_theory_formula \<Sigma> G ?FA" by (rule gi_book_vector_language[OF fl])
  have hal: "book_theory_formula \<Sigma> G ?HA" by (rule gi_book_vector_language[OF hl])
  have certificate: "goodman_book_proves \<Sigma> G T
    (book_imp (book_and G (book_imp ?FA ?HA) (book_imp ?HA ?FA)) (book_iff G ?FA ?HA))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule gi_H_expanded_iff_to_book[OF rich fal hal])
  have equivalent: "goodman_book_proves \<Sigma> G T (book_iff G ?FA ?HA)"
    by (rule goodman_book_proves.MP[OF expanded certificate book_iff_language[OF rich fal hal]])
  have identity: "goodman_book_proves \<Sigma> G T (book_leibniz G (foldr Arr (map G ?vs) Prop) ?F ?H)"
    by (rule gi_goodman_vector_equivalence[OF rich instance_ok equivalent])
  show ?thesis using identity by (simp only: order_type gi_to_book.simps)
qed

lemma gi_zeta_body_order:
  "zeta_body \<Delta> F H = gi_vec_body False \<Delta> F H"
  by (simp add: zeta_body_def gi_vec_body_def gi_order_def)

lemma gi_H_body_order:
  "H_rule_body \<Delta> F H = gi_vec_body True \<Delta> F H"
  by (simp add: H_rule_body_def H_rule_app_vec_bridge gi_H_rule_raise_shift H_rule_args_bridge
    gi_vec_body_def gi_order_def)

end
