theory Bacon_Book_Term_General_Model
  imports Bacon_Book_Term_Logical_Clauses
begin

section \<open>The canonical term structure at each world as a general model\<close>

context book_C_identity_world
begin

theorem term_full_minimal_model:
  assumes witnesses: "book_closed_constant_witness_complete \<Sigma> G w"
    and nonempty: "\<And>\<sigma>. book_C_identity_domain \<Sigma> G w \<sigma> \<noteq> {}"
  shows "book_full_minimal_model (book_C_identity_domain \<Sigma> G w)
    (book_C_term_app \<Sigma> G w) \<Sigma> G (book_C_term_denote \<Sigma> G w)
    (book_C_term_valuation w) (book_C_term_logical_value \<Sigma> G w)"
proof -
  let ?D = "book_C_identity_domain \<Sigma> G w"
  let ?app = "book_C_term_app \<Sigma> G w"
  let ?J = "book_C_term_denote \<Sigma> G w"
  let ?V = "book_C_term_valuation w"
  let ?k = "book_C_term_logical_value \<Sigma> G w"
  interpret E: book_full_environment ?D ?app book_minimal_logical_type UNIV \<Sigma> G ?J
    by (rule book_C_term_full_environment)
  obtain g where typed: "book_env_typed ?D G g"
    using book_total_assignment_exists[where D="?D" and G=G, OF nonempty] by blast
  have logicals: "E.book_closed_value (book_minimal_logical_type l) (NLogical l) (?k l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    have evaluated: "?J g (NLogical l) = ?k l"
      unfolding book_C_term_logical_value_def by (rule book_C_term_denote_closed[OF language closed])
    show ?thesis using E.book_closed_value_intro[OF UNIV_I language closed typed] by (simp only: evaluated)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def, rule conjI[OF E.book_full_environment_axioms], unfold_locales)
    fix l
    show "E.book_closed_value (book_minimal_logical_type l) (NLogical l) (?k l)" by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> ?D Prop" and qm: "q \<in> ?D Prop"
    show "?V (?app Prop Prop (?app Prop (Arr Prop Prop) (?k SImp) p) q) = (?V p \<longrightarrow> ?V q)"
      by (rule term_implication_truth[OF pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> ?D (Arr \<sigma> Prop)"
    show "?V (?app (Arr \<sigma> Prop) Prop (?k (SBAll \<sigma>)) f) = (\<forall>a\<in>?D \<sigma>. ?V (?app \<sigma> Prop f a))"
      by (rule term_forall_truth[OF witnesses fm])
  next
    have member: "book_C_identity_class \<Sigma> G w Prop (book_bottom G) \<in> ?D Prop"
      by (rule book_C_identity_domainI[OF book_closed_termsI[OF book_bottom_language[OF rich] book_bottom_closed]])
    show "\<exists>f\<in>?D Prop. \<not> ?V f"
      by (rule bexI[where x="book_C_identity_class \<Sigma> G w Prop (book_bottom G)"];
        rule term_valuation_bottom member)
  qed
qed

end

context book_full_C_canonical_frame
begin

theorem full_term_general_model:
  assumes ww: "w \<in> worlds"
  shows "book_full_minimal_model (book_C_identity_domain (fst w) G (snd w))
    (book_C_term_app (fst w) G (snd w)) (fst w) G (book_C_term_denote (fst w) G (snd w))
    (book_C_term_valuation (snd w)) (book_C_term_logical_value (fst w) G (snd w))"
proof -
  have wf: "w \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF ww])
  interpret T: book_C_identity_world "fst w" G "snd w" by (rule book_full_C_world_identity_algebra[OF rich wf])
  have witnesses: "book_closed_constant_witness_complete (fst w) G (snd w)"
    by (rule book_full_C_canonical_world_data(5)[OF wf])
  have nonempty: "\<And>\<sigma>. book_C_identity_domain (fst w) G (snd w) \<sigma> \<noteq> {}"
    by (rule book_full_C_canonical_identity_domain_nonempty[OF rich wf])
  show ?thesis by (rule T.term_full_minimal_model[OF witnesses nonempty])
qed

end

text \<open>
  This is the general-model view of the same canonical term structure,
  not a replacement for its modal representation. Every model field is
  discharged from the actual interpretation, closed maximality,
  witnesses and domain inhabitation. The false proposition is displayed.
  At an actual full-C world the last two prerequisites are theorems.
  This does not yet certify the represented modal model or C completeness.
\<close>

end
