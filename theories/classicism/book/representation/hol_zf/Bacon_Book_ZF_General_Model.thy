theory Bacon_Book_ZF_General_Model
  imports Bacon_Book_ZF_Primitive_Truth
begin

section \<open>Every represented world satisfies the general-model clauses\<close>

context book_full_C_canonical_frame
begin

theorem full_ZF_separated_environment:
  assumes ww: "w \<in> worlds"
  shows "book_environment_separated (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w))
    (full_ZF_app w) book_minimal_logical_type UNIV (fst w) G UNIV (full_ZF_denote w)"
  apply unfold_locales
       apply (rule full_ZF_app_type[OF ww]; assumption)
      apply (rule full_ZF_denote_type[OF ww]; assumption)
     apply (rule full_ZF_denote_var[OF ww]; assumption)
    apply (unfold full_ZF_app_def; rule full_ZF_denote_app[OF ww]; assumption)
   apply (rule full_ZF_denote_locality; assumption)
  apply (rule full_ZF_denote_conversion[OF ww]; assumption)
  done

theorem full_ZF_full_environment:
  assumes ww: "w \<in> worlds"
  shows "book_full_environment (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w))
    (full_ZF_app w) book_minimal_logical_type UNIV (fst w) G (full_ZF_denote w)"
proof -
  interpret S: book_environment_separated "\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)"
    "full_ZF_app w" book_minimal_logical_type UNIV "fst w" G UNIV "full_ZF_denote w"
    by (rule full_ZF_separated_environment[OF ww])
  interpret E: book_environment_conditions "\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)"
    "full_ZF_app w" book_minimal_logical_type UNIV "fst w" G UNIV "full_ZF_denote w"
    by (rule S.book_separated_to_environment)
  show ?thesis by unfold_locales
qed

theorem full_ZF_false_proposition:
  assumes ww: "w \<in> worlds"
  shows "\<exists>p\<in>explode (full_ZF_D Prop w). \<not> full_ZF_value_truth w p"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?X = "book_C_identity_class (fst w) G (snd w) Prop (book_bottom G)"
  have source: "?X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
    by (rule book_C_identity_domainI[OF book_closed_termsI[OF book_bottom_language[OF rich] book_bottom_closed]])
  have member: "full_ZF_h Prop w ?X \<in> explode (full_ZF_D Prop w)" by (rule full_ZF_h_type[OF source])
  have false_value: "\<not> full_ZF_value_truth w (full_ZF_h Prop w ?X)"
    by (simp only: full_ZF_h_proposition_truth[OF ww]; rule T.term_valuation_bottom)
  show ?thesis by (rule bexI[where x="full_ZF_h Prop w ?X"]; rule false_value member)
qed

theorem full_ZF_general_model:
  assumes ww: "w \<in> worlds"
  shows "book_full_minimal_model (\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)) (full_ZF_app w)
    (fst w) G (full_ZF_denote w) (full_ZF_value_truth w) (full_ZF_logical_value w)"
proof -
  let ?D = "\<lambda>\<sigma>. explode (full_ZF_D \<sigma> w)"
  interpret E: book_full_environment ?D "full_ZF_app w" book_minimal_logical_type UNIV "fst w" G "full_ZF_denote w"
    by (rule full_ZF_full_environment[OF ww])
  obtain g where typed: "book_env_typed ?D G g"
    using book_total_assignment_exists[where D="?D" and G=G, OF full_ZF_domains_nonempty[OF ww]] by blast
  have logicals: "E.book_closed_value (book_minimal_logical_type l) (NLogical l) (full_ZF_logical_value w l)" for l
  proof -
    have language: "book_in_language book_minimal_logical_type UNIV (fst w) G (NLogical l) (book_minimal_logical_type l)"
      by (rule book_language_Logical[OF UNIV_I])
    have closed: "named_fv (NLogical l) = {}" by simp
    show ?thesis using E.book_closed_value_intro[OF UNIV_I language closed typed]
      by (simp only: full_ZF_logical_denote)
  qed
  show ?thesis
  proof (unfold book_full_minimal_model_def, rule conjI[OF E.book_full_environment_axioms], unfold_locales)
    fix l
    show "E.book_closed_value (book_minimal_logical_type l) (NLogical l) (full_ZF_logical_value w l)" by (rule logicals)
  next
    fix p q
    assume pm: "p \<in> ?D Prop" and qm: "q \<in> ?D Prop"
    show "full_ZF_value_truth w (full_ZF_app w Prop Prop
      (full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p) q) =
      (full_ZF_value_truth w p \<longrightarrow> full_ZF_value_truth w q)"
      by (rule full_ZF_implication_truth[OF ww pm qm])
  next
    fix \<sigma> f
    assume fm: "f \<in> ?D (Arr \<sigma> Prop)"
    show "full_ZF_value_truth w (full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f) =
      (\<forall>a\<in>?D \<sigma>. full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f a))"
      by (rule full_ZF_forall_truth[OF ww fm])
  next
    show "\<exists>p\<in>?D Prop. \<not> full_ZF_value_truth w p" by (rule full_ZF_false_proposition[OF ww])
  qed
qed

end

text \<open>
  This certificate checks every independent full minimal general-model
  field for the actual represented data at w, including witnessed
  logical denotations and a false proposition. The previously proved
  cross-world naturality and future abstraction laws still belong to
  the same data. A family of per-world general models is not silently
  promoted to the complete modal model of Definition 18.1; its literal
  function-space/logical-operation conditions and the final
  soundness/completeness statements remain separate obligations.
\<close>

end
