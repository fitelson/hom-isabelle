theory Bacon_Book_ZF_Actual_Identity
  imports Bacon_Book_ZF_General_Model
    Bacon_Book_Modal_Representation.Bacon_Book_Term_Actual_Identity
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_leibniz_h_iff:
  assumes ww: "w \<in> worlds"
    and xm: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
    and ym: "Y \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_leibniz_equiv (\<lambda>\<tau>. explode (full_ZF_D \<tau> w)) (full_ZF_app w) (full_ZF_value_truth w)
      \<sigma> (full_ZF_h \<sigma> w X) (full_ZF_h \<sigma> w Y) =
    book_leibniz_equiv (book_C_identity_domain (fst w) G (snd w))
      (book_C_term_app (fst w) G (snd w)) (book_C_term_valuation (snd w)) \<sigma> X Y"
proof -
  let ?D = "book_C_identity_domain (fst w) G (snd w)"
  let ?app = "book_C_term_app (fst w) G (snd w)"
  let ?V = "book_C_term_valuation (snd w)"
  have tests: "(\<forall>f\<in>explode (full_ZF_D (Arr \<sigma> Prop) w).
      full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f (full_ZF_h \<sigma> w X)) =
      full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f (full_ZF_h \<sigma> w Y))) =
    (\<forall>F\<in>?D (Arr \<sigma> Prop). ?V (?app \<sigma> Prop F X) = ?V (?app \<sigma> Prop F Y))"
  proof (simp only: full_ZF_D_elements ball_simps(9), rule ball_cong[OF refl])
    fix F
    assume fm: "F \<in> ?D (Arr \<sigma> Prop)"
    show "(full_ZF_value_truth w (full_ZF_app w \<sigma> Prop (full_ZF_h (Arr \<sigma> Prop) w F) (full_ZF_h \<sigma> w X)) =
      full_ZF_value_truth w (full_ZF_app w \<sigma> Prop (full_ZF_h (Arr \<sigma> Prop) w F) (full_ZF_h \<sigma> w Y))) =
      (?V (?app \<sigma> Prop F X) = ?V (?app \<sigma> Prop F Y))"
      by (simp only: full_ZF_app_h[OF ww fm xm] full_ZF_app_h[OF ww fm ym] full_ZF_h_proposition_truth[OF ww])
  qed
  show ?thesis unfolding book_leibniz_equiv_def
    using tests full_ZF_h_type[OF xm] full_ZF_h_type[OF ym] xm ym by blast
qed

theorem full_ZF_leibniz_iff_equal:
  assumes ww: "w \<in> worlds" and am: "a \<in> explode (full_ZF_D \<sigma> w)"
    and bm: "b \<in> explode (full_ZF_D \<sigma> w)"
  shows "book_leibniz_equiv (\<lambda>\<tau>. explode (full_ZF_D \<tau> w)) (full_ZF_app w) (full_ZF_value_truth w)
    \<sigma> a b \<longleftrightarrow> a = b"
proof -
  let ?X = "full_ZF_j \<sigma> w a"
  let ?Y = "full_ZF_j \<sigma> w b"
  have xm: "?X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF am])
  have ym: "?Y \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>" by (rule full_ZF_j_type[OF bm])
  have source: "book_leibniz_equiv (\<lambda>\<tau>. explode (full_ZF_D \<tau> w)) (full_ZF_app w) (full_ZF_value_truth w)
    \<sigma> a b \<longleftrightarrow> ?X = ?Y"
    using full_ZF_leibniz_h_iff[OF ww xm ym]
    by (simp only: full_ZF_hj[OF am] full_ZF_hj[OF bm] full_term_leibniz_iff_equal[OF ww xm ym])
  have equal: "?X = ?Y \<longleftrightarrow> a = b"
  proof
    assume same: "?X = ?Y"
    have "full_ZF_h \<sigma> w ?X = full_ZF_h \<sigma> w ?Y" by (simp only: same)
    then show "a = b" by (simp only: full_ZF_hj[OF am] full_ZF_hj[OF bm])
  next
    assume "a = b"
    then show "?X = ?Y" by simp
  qed
  show ?thesis by (simp only: source equal)
qed

theorem full_ZF_identity_truth:
  assumes ww: "w \<in> worlds"
    and al: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<sigma>"
    and cl: "book_in_language book_minimal_logical_type UNIV (fst w) G C \<sigma>"
    and typed: "book_env_typed (\<lambda>\<tau>. explode (full_ZF_D \<tau> w)) G g"
  shows "full_ZF_value_truth w (full_ZF_denote w g (book_leibniz G \<sigma> A C)) =
    (full_ZF_denote w g A = full_ZF_denote w g C)"
proof -
  interpret M: book_full_minimal_model "\<lambda>\<tau>. explode (full_ZF_D \<tau> w)" "full_ZF_app w"
    "fst w" G "full_ZF_denote w" "full_ZF_value_truth w" "full_ZF_logical_value w"
    by (rule full_ZF_general_model[OF ww])
  have am: "full_ZF_denote w g A \<in> explode (full_ZF_D \<sigma> w)" by (rule full_ZF_denote_type[OF ww al typed])
  have cm: "full_ZF_denote w g C \<in> explode (full_ZF_D \<sigma> w)" by (rule full_ZF_denote_type[OF ww cl typed])
  show ?thesis by (simp only: M.book_leibniz_truth[OF rich typed al cl] full_ZF_leibniz_iff_equal[OF ww am cm])
qed

end

text \<open>
  All represented predicate tests are h-images of source predicates.
  Application and truth preservation therefore transfer Leibniz
  equivalence exactly. The proved source separation and the inverse
  maps identify it with equality in every Dσ. The literal Leibniz
  formula consequently expresses actual equality under every typed
  assignment. None of these conclusions is an added model axiom.
\<close>

end
