theory Bacon_Book_ZF_Logical_Future_Results
  imports Bacon_Book_ZF_Equality_Future_Value
begin

context book_full_C_canonical_frame
begin

lemma full_ZF_implication_value_type:
  "w \<in> worlds \<Longrightarrow> full_ZF_logical_value w SImp \<in> explode (full_ZF_D (Arr Prop (Arr Prop Prop)) w)"
  using full_ZF_logical_value_type[where l=SImp] by (simp only: book_minimal_logical_type.simps)

lemma full_ZF_forall_value_type:
  "w \<in> worlds \<Longrightarrow> full_ZF_logical_value w (SBAll \<sigma>) \<in> explode (full_ZF_D (Arr (Arr \<sigma> Prop) Prop) w)"
  using full_ZF_logical_value_type[where l="SBAll \<sigma>"] by (simp only: book_minimal_logical_type.simps)

lemma full_ZF_implication_value_natural:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
    full_ZF_i (Arr Prop (Arr Prop Prop)) w v (full_ZF_logical_value w SImp) = full_ZF_logical_value v SImp"
  using full_ZF_logical_value_natural[where l=SImp] by (simp only: book_minimal_logical_type.simps)

lemma full_ZF_forall_value_natural:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
    full_ZF_i (Arr (Arr \<sigma> Prop) Prop) w v (full_ZF_logical_value w (SBAll \<sigma>)) = full_ZF_logical_value v (SBAll \<sigma>)"
  using full_ZF_logical_value_natural[where l="SBAll \<sigma>"] by (simp only: book_minimal_logical_type.simps)

theorem full_ZF_implication_result:
  assumes ww: "w \<in> worlds" and pm: "p \<in> explode (full_ZF_D Prop w)" and qm: "q \<in> explode (full_ZF_D Prop w)"
  shows "full_ZF_app w Prop Prop (full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p) q =
    full_ZF_future_collect w (\<lambda>v. \<not> Elem (book_ZF_world_code v) p \<or> Elem (book_ZF_world_code v) q)"
proof -
  let ?I = "full_ZF_logical_value w SImp"
  let ?F = "full_ZF_app w Prop (Arr Prop Prop) ?I p"
  let ?r = "full_ZF_app w Prop Prop ?F q"
  have ft: "?F \<in> explode (full_ZF_D (Arr Prop Prop) w)" by (rule full_ZF_app_type[OF ww full_ZF_implication_value_type[OF ww] pm])
  have rt: "?r \<in> explode (full_ZF_D Prop w)" by (rule full_ZF_app_type[OF ww ft qm])
  show ?thesis
  proof (rule full_ZF_proposition_eq_collect[OF rt])
    fix v
    assume vw: "v \<in> worlds" and access: "le w v"
    have pv: "full_ZF_i Prop w v p \<in> explode (full_ZF_D Prop v)" by (rule full_ZF_i_type[OF ww vw access pm])
    have qv: "full_ZF_i Prop w v q \<in> explode (full_ZF_D Prop v)" by (rule full_ZF_i_type[OF ww vw access qm])
    have natural: "full_ZF_i Prop w v ?r =
      full_ZF_app v Prop Prop (full_ZF_app v Prop (Arr Prop Prop) (full_ZF_logical_value v SImp)
        (full_ZF_i Prop w v p)) (full_ZF_i Prop w v q)"
      by (simp only: full_ZF_app_natural[OF ww vw access ft qm]
        full_ZF_app_natural[OF ww vw access full_ZF_implication_value_type[OF ww] pm]
        full_ZF_implication_value_natural[OF ww vw access])
    have truth: "full_ZF_value_truth v (full_ZF_i Prop w v ?r) =
      (full_ZF_value_truth v (full_ZF_i Prop w v p) \<longrightarrow> full_ZF_value_truth v (full_ZF_i Prop w v q))"
      by (simp only: natural; rule full_ZF_implication_truth[OF vw pv qv])
    show "Elem (book_ZF_world_code v) ?r = (\<not> Elem (book_ZF_world_code v) p \<or> Elem (book_ZF_world_code v) q)"
      using truth by (simp only: full_ZF_proposition_future_truth[OF ww vw access rt]
        full_ZF_proposition_future_truth[OF ww vw access pm] full_ZF_proposition_future_truth[OF ww vw access qm]; blast)
  qed
qed

theorem full_ZF_forall_result:
  assumes ww: "w \<in> worlds" and fm: "f \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
  shows "full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f =
    full_ZF_future_collect w (\<lambda>v. \<forall>a\<in>explode (full_ZF_D \<sigma> v).
      Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a)))"
proof -
  let ?r = "full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f"
  have rt: "?r \<in> explode (full_ZF_D Prop w)"
    by (rule full_ZF_app_type[OF ww full_ZF_forall_value_type[OF ww] fm])
  show ?thesis
  proof (rule full_ZF_proposition_eq_collect[OF rt])
    fix v
    assume vw: "v \<in> worlds" and access: "le w v"
    let ?F = "full_ZF_i (Arr \<sigma> Prop) w v f"
    have fv: "?F \<in> explode (full_ZF_D (Arr \<sigma> Prop) v)" by (rule full_ZF_i_type[OF ww vw access fm])
    have natural: "full_ZF_i Prop w v ?r = full_ZF_app v (Arr \<sigma> Prop) Prop (full_ZF_logical_value v (SBAll \<sigma>)) ?F"
      by (simp only: full_ZF_app_natural[OF ww vw access full_ZF_forall_value_type[OF ww] fm]
        full_ZF_forall_value_natural[OF ww vw access])
    have tests: "(\<forall>a\<in>explode (full_ZF_D \<sigma> v). full_ZF_value_truth v (full_ZF_app v \<sigma> Prop ?F a)) =
      (\<forall>a\<in>explode (full_ZF_D \<sigma> v). Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a)))"
    proof (rule ball_cong[OF refl])
      fix a
      assume am: "a \<in> explode (full_ZF_D \<sigma> v)"
      show "full_ZF_value_truth v (full_ZF_app v \<sigma> Prop ?F a) =
        Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a))"
        by (simp only: full_ZF_future_application[OF ww vw access fm am] full_ZF_value_truth_def)
    qed
    have truth: "full_ZF_value_truth v (full_ZF_i Prop w v ?r) =
      (\<forall>a\<in>explode (full_ZF_D \<sigma> v). Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a)))"
      by (simp only: natural full_ZF_forall_truth[OF vw fv] tests)
    show "Elem (book_ZF_world_code v) ?r =
      (\<forall>a\<in>explode (full_ZF_D \<sigma> v). Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a)))"
      using truth by (simp only: full_ZF_proposition_future_truth[OF ww vw access rt])
  qed
qed

end

text \<open>
  Each actual primitive result is identified with its entire future
  truth set. Naturality moves the result to each future world, where
  the all-domain truth clause applies. For ∀σ, future evaluation of f
  is identified with evaluation of its restriction. The result sets
  already belong to Dᵗ by actual application closure; membership is
  not inferred merely from being subsets of the future.
\<close>

end
