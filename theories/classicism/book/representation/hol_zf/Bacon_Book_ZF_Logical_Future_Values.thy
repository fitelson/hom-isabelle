theory Bacon_Book_ZF_Logical_Future_Values
  imports Bacon_Book_ZF_Logical_Future_Results
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_implication_future_value:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and pm: "p \<in> explode (full_ZF_D Prop w)" and qm: "q \<in> explode (full_ZF_D Prop v)"
  shows "app (app (full_ZF_logical_value actual SImp) (Opair (book_ZF_world_code w) p)) (Opair (book_ZF_world_code v) q) =
    full_ZF_future_collect v (\<lambda>u. \<not> Elem (book_ZF_world_code u) (full_ZF_i Prop w v p) \<or> Elem (book_ZF_world_code u) q)"
proof -
  let ?F = "app (full_ZF_logical_value actual SImp) (Opair (book_ZF_world_code w) p)"
  have root: "actual \<in> worlds" by (rule book_full_C_root_is_world)
  have reach: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  have first: "?F = full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p"
    by (simp only: full_ZF_future_application[OF root ww reach full_ZF_implication_value_type[OF root] pm]
      full_ZF_implication_value_natural[OF root ww reach])
  have ft: "?F \<in> explode (full_ZF_D (Arr Prop Prop) w)"
    by (simp only: first; rule full_ZF_app_type[OF ww full_ZF_implication_value_type[OF ww] pm])
  have pv: "full_ZF_i Prop w v p \<in> explode (full_ZF_D Prop v)" by (rule full_ZF_i_type[OF ww vw access pm])
  have evaluated: "app ?F (Opair (book_ZF_world_code v) q) =
    full_ZF_app v Prop Prop (full_ZF_app v Prop (Arr Prop Prop) (full_ZF_logical_value v SImp) (full_ZF_i Prop w v p)) q"
    by (subst full_ZF_future_application[OF ww vw access ft qm]; simp only: first
      full_ZF_app_natural[OF ww vw access full_ZF_implication_value_type[OF ww] pm]
      full_ZF_implication_value_natural[OF ww vw access])
  show ?thesis by (simp only: evaluated; rule full_ZF_implication_result[OF vw pv qm])
qed

theorem full_ZF_forall_future_value:
  assumes ww: "w \<in> worlds" and fm: "f \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
  shows "app (full_ZF_logical_value actual (SBAll \<sigma>)) (Opair (book_ZF_world_code w) f) =
    full_ZF_future_collect w (\<lambda>v. \<forall>a\<in>explode (full_ZF_D \<sigma> v).
      Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a)))"
proof -
  have root: "actual \<in> worlds" by (rule book_full_C_root_is_world)
  have reach: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  have evaluated: "app (full_ZF_logical_value actual (SBAll \<sigma>)) (Opair (book_ZF_world_code w) f) =
    full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f"
    by (simp only: full_ZF_future_application[OF root ww reach full_ZF_forall_value_type[OF root] fm]
      full_ZF_forall_value_natural[OF root ww reach])
  show ?thesis by (simp only: evaluated; rule full_ZF_forall_result[OF ww fm])
qed

theorem full_ZF_forall_future_set_in_domain:
  assumes ww: "w \<in> worlds" and fm: "f \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
  shows "full_ZF_future_collect w (\<lambda>v. \<forall>a\<in>explode (full_ZF_D \<sigma> v).
    Elem (book_ZF_world_code v) (app f (Opair (book_ZF_world_code v) a))) \<in> explode (full_ZF_D Prop w)"
  by (simp only: full_ZF_forall_result[OF ww fm, symmetric];
    rule full_ZF_app_type[OF ww full_ZF_forall_value_type[OF ww] fm])

theorem full_ZF_implication_future_set_in_domain:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and pm: "p \<in> explode (full_ZF_D Prop w)" and qm: "q \<in> explode (full_ZF_D Prop v)"
  shows "full_ZF_future_collect v (\<lambda>u. \<not> Elem (book_ZF_world_code u) (full_ZF_i Prop w v p) \<or> Elem (book_ZF_world_code u) q)
    \<in> explode (full_ZF_D Prop v)"
proof -
  have pv: "full_ZF_i Prop w v p \<in> explode (full_ZF_D Prop v)" by (rule full_ZF_i_type[OF ww vw access pm])
  show ?thesis by (simp only: full_ZF_implication_result[OF vw pv qm, symmetric];
    rule full_ZF_app_type[OF vw full_ZF_app_type[OF vw full_ZF_implication_value_type[OF vw] pv] qm])
qed

end

text \<open>
  The actual root operators have the future behavior specified by
  Definition 18.1(3.3–3.4), with the explicit future-domain reading of
  implication. The returned comprehensions belong to the chosen Dᵗ,
  not only to the ambient powerset. No proper-domain closure premise
  has been added. The untruncated printed W-complement remains a
  distinct expression, as documented in the source-convention note.
\<close>

end
