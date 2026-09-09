theory Bacon_Book_ZF_Equality_Future_Value
  imports Bacon_Book_ZF_Equality_Value
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_equality_result:
  assumes ww: "w \<in> worlds" and am: "a \<in> explode (full_ZF_D \<sigma> w)" and bm: "b \<in> explode (full_ZF_D \<sigma> w)"
  shows "full_ZF_app w \<sigma> Prop (full_ZF_app w \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value w \<sigma>) a) b =
    full_ZF_future_collect w (\<lambda>v. full_ZF_i \<sigma> w v a = full_ZF_i \<sigma> w v b)"
proof -
  let ?E = "full_ZF_equality_value w \<sigma>"
  let ?F = "full_ZF_app w \<sigma> (Arr \<sigma> Prop) ?E a"
  let ?p = "full_ZF_app w \<sigma> Prop ?F b"
  have ft: "?F \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
    by (rule full_ZF_app_type[OF ww full_ZF_equality_value_type am])
  have pt: "?p \<in> explode (full_ZF_D Prop w)" by (rule full_ZF_app_type[OF ww ft bm])
  show ?thesis
  proof (rule full_ZF_proposition_eq_collect[OF pt])
    fix v
    assume vw: "v \<in> worlds" and access: "le w v"
    have av: "full_ZF_i \<sigma> w v a \<in> explode (full_ZF_D \<sigma> v)" by (rule full_ZF_i_type[OF ww vw access am])
    have bv: "full_ZF_i \<sigma> w v b \<in> explode (full_ZF_D \<sigma> v)" by (rule full_ZF_i_type[OF ww vw access bm])
    have natural: "full_ZF_i Prop w v ?p =
      full_ZF_app v \<sigma> Prop
        (full_ZF_app v \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value v \<sigma>) (full_ZF_i \<sigma> w v a))
        (full_ZF_i \<sigma> w v b)"
      by (simp only: full_ZF_app_natural[OF ww vw access ft bm]
        full_ZF_app_natural[OF ww vw access full_ZF_equality_value_type am] full_ZF_equality_value_natural[OF ww vw access])
    have truth: "full_ZF_value_truth v (full_ZF_i Prop w v ?p) =
      (full_ZF_i \<sigma> w v a = full_ZF_i \<sigma> w v b)"
      by (simp only: natural; rule full_ZF_equality_value_truth[OF vw av bv])
    show "Elem (book_ZF_world_code v) ?p = (full_ZF_i \<sigma> w v a = full_ZF_i \<sigma> w v b)"
      using truth by (simp only: full_ZF_proposition_future_truth[OF ww vw access pt])
  qed
qed

theorem full_ZF_equality_future_value:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and am: "a \<in> explode (full_ZF_D \<sigma> w)" and bm: "b \<in> explode (full_ZF_D \<sigma> v)"
  shows "app (app (full_ZF_equality_value actual \<sigma>) (Opair (book_ZF_world_code w) a))
      (Opair (book_ZF_world_code v) b) =
    full_ZF_future_collect v (\<lambda>u. full_ZF_i \<sigma> w u a = full_ZF_i \<sigma> v u b)"
proof -
  let ?F = "app (full_ZF_equality_value actual \<sigma>) (Opair (book_ZF_world_code w) a)"
  let ?p = "app ?F (Opair (book_ZF_world_code v) b)"
  let ?a = "full_ZF_i \<sigma> w v a"
  have root: "actual \<in> worlds" by (rule book_full_C_root_is_world)
  have reach: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  have first: "?F = full_ZF_app w \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value w \<sigma>) a"
    by (simp only: full_ZF_future_application[OF root ww reach full_ZF_equality_value_type am]
      full_ZF_equality_value_natural[OF root ww reach])
  have ft: "?F \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
    by (simp only: first; rule full_ZF_app_type[OF ww full_ZF_equality_value_type am])
  have av: "?a \<in> explode (full_ZF_D \<sigma> v)" by (rule full_ZF_i_type[OF ww vw access am])
  have second: "?p = full_ZF_app v \<sigma> Prop (full_ZF_app v \<sigma> (Arr \<sigma> Prop) (full_ZF_equality_value v \<sigma>) ?a) b"
    by (subst full_ZF_future_application[OF ww vw access ft bm]; simp only: first
      full_ZF_app_natural[OF ww vw access full_ZF_equality_value_type am] full_ZF_equality_value_natural[OF ww vw access])
  have pt: "?p \<in> explode (full_ZF_D Prop v)"
    by (rule full_ZF_future_application_type[OF ww vw access ft bm])
  have represented: "?p = full_ZF_future_collect v (\<lambda>u. full_ZF_i \<sigma> v u ?a = full_ZF_i \<sigma> v u b)"
    by (simp only: second; rule full_ZF_equality_result[OF vw av bm])
  show ?thesis
  proof (rule full_ZF_proposition_eq_collect[OF pt])
    fix u
    assume uw: "u \<in> worlds" and vu: "le v u"
    have composition: "full_ZF_i \<sigma> v u ?a = full_ZF_i \<sigma> w u a"
      by (rule full_ZF_i_composition[OF ww vw uw access vu am, symmetric])
    show "Elem (book_ZF_world_code u) ?p = (full_ZF_i \<sigma> w u a = full_ZF_i \<sigma> v u b)"
      by (simp only: represented full_ZF_future_collect_member[OF uw] vu simp_thms composition)
  qed
qed

end

text \<open>
  Definition 18.1(3.5): the actual closed identity operator at @ sends
  (w,a), then (v,b), to the set of future u where iᵂᵘa=iᵛᵘb.
  The future guard u≥v≥w≥@ is explicit in the comprehension and
  application premises. This is equality of actual proposition sets,
  not just agreement of their truth values at v. Domain membership
  comes from the typed closed operator and actual application closure.
\<close>

end
