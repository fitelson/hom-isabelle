theory Bacon_Book_ZF_Model_Operator_Restriction
  imports Bacon_Book_ZF_Modal_Model
begin

context book_ZF_frame
begin

lemma later_pair_earlier:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and access: "R w v"
    and member: "Elem p (book_ZF_pairs W R A v)"
  shows "Elem p (book_ZF_pairs W R A w)"
proof -
  have uw: "Fst p \<in> explode W" and vu: "R v (Fst p)"
    and am: "Elem (Snd p) (A (Fst p))" and shape: "Opair (Fst p) (Snd p) = p"
    using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
  have wu: "R w (Fst p)" by (rule transitive[OF ww vw uw access vu])
  have uelem: "Elem (Fst p) W" using uw by (simp only: explode_Elem)
  have "Elem (Opair (Fst p) (Snd p)) (book_ZF_pairs W R A w)"
    by (simp only: book_ZF_pairs_member; rule conjI[OF uelem conjI[OF wu am]])
  then show ?thesis by (simp only: shape)
qed

theorem outer_function_restriction:
  assumes ww: "w \<in> explode W" and vw: "v \<in> explode W" and access: "R w v"
  shows "book_ZF_restrict W R A v (Lambda (book_ZF_pairs W R A w) B) = Lambda (book_ZF_pairs W R A v) B"
proof (unfold book_ZF_restrict_def, rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
  fix p
  assume member: "Elem p (book_ZF_pairs W R A v)"
  have earlier: "Elem p (book_ZF_pairs W R A w)" by (rule later_pair_earlier[OF ww vw access member])
  show "app (Lambda (book_ZF_pairs W R A w) B) p = B p" by (rule Lambda_app[OF earlier])
qed

end

context book_ZF_modal_model
begin

lemma outer_family_member:
  assumes vw: "v \<in> explode W"
    and member: "Lambda (book_ZF_pairs W R (D \<sigma>) root) B \<in> explode (D (Arr \<sigma> \<tau>) root)"
  shows "Lambda (book_ZF_pairs W R (D \<sigma>) v) B \<in> explode (D (Arr \<sigma> \<tau>) v)"
proof -
  have access: "R root v" by (rule root_below[OF vw])
  have moved: "i (Arr \<sigma> \<tau>) root v (Lambda (book_ZF_pairs W R (D \<sigma>) root) B) \<in> explode (D (Arr \<sigma> \<tau>) v)"
    by (rule transport_type[OF root_world vw access member])
  have equation: "i (Arr \<sigma> \<tau>) root v (Lambda (book_ZF_pairs W R (D \<sigma>) root) B) =
    Lambda (book_ZF_pairs W R (D \<sigma>) v) B"
    by (simp only: function_restriction[OF root_world vw access member] outer_function_restriction[OF root_world vw access])
  show ?thesis using moved by (simp only: equation)
qed

theorem k_member_at:
  "v \<in> explode W \<Longrightarrow> book_ZF_k W R D i v \<sigma> \<tau> \<in> explode (D (Arr \<sigma> (Arr \<tau> \<sigma>)) v)"
  unfolding book_ZF_k_def by (rule outer_family_member; (assumption | rule k_member[unfolded book_ZF_k_def]))

theorem s_member_at:
  "v \<in> explode W \<Longrightarrow> book_ZF_s W R D v \<sigma> \<tau> \<rho> \<in>
    explode (D (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) v)"
  unfolding book_ZF_s_def by (rule outer_family_member; (assumption | rule s_member[unfolded book_ZF_s_def]))

theorem implication_member_at:
  "v \<in> explode W \<Longrightarrow> book_ZF_if_future W R D i v \<in> explode (D (Arr Prop (Arr Prop Prop)) v)"
  unfolding book_ZF_if_future_def by (rule outer_family_member; (assumption | rule implication_member[unfolded book_ZF_if_future_def]))

theorem universal_member_at:
  "v \<in> explode W \<Longrightarrow> book_ZF_all W R D v \<sigma> \<in> explode (D (Arr (Arr \<sigma> Prop) Prop) v)"
  unfolding book_ZF_all_def by (rule outer_family_member; (assumption | rule universal_member[unfolded book_ZF_all_def]))

theorem identity_member_at:
  "v \<in> explode W \<Longrightarrow> book_ZF_eq W R D i v \<sigma> \<in> explode (D (Arr \<sigma> (Arr \<sigma> Prop)) v)"
  unfolding book_ZF_eq_def by (rule outer_family_member; (assumption | rule identity_member[unfolded book_ZF_eq_def]))

end

text \<open>
  Each prescribed operation has an outer future-pair domain and a
  body independent of the starting world. Restriction therefore
  changes only that outer domain. Root membership, counterpart
  closure and @≤v give membership at every world, discharging the
  all-world wording preceding Definition 18.1(3)'s displayed root
  memberships. No interpreter or canonical construction is used.
\<close>

end
