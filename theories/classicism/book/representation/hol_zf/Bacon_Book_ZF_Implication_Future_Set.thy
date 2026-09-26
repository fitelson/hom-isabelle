theory Bacon_Book_ZF_Implication_Future_Set
  imports Bacon_Book_ZF_Logical_Future_Values
begin

context book_full_C_coded_frame
begin

lemma full_ZF_future_implication_set:
  assumes admitted: "full_ZF_admitted w" and qm: "q \<in> explode (full_ZF_D Prop w)"
  shows "explode (full_ZF_future_collect w (\<lambda>v. \<not> Elem (book_ZF_world_code v) p \<or> Elem (book_ZF_world_code v) q)) =
    (explode (full_ZF_future w) - explode p) \<union> explode q"
proof (rule set_eqI)
  fix z
  show "z \<in> explode (full_ZF_future_collect w (\<lambda>v. \<not> Elem (book_ZF_world_code v) p \<or> Elem (book_ZF_world_code v) q)) =
    (z \<in> (explode (full_ZF_future w) - explode p) \<union> explode q)"
  proof (cases "z \<in> explode (full_ZF_future w)")
    case True
    have code: "book_ZF_world_code (full_world_decode z) = z"
      by (rule full_ZF_future_member_data(3)[OF True])
    show ?thesis using True by (auto simp: full_ZF_future_collect_def Sep explode_Elem code)
  next
    case False
    have outside: "z \<notin> explode q" using full_ZF_proposition_future[OF admitted qm] False by blast
    show ?thesis using False outside by (auto simp: full_ZF_future_collect_def Sep explode_Elem)
  qed
qed

theorem full_ZF_implication_future_set:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and pm: "p \<in> explode (full_ZF_D Prop w)" and qm: "q \<in> explode (full_ZF_D Prop v)"
  shows "explode (app (app (full_ZF_logical_value actual SImp) (Opair (book_ZF_world_code w) p))
      (Opair (book_ZF_world_code v) q)) =
    (explode (full_ZF_future v) - explode (full_ZF_i Prop w v p)) \<union> explode q"
  by (simp only: full_ZF_implication_future_value[OF ww vw access pm qm]; rule full_ZF_future_implication_set[OF worlds_admitted[OF vw] qm])

end

text \<open>
  The actual implication result has the explicit set form
  (W↑v ∖ iᵂᵛp) ∪ q, under the world-code correspondence.
  This is the typed future restriction of Definition 18.1(3.3)'s
  printed W-complement, not an assertion that the two untruncated
  expressions are equal. The earlier source-convention diagnosis
  and its two-world counterexample remain unchanged.
\<close>

end
