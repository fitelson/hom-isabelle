theory Bacon_Book_ZF_Arrow_Values
  imports Bacon_Book_ZF_Recursion_Base
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_arrow_value:
  assumes vw: "v \<in> worlds" and access: "le w v" and member: "a \<in> explode (full_ZF_D \<sigma> v)"
  shows "app (full_ZF_h (Arr \<sigma> \<tau>) w X) (Opair (book_ZF_world_code v) a) =
    full_ZF_h \<tau> v (book_C_term_app (fst v) G (snd v) \<sigma> \<tau>
      (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X) (full_ZF_j \<sigma> v a))"
proof -
  have pair: "Elem (Opair (book_ZF_world_code v) a) (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) w)"
    by (simp only: full_ZF_future_pair_member[OF vw] full_ZF_D_def[symmetric]; rule conjI[OF access member])
  show ?thesis by (simp only: full_ZF_h.simps Lambda_app[OF pair] Fst Snd full_world_decode_code[OF vw] full_ZF_j_def)
qed

theorem full_ZF_arrow_domain:
  "isFun (full_ZF_h (Arr \<sigma> \<tau>) w X) \<and>
    Domain (full_ZF_h (Arr \<sigma> \<tau>) w X) = full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) w"
  by (simp only: full_ZF_h.simps isFun_Lambda domain_Lambda; simp)

end

text \<open>
  Each arrow value is an actual set-theoretic function graph with
  precisely the coded future/argument domain. Graph application at a
  valid pair gives the source term application transported through the
  two lower-type maps. The pair membership guard is proved before
  Lambda_app is used; injectivity of the lower map is not hidden here.
\<close>

end
