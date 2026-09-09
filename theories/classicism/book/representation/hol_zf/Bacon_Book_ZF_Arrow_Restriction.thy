theory Bacon_Book_ZF_Arrow_Restriction
  imports Bacon_Book_ZF_Modalized_Family
begin

section \<open>Function counterparts are restrictions of actual graphs\<close>

context book_full_C_canonical_frame
begin

definition full_ZF_arrow_restrict where
  "full_ZF_arrow_restrict \<sigma> v F =
    Lambda (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) v) (\<lambda>p. app F p)"

text \<open>
  We first prove the restriction equation on h-images. At a future
  pair (u,a), both sides apply the same source function at u: the
  counterpart composition law identifies the two source values.
  Pair decoding supplies all world, accessibility and argument guards.
\<close>

theorem full_ZF_h_arrow_restriction:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and wv: "le w v"
    and member: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
  shows "full_ZF_h (Arr \<sigma> \<tau>) v (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X) =
    full_ZF_arrow_restrict \<sigma> v (full_ZF_h (Arr \<sigma> \<tau>) w X)"
proof -
  have bodies: "\<And>p. Elem p (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) v) \<Longrightarrow>
    full_ZF_h \<tau> (full_world_decode (Fst p))
      (book_C_term_app (fst (full_world_decode (Fst p))) G (snd (full_world_decode (Fst p))) \<sigma> \<tau>
        (book_C_term_counterpart G v (full_world_decode (Fst p)) (Arr \<sigma> \<tau>)
          (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X))
        (full_ZF_inverse \<sigma> (full_ZF_h \<sigma>) (full_world_decode (Fst p)) (Snd p))) =
    app (full_ZF_h (Arr \<sigma> \<tau>) w X) p"
  proof -
    fix p
    assume pair: "Elem p (full_ZF_future_pairs \<sigma> (full_ZF_h \<sigma>) v)"
    let ?u = "full_world_decode (Fst p)"
    have uw: "?u \<in> worlds" and vu: "le v ?u"
      and am: "Snd p \<in> explode (full_ZF_domain \<sigma> (full_ZF_h \<sigma>) ?u)"
      and pe: "Opair (book_ZF_world_code ?u) (Snd p) = p"
      using full_ZF_future_pair_decode[OF pair] by blast+
    have wu: "le w ?u" by (rule book_full_C_rooted_trans[OF ww wv vu])
    have ad: "Snd p \<in> explode (full_ZF_D \<sigma> ?u)" using am by (simp only: full_ZF_D_def)
    have chain: "book_C_term_counterpart G v ?u (Arr \<sigma> \<tau>)
        (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X) =
      book_C_term_counterpart G w ?u (Arr \<sigma> \<tau>) X"
      by (rule book_C_term_counterpart_composition[OF rich full_rooted_base_world[OF ww]
        full_rooted_base_world[OF vw] full_rooted_base_world[OF uw] wv vu member])
    show "full_ZF_h \<tau> ?u
      (book_C_term_app (fst ?u) G (snd ?u) \<sigma> \<tau>
        (book_C_term_counterpart G v ?u (Arr \<sigma> \<tau>)
          (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X))
        (full_ZF_inverse \<sigma> (full_ZF_h \<sigma>) ?u (Snd p))) =
      app (full_ZF_h (Arr \<sigma> \<tau>) w X) p"
      using full_ZF_arrow_value[OF uw wu ad, of \<tau> X]
      by (simp only: chain full_ZF_j_def pe)
  qed
  show ?thesis
    unfolding full_ZF_h.simps full_ZF_arrow_restrict_def
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI; rule bodies[unfolded full_ZF_h.simps]; assumption)
qed

theorem full_ZF_i_arrow_restriction:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and wv: "le w v"
    and member: "F \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) w)"
  shows "full_ZF_i (Arr \<sigma> \<tau>) w v F = full_ZF_arrow_restrict \<sigma> v F"
proof -
  have inverse: "full_ZF_j (Arr \<sigma> \<tau>) w F \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    by (rule full_ZF_j_type[OF member])
  show ?thesis unfolding full_ZF_i_def
    by (simp only: full_ZF_h_arrow_restriction[OF ww vw wv inverse] full_ZF_hj[OF member])
qed

theorem full_ZF_application_preserved:
  assumes ww: "w \<in> worlds"
    and member: "a \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
    and fm: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
  shows "app (full_ZF_h (Arr \<sigma> \<tau>) w X) (Opair (book_ZF_world_code w) (full_ZF_h \<sigma> w a)) =
    full_ZF_h \<tau> w (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> X a)"
  using full_ZF_arrow_value[OF ww book_full_C_rooted_refl[OF ww] full_ZF_h_type[OF member], of \<tau> X]
  by (simp only: full_ZF_jh[OF ww member]
    book_C_term_counterpart_identity[OF rich full_rooted_base_world[OF ww] fm])

end

text \<open>
  These are the literal restriction and application equations required
  by Bacon's function-type construction on pp.400–401. They hold for
  every full type in the one ZF recursion, not only for a separately
  chosen lower representation. No complete modal-model certificate is
  inferred from these equations alone.
\<close>

end
