theory Bacon_Book_ZF_Reindexed_Logical_Operators
  imports Bacon_Book_ZF_Reindexed_Combinators
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_implication_identification:
  "full_ZF_logical_value actual SImp =
    book_ZF_if_future full_world_set full_ZF_R full_ZF_D_at full_ZF_i_at full_ZF_root"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have it: "full_ZF_logical_value actual SImp \<in> explode (full_ZF_D_at (Arr Prop (Arr Prop Prop)) full_ZF_root)"
    by (simp only: full_ZF_D_at_root; rule full_ZF_implication_value_type[OF book_full_C_root_is_world])
  show ?thesis
  proof (unfold book_ZF_if_future_def, rule S.function_as_two_lambdas[OF full_ZF_root_member it])
    fix v p u q
    assume vw: "v \<in> explode full_world_set" and "full_ZF_R full_ZF_root v"
      and pm: "p \<in> explode (full_ZF_D_at Prop v)"
      and uw: "u \<in> explode full_world_set" and vu: "full_ZF_R v u"
      and qm: "q \<in> explode (full_ZF_D_at Prop u)"
    have behavior: "app (app (full_ZF_logical_value actual SImp) (Opair v p)) (Opair u q) =
      full_ZF_future_collect (full_world_decode u) (\<lambda>t.
        \<not> Elem (book_ZF_world_code t) (full_ZF_i Prop (full_world_decode v) (full_world_decode u) p) \<or> Elem (book_ZF_world_code t) q)"
      using full_ZF_implication_future_value[OF full_world_decode_type[OF vw] full_world_decode_type[OF uw]
        vu[unfolded full_ZF_R_def] pm[unfolded full_ZF_D_at_def] qm[unfolded full_ZF_D_at_def]]
      by (simp only: full_world_code_decode[OF vw] full_world_code_decode[OF uw])
    show "app (app (full_ZF_logical_value actual SImp) (Opair v p)) (Opair u q) =
      book_ZF_collect full_world_set full_ZF_R (Fst (Opair u q))
        (\<lambda>t. \<not> Elem t (full_ZF_i_at Prop (Fst (Opair v p)) (Fst (Opair u q)) (Snd (Opair v p))) \<or> Elem t (Snd (Opair u q)))"
      by (simp only: Fst Snd full_ZF_collect_reindex full_ZF_i_at_def; rule behavior)
  qed
qed

theorem full_ZF_universal_identification:
  "full_ZF_logical_value actual (SBAll \<sigma>) =
    book_ZF_all full_world_set full_ZF_R full_ZF_D_at full_ZF_root \<sigma>"
proof -
  interpret S: book_ZF_modal_structure full_world_set full_ZF_R full_ZF_root full_ZF_D_at full_ZF_i_at
    by (rule full_ZF_reindexed_structure)
  have at: "full_ZF_logical_value actual (SBAll \<sigma>) \<in> explode (full_ZF_D_at (Arr (Arr \<sigma> Prop) Prop) full_ZF_root)"
    by (simp only: full_ZF_D_at_root; rule full_ZF_forall_value_type[OF book_full_C_root_is_world])
  show ?thesis
  proof (unfold book_ZF_all_def, rule S.function_as_lambda[OF full_ZF_root_member at])
    fix v f
    assume vw: "v \<in> explode full_world_set" and "full_ZF_R full_ZF_root v"
      and fm: "f \<in> explode (full_ZF_D_at (Arr \<sigma> Prop) v)"
    have behavior: "app (full_ZF_logical_value actual (SBAll \<sigma>)) (Opair v f) =
      full_ZF_future_collect (full_world_decode v) (\<lambda>t. \<forall>a\<in>explode (full_ZF_D \<sigma> t).
        Elem (book_ZF_world_code t) (app f (Opair (book_ZF_world_code t) a)))"
      using full_ZF_forall_future_value[OF full_world_decode_type[OF vw] fm[unfolded full_ZF_D_at_def]]
      by (simp only: full_world_code_decode[OF vw])
    have collect: "book_ZF_collect full_world_set full_ZF_R v
      (\<lambda>t. \<forall>a\<in>explode (full_ZF_D_at \<sigma> t). Elem t (app f (Opair t a))) =
      full_ZF_future_collect (full_world_decode v) (\<lambda>t. \<forall>a\<in>explode (full_ZF_D \<sigma> t).
        Elem (book_ZF_world_code t) (app f (Opair (book_ZF_world_code t) a)))"
    proof (rule full_ZF_collect_compatible)
      fix t
      assume tw: "t \<in> worlds"
      show "(\<forall>a\<in>explode (full_ZF_D_at \<sigma> (book_ZF_world_code t)).
          Elem (book_ZF_world_code t) (app f (Opair (book_ZF_world_code t) a))) =
        (\<forall>a\<in>explode (full_ZF_D \<sigma> t). Elem (book_ZF_world_code t) (app f (Opair (book_ZF_world_code t) a)))"
        by (simp only: full_ZF_D_at_code[OF tw])
    qed
    show "app (full_ZF_logical_value actual (SBAll \<sigma>)) (Opair v f) =
      book_ZF_collect full_world_set full_ZF_R (Fst (Opair v f))
        (\<lambda>t. \<forall>a\<in>explode (full_ZF_D_at \<sigma> t). Elem t (app (Snd (Opair v f)) (Opair t a)))"
      by (simp only: Fst Snd collect; rule behavior)
  qed
qed

end

text \<open>
  The canonical primitive values are exactly the independent model's
  prescribed graphs, not only functions with matching present-world
  truth values. Future comprehensions are compared through the actual
  world-code bijection. The universal comparison retains the whole
  typed future domain, and implication retains its explicit future
  restriction.
\<close>

end
