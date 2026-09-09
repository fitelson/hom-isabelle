theory Bacon_Book_Canonical_Identity_Persistence
  imports Bacon_Book_Classicism_Identity_Stability Bacon_Book_Canonical_Frame
begin

theorem book_C_canonical_identity_persistence:
  assumes rich: "sg_rich G" and world: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and access: "book_C_canonical_le G w v"
    and al: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV (fst w) G D \<sigma>"
    and ac: "named_fv A = {}" and dc: "named_fv D = {}"
    and identity: "book_leibniz G \<sigma> A D \<in> snd w"
  shows "book_leibniz G \<sigma> A D \<in> snd v"
proof -
  have old_world: "snd w \<in> book_C_closed_worlds (fst w) G"
    by (rule book_C_closed_maximal_is_world[OF book_C_canonical_world_data(4)[OF world]])
  have bc: "named_fv (book_box G (book_leibniz G \<sigma> A D)) = {}"
    by (simp only: book_box_fv book_leibniz_fv ac dc Un_empty)
  have necessary: "book_box G (book_leibniz G \<sigma> A D) \<in> snd w"
    by (rule book_C_closed_world_apply_theorem[OF rich old_world book_C_identity_stability[OF rich al bl] identity bc])
  show ?thesis using access necessary unfolding book_C_canonical_le_def by blast
qed

text \<open>
  If the closed identity A=σD belongs to w and w≤v, it belongs to v.
  This is obtained by ordinary modus ponens with the original C stability
  implication, then by accessibility. The target need not separately be
  a canonical world for this implication; target-language membership,
  when required for classes, follows from the earlier language theorem.
\<close>

end
