theory Bacon_Book_Full_Canonical_World_Existence
  imports Bacon_Book_Full_Canonical_Worlds Bacon_Book_Full_Countable_Signature_Recoding
begin

context book_countable_ambient_signature
begin

theorem book_full_C_canonical_world_exists:
  assumes rich: "sg_rich G" and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>w\<in>book_full_C_canonical_worlds \<Sigma> B G. \<forall>A\<in>S. book_universal_closure G A \<in> snd w"
proof -
  let ?\<Omega> = "book_ambient_henkin_signature G"
  obtain M where maximal: "book_full_C_closed_maximal_extension ?\<Omega> G {} M"
    and originals: "\<forall>A\<in>S. book_universal_closure G A \<in> M"
    and witnesses: "book_closed_constant_witness_complete ?\<Omega> G M"
    using book_full_C_ambient_henkin_extension_exists[OF rich language consistent] by blast
  have world: "(?\<Omega>, M) \<in> book_full_C_canonical_worlds \<Sigma> B G"
    unfolding book_full_C_canonical_worlds_def
    by (simp only: mem_Collect_eq fst_conv snd_conv; intro conjI allI;
      rule book_ambient_henkin_signature_contains book_ambient_henkin_signature_inside
        book_ambient_henkin_signature_reserve maximal witnesses)
  have keeps: "\<forall>A\<in>S. book_universal_closure G A \<in> snd (?\<Omega>, M)" using originals by simp
  show ?thesis by (rule bexI[where x="(?\<Omega>, M)"], rule keeps, rule world)
qed

end

theorem book_full_C_countable_canonical_world_exists:
  assumes rich: "sg_rich G" and small: "\<And>\<sigma>. countable (\<Sigma> \<sigma>)"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>w\<in>book_full_C_canonical_worlds (book_countable_signature_image \<Sigma>) (\<lambda>_. UNIV) G.
    \<forall>A\<in>S. book_universal_closure G (book_typed_name_map (book_countable_signature_map \<Sigma>) A) \<in> snd w"
proof -
  let ?\<rho> = "book_countable_signature_map \<Sigma>"
  let ?\<Omega> = "book_countable_signature_image \<Sigma>"
  let ?S = "book_typed_name_map ?\<rho> ` S"
  interpret names: book_countable_ambient_signature ?\<Omega> "\<lambda>_. UNIV"
    by (rule book_countable_signature_has_ambient)
  have pc: "book_full_C_theory_consistent ?\<Omega> G ?S"
    using consistent book_full_C_countable_signature_consistency_iff[OF rich small language] by blast
  have pl: "book_theory_formula ?\<Omega> G P" if member: "P \<in> ?S" for P
  proof -
    obtain A where am: "A \<in> S" and shape: "P = book_typed_name_map ?\<rho> A" using member by blast
    show ?thesis unfolding shape book_countable_signature_image_def
      by (rule book_typed_name_map_language[OF language[OF am]]; rule book_typed_image_maps; assumption)
  qed
  show ?thesis using names.book_full_C_canonical_world_exists[OF rich pl pc] by blast
qed

text \<open>
  An actual canonical world containing the universal closures of the
  given C-consistent premises is constructed. For countably declared
  signatures on arbitrary name carriers, the original names are first
  recoded into ℕ; only that initial step changes the carrier. Every
  subsequent world uses a sublanguage of the same ambient ℕ signature.
  The theorem is existence of a sentence set, not a modal-model theorem.
\<close>

end
