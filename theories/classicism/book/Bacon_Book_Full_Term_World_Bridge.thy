theory Bacon_Book_Full_Term_World_Bridge
  imports Bacon_Book_Full_Canonical_Frame Bacon_Book_Modal_Term_Inhabitation
begin

theorem book_full_C_world_identity_algebra:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
  shows "book_C_identity_world (fst w) G (snd w)"
  by (unfold_locales; rule rich book_full_C_closed_maximal_is_base[
    OF rich book_full_C_canonical_world_data(4)[OF world]])

lemma book_full_C_closed_terms_future:
  assumes rich: "sg_rich G" and w: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "A \<in> book_closed_terms (fst v) G \<sigma>"
  by (rule book_C_closed_terms_future[OF rich book_full_C_canonical_world_is_base[OF rich w]
    book_full_C_canonical_world_is_base[OF rich v] access am])

lemma book_full_C_canonical_identity_persistence:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and access: "book_C_canonical_le G w v"
    and al: "book_in_language book_minimal_logical_type UNIV (fst w) G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV (fst w) G D \<sigma>"
    and ac: "named_fv A = {}" and dc: "named_fv D = {}"
    and identity: "book_leibniz G \<sigma> A D \<in> snd w"
  shows "book_leibniz G \<sigma> A D \<in> snd v"
  by (rule book_C_canonical_identity_persistence[OF rich book_full_C_canonical_world_is_base[
    OF rich world] access al bl ac dc identity])

lemma book_full_C_world_boxed_propositional_equivalence:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and pl: "book_theory_formula (fst w) G P" and ql: "book_theory_formula (fst w) G Q"
    and pc: "named_fv P = {}" and qc: "named_fv Q = {}"
    and boxed: "book_box G (book_iff G P Q) \<in> snd w"
  shows "book_leibniz G Prop P Q \<in> snd w"
  by (rule book_C_world_boxed_propositional_equivalence[OF rich
    book_full_C_canonical_world_is_base[OF rich world] pl ql pc qc boxed])

lemma book_full_C_term_counterpart_class:
  assumes rich: "sg_rich G" and w: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_full_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "book_C_term_counterpart G w v \<sigma> (book_C_identity_class (fst w) G (snd w) \<sigma> A) =
    book_C_identity_class (fst v) G (snd v) \<sigma> A"
  by (rule book_C_term_counterpart_class[OF rich book_full_C_canonical_world_is_base[OF rich w]
    book_full_C_canonical_world_is_base[OF rich v] access am])

theorem book_full_C_canonical_identity_domain_nonempty:
  assumes rich: "sg_rich G" and world: "w \<in> book_full_C_canonical_worlds \<Sigma> B G"
  shows "book_C_identity_domain (fst w) G (snd w) \<sigma> \<noteq> {}"
  by (rule book_C_canonical_identity_domain_nonempty[OF rich book_full_C_canonical_world_is_base[OF rich world]])

text \<open>
  Identity classes, their application/representatives, and the literal
  counterpart map depend on a world's language and sentence set, not
  on the choice of the surrounding frame. Their checked algebra is
  reused by a proved locale interpretation. Proposition profiles are
  different: those must be rebuilt over the full-C future world set.
  No equality of the base and full canonical frames is asserted.
\<close>

end
