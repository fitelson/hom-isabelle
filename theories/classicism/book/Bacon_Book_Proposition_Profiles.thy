theory Bacon_Book_Proposition_Profiles
  imports Bacon_Book_Proposition_Identity_Membership
begin

section \<open>Proposition 18.4 at type t: future truth sets determine identity\<close>

definition book_C_proposition_profile where
  "book_C_proposition_profile \<Sigma> B G actual w P =
    {v \<in> book_C_rooted_worlds \<Sigma> B G actual. book_C_canonical_le G w v \<and> P \<in> snd v}"

context book_C_canonical_frame
begin

theorem proposition_profiles_eq_iff_identity:
  assumes world: "w \<in> worlds" and pm: "P \<in> book_closed_terms (fst w) G Prop"
    and qm: "Q \<in> book_closed_terms (fst w) G Prop"
  shows "book_C_proposition_profile \<Sigma> B G actual w P = book_C_proposition_profile \<Sigma> B G actual w Q \<longleftrightarrow>
    book_leibniz G Prop P Q \<in> snd w"
proof -
  have ww: "w \<in> book_C_canonical_worlds \<Sigma> B G" by (rule book_C_rooted_world_data(1)[OF world])
  have pl: "book_theory_formula (fst w) G P" by (rule book_closed_terms_language[OF pm])
  have ql: "book_theory_formula (fst w) G Q" by (rule book_closed_terms_language[OF qm])
  have pc: "named_fv P = {}" by (rule book_closed_terms_closed[OF pm])
  have qc: "named_fv Q = {}" by (rule book_closed_terms_closed[OF qm])
  show ?thesis
  proof
    assume equal: "book_C_proposition_profile \<Sigma> B G actual w P = book_C_proposition_profile \<Sigma> B G actual w Q"
    have every: "\<forall>v\<in>worlds. le w v \<longrightarrow> book_iff G P Q \<in> snd v"
    proof (intro ballI impI)
      fix v
      assume vw: "v \<in> worlds" and access: "le w v"
      have vv: "v \<in> book_C_canonical_worlds \<Sigma> B G" by (rule book_C_rooted_world_data(1)[OF vw])
      interpret V: book_C_identity_world "fst v" G "snd v"
        by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF vv])
      have pv: "P \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich ww vv access pm])
      have qv: "Q \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich ww vv access qm])
      have same: "P \<in> snd v \<longleftrightarrow> Q \<in> snd v"
        using equal vw access unfolding book_C_proposition_profile_def by blast
      show "book_iff G P Q \<in> snd v"
        by (simp only: V.member_biconditional_iff[OF book_closed_terms_language[OF pv] book_closed_terms_language[OF qv] pc qc]; rule same)
    qed
    have il: "book_theory_formula (fst w) G (book_iff G P Q)" by (rule book_iff_language[OF rich pl ql])
    have ic: "named_fv (book_iff G P Q) = {}" by (simp add: book_iff_fv pc qc)
    have necessary: "book_box G (book_iff G P Q) \<in> snd w"
      using every by (simp only: book_proposition_18_3[OF world il ic])
    show "book_leibniz G Prop P Q \<in> snd w"
      by (rule book_C_world_boxed_propositional_equivalence[OF rich ww pl ql pc qc necessary])
  next
    assume identity: "book_leibniz G Prop P Q \<in> snd w"
    have same: "P \<in> snd v \<longleftrightarrow> Q \<in> snd v" if vw: "v \<in> worlds" and access: "le w v" for v
    proof -
      have vv: "v \<in> book_C_canonical_worlds \<Sigma> B G" by (rule book_C_rooted_world_data(1)[OF vw])
      interpret V: book_C_identity_world "fst v" G "snd v"
        by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF vv])
      have pv: "P \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich ww vv access pm])
      have qv: "Q \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich ww vv access qm])
      have future_identity: "book_leibniz G Prop P Q \<in> snd v"
        by (rule book_C_canonical_identity_persistence[OF rich ww access pl ql pc qc identity])
      show ?thesis by (rule V.proposition_identity_membership[OF pv qv future_identity])
    qed
    show "book_C_proposition_profile \<Sigma> B G actual w P = book_C_proposition_profile \<Sigma> B G actual w Q"
      unfolding book_C_proposition_profile_def using same by blast
  qed
qed

theorem proposition_profiles_eq_iff_classes:
  assumes world: "w \<in> worlds" and pm: "P \<in> book_closed_terms (fst w) G Prop"
    and qm: "Q \<in> book_closed_terms (fst w) G Prop"
  shows "book_C_proposition_profile \<Sigma> B G actual w P = book_C_proposition_profile \<Sigma> B G actual w Q \<longleftrightarrow>
    book_C_identity_class (fst w) G (snd w) Prop P = book_C_identity_class (fst w) G (snd w) Prop Q"
proof -
  interpret W: book_C_identity_world "fst w" G "snd w"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF book_C_rooted_world_data(1)[OF world]])
  show ?thesis by (simp only: proposition_profiles_eq_iff_identity[OF world pm qm] W.identity_class_eq_iff[OF pm qm])
qed

end

text \<open>
  p[A]w={v≥w : A∈v}. Equality of these actual future truth sets is
  equivalent to identity of the closed propositions in w, hence to
  equality of their term classes. The reverse separation argument uses
  the actual canonical Proposition 18.3 and the proved boxed PE theorem.
  This is the type-t separation step, not the all-type j/h construction
  or a modal-model completeness result.
\<close>

end
