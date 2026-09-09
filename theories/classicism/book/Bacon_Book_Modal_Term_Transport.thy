theory Bacon_Book_Modal_Term_Transport
  imports Bacon_Book_Modal_Term_Application
begin

section \<open>Definition 18.9: counterparts of identity classes\<close>

definition book_C_term_counterpart :: "sgcontext \<Rightarrow> 'c book_C_world \<Rightarrow> 'c book_C_world \<Rightarrow>
    otype \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term set" where
  "book_C_term_counterpart G w v \<sigma> X = book_C_identity_class (fst v) G (snd v) \<sigma> (book_C_identity_rep X)"

lemma book_C_closed_terms_future:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "A \<in> book_closed_terms (fst v) G \<sigma>"
proof -
  have maps: "\<And>\<tau> c. c \<in> fst w \<tau> \<Longrightarrow> c \<in> fst v \<tau>"
    by (rule subsetD[OF book_C_canonical_le_language[OF rich w v access]]; assumption)
  have al: "book_in_language book_minimal_logical_type UNIV (fst v) G A \<sigma>"
    using book_typed_name_map_language[where \<rho>="\<lambda>\<tau> c. c", OF book_closed_terms_language[OF am] maps]
    by (simp only: book_typed_name_map_id)
  show ?thesis by (rule book_closed_termsI[OF al book_closed_terms_closed[OF am]])
qed

theorem book_C_identity_class_future_inclusion:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "book_C_identity_class (fst w) G (snd w) \<sigma> A \<subseteq> book_C_identity_class (fst v) G (snd v) \<sigma> A"
proof
  fix D
  assume member: "D \<in> book_C_identity_class (fst w) G (snd w) \<sigma> A"
  have data: "D \<in> book_closed_terms (fst w) G \<sigma> \<and> book_leibniz G \<sigma> A D \<in> snd w"
    using member unfolding book_C_identity_class_def by (rule CollectD)
  have dm: "D \<in> book_closed_terms (fst w) G \<sigma>" by (rule conjunct1[OF data])
  have future: "D \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v access dm])
  have identity: "book_leibniz G \<sigma> A D \<in> snd v"
    by (rule book_C_canonical_identity_persistence[OF rich w access book_closed_terms_language[OF am]
      book_closed_terms_language[OF dm] book_closed_terms_closed[OF am] book_closed_terms_closed[OF dm] conjunct2[OF data]])
  show "D \<in> book_C_identity_class (fst v) G (snd v) \<sigma> A"
    unfolding book_C_identity_class_def by (rule CollectI, rule conjI[OF future identity])
qed

theorem book_C_term_counterpart_class:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and am: "A \<in> book_closed_terms (fst w) G \<sigma>"
  shows "book_C_term_counterpart G w v \<sigma> (book_C_identity_class (fst w) G (snd w) \<sigma> A) =
    book_C_identity_class (fst v) G (snd v) \<sigma> A"
proof -
  interpret W: book_C_identity_world "fst w" G "snd w"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF w])
  interpret V: book_C_identity_world "fst v" G "snd v"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF v])
  let ?X = "book_C_identity_class (fst w) G (snd w) \<sigma> A"
  have xd: "?X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
    unfolding book_C_identity_domain_def by (rule imageI[OF am])
  have rm: "book_C_identity_rep ?X \<in> book_closed_terms (fst w) G \<sigma>" by (rule W.identity_rep_typed[OF xd])
  have equal: "book_C_identity_class (fst w) G (snd w) \<sigma> (book_C_identity_rep ?X) = ?X"
    by (rule W.identity_rep_class[OF xd])
  have identity: "book_leibniz G \<sigma> (book_C_identity_rep ?X) A \<in> snd w"
    using equal by (simp only: W.identity_class_eq_iff[OF rm am])
  have future_identity: "book_leibniz G \<sigma> (book_C_identity_rep ?X) A \<in> snd v"
    by (rule book_C_canonical_identity_persistence[OF rich w access book_closed_terms_language[OF rm]
      book_closed_terms_language[OF am] book_closed_terms_closed[OF rm] book_closed_terms_closed[OF am] identity])
  have rv: "book_C_identity_rep ?X \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v access rm])
  have av: "A \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v access am])
  show ?thesis unfolding book_C_term_counterpart_def
    by (simp only: V.identity_class_eq_iff[OF rv av]; rule future_identity)
qed

theorem book_C_term_counterpart_typed:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_C_term_counterpart G w v \<sigma> X \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
proof -
  obtain A where am: "A \<in> book_closed_terms (fst w) G \<sigma>"
    and shape: "X = book_C_identity_class (fst w) G (snd w) \<sigma> A"
    using xd unfolding book_C_identity_domain_def by blast
  have av: "A \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v access am])
  show ?thesis by (simp only: shape book_C_term_counterpart_class[OF rich w v access am];
    unfold book_C_identity_domain_def; rule imageI[OF av])
qed

text \<open>
  For w≤v, [A]w ⊆ [A]v, and the actual counterpart map satisfies
  iwv([A]w)=[A]v. Typedness and representative independence follow from
  language inclusion and identity persistence, both already proved.
  Classes may grow and different source classes may acquire the same
  target class: no injectivity of counterpart maps is assumed.
\<close>

end
