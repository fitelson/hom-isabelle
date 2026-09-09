theory Bacon_Book_Full_Proposition_Modalized
  imports Bacon_Book_Full_Term_Modalized_Sets Bacon_Book_Modalized_Bijection
begin

context book_full_C_canonical_frame
begin

theorem full_proposition_modalized_set:
  "book_modalized_set worlds le (book_full_C_proposition_domain \<Sigma> B G actual)
    (\<lambda>w v p. p \<inter> {u\<in>worlds. le v u})"
proof -
  interpret Order: book_pointed_preorder worlds le actual by (rule full_frame_pointed_preorder)
  show ?thesis
  proof unfold_locales
    show "\<And>w v p. w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
      p \<in> book_full_C_proposition_domain \<Sigma> B G actual w \<Longrightarrow>
      p \<inter> {u\<in>worlds. le v u} \<in> book_full_C_proposition_domain \<Sigma> B G actual v"
      by (rule proposition_domain_truncation; assumption)
    show "\<And>w p. w \<in> worlds \<Longrightarrow> p \<in> book_full_C_proposition_domain \<Sigma> B G actual w \<Longrightarrow>
      p \<inter> {u\<in>worlds. le w u} = p"
      using proposition_domain_future by blast
    fix w v u p
    assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds" and wv: "le w v" and vu: "le v u"
      and member: "p \<in> book_full_C_proposition_domain \<Sigma> B G actual w"
    have subset: "{z\<in>worlds. le u z} \<subseteq> {z\<in>worlds. le v z}"
      using book_full_C_rooted_trans[OF vw vu] by blast
    show "p \<inter> {z\<in>worlds. le u z} = (p \<inter> {z\<in>worlds. le v z}) \<inter> {z\<in>worlds. le u z}"
      using subset by blast
  qed
qed

theorem full_proposition_modalized_map:
  "book_modalized_map worlds le (\<lambda>w. book_C_identity_domain (fst w) G (snd w) Prop)
    (\<lambda>w v X. book_C_term_counterpart G w v Prop X)
    (book_full_C_proposition_domain \<Sigma> B G actual) (\<lambda>w v p. p \<inter> {u\<in>worlds. le v u})
    (book_full_C_proposition_h \<Sigma> B G actual)"
proof (rule book_modalized_mapI)
  fix w X
  assume ww: "w \<in> worlds" and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
  have image: "book_full_C_proposition_h \<Sigma> B G actual w ` book_C_identity_domain (fst w) G (snd w) Prop =
    book_full_C_proposition_domain \<Sigma> B G actual w"
    using proposition_h_bijection[OF ww] unfolding bij_betw_def by (rule conjunct2)
  have member: "book_full_C_proposition_h \<Sigma> B G actual w X \<in>
    book_full_C_proposition_h \<Sigma> B G actual w ` book_C_identity_domain (fst w) G (snd w) Prop"
    by (rule imageI[OF xd])
  show "book_full_C_proposition_h \<Sigma> B G actual w X \<in> book_full_C_proposition_domain \<Sigma> B G actual w"
    using member by (simp only: image)
next
  fix w v X
  assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
  show "book_full_C_proposition_h \<Sigma> B G actual v (book_C_term_counterpart G w v Prop X) =
    book_full_C_proposition_h \<Sigma> B G actual w X \<inter> {u\<in>worlds. le v u}"
    by (rule proposition_h_naturality[OF ww vw access xd])
qed

theorem full_proposition_modalized_bijection:
  "book_modalized_bijection worlds le (\<lambda>w. book_C_identity_domain (fst w) G (snd w) Prop)
    (\<lambda>w v X. book_C_term_counterpart G w v Prop X)
    (book_full_C_proposition_domain \<Sigma> B G actual) (\<lambda>w v p. p \<inter> {u\<in>worlds. le v u})
    (book_full_C_proposition_h \<Sigma> B G actual)"
proof -
  interpret S: book_modalized_set worlds le "\<lambda>w. book_C_identity_domain (fst w) G (snd w) Prop"
    "\<lambda>w v X. book_C_term_counterpart G w v Prop X" by (rule full_term_modalized_set)
  interpret T: book_modalized_set worlds le "book_full_C_proposition_domain \<Sigma> B G actual"
    "\<lambda>w v p. p \<inter> {u\<in>worlds. le v u}" by (rule full_proposition_modalized_set)
  show ?thesis by (unfold_locales; (rule full_proposition_modalized_map | rule proposition_h_bijection); assumption?)
qed

end

text \<open>
  The already constructed full-C proposition domains and hᵗ map now
  instantiate the exact Chapter 17 modalized-set/map interfaces and the
  lower-type bijection interface. Counterparts are literal intersection
  with the later future. No base-frame proposition sets, full powerset
  domain or new naturality assumption is substituted for this instance.
\<close>

end
