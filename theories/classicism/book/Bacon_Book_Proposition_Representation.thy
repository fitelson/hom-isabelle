theory Bacon_Book_Proposition_Representation
  imports Bacon_Book_Proposition_Profiles
begin

section \<open>The actual maps hᵗ and jᵗ\<close>

definition book_C_proposition_domain where
  "book_C_proposition_domain \<Sigma> B G actual w =
    book_C_proposition_profile \<Sigma> B G actual w ` book_closed_terms (fst w) G Prop"

definition book_C_proposition_h where
  "book_C_proposition_h \<Sigma> B G actual w X =
    book_C_proposition_profile \<Sigma> B G actual w (book_C_identity_rep X)"

definition book_C_proposition_j where
  "book_C_proposition_j \<Sigma> B G actual w = inv_into
    (book_C_identity_domain (fst w) G (snd w) Prop) (book_C_proposition_h \<Sigma> B G actual w)"

context book_C_canonical_frame
begin

lemma proposition_h_class:
  assumes world: "w \<in> worlds" and pm: "P \<in> book_closed_terms (fst w) G Prop"
  shows "book_C_proposition_h \<Sigma> B G actual w (book_C_identity_class (fst w) G (snd w) Prop P) =
    book_C_proposition_profile \<Sigma> B G actual w P"
proof -
  interpret W: book_C_identity_world "fst w" G "snd w"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF book_C_rooted_world_data(1)[OF world]])
  let ?X = "book_C_identity_class (fst w) G (snd w) Prop P"
  have xd: "?X \<in> book_C_identity_domain (fst w) G (snd w) Prop" unfolding book_C_identity_domain_def by (rule imageI[OF pm])
  have rm: "book_C_identity_rep ?X \<in> book_closed_terms (fst w) G Prop" by (rule W.identity_rep_typed[OF xd])
  have same: "book_C_identity_class (fst w) G (snd w) Prop (book_C_identity_rep ?X) = ?X" by (rule W.identity_rep_class[OF xd])
  show ?thesis unfolding book_C_proposition_h_def
    by (simp only: proposition_profiles_eq_iff_classes[OF world rm pm]; rule same)
qed

theorem proposition_h_bijection:
  assumes world: "w \<in> worlds"
  shows "bij_betw (book_C_proposition_h \<Sigma> B G actual w)
    (book_C_identity_domain (fst w) G (snd w) Prop) (book_C_proposition_domain \<Sigma> B G actual w)"
proof -
  let ?h = "book_C_proposition_h \<Sigma> B G actual w"
  let ?D = "book_C_identity_domain (fst w) G (snd w) Prop"
  have injective: "inj_on ?h ?D"
  proof (rule inj_onI)
    fix X Y
    assume xd: "X \<in> ?D" and yd: "Y \<in> ?D" and equal: "?h X = ?h Y"
    obtain P where pm: "P \<in> book_closed_terms (fst w) G Prop"
      and xs: "X = book_C_identity_class (fst w) G (snd w) Prop P"
      using xd unfolding book_C_identity_domain_def by blast
    obtain Q where qm: "Q \<in> book_closed_terms (fst w) G Prop"
      and ys: "Y = book_C_identity_class (fst w) G (snd w) Prop Q"
      using yd unfolding book_C_identity_domain_def by blast
    have profiles: "book_C_proposition_profile \<Sigma> B G actual w P = book_C_proposition_profile \<Sigma> B G actual w Q"
      using equal by (simp only: xs ys proposition_h_class[OF world pm] proposition_h_class[OF world qm])
    have classes: "book_C_identity_class (fst w) G (snd w) Prop P = book_C_identity_class (fst w) G (snd w) Prop Q"
      using profiles by (simp only: proposition_profiles_eq_iff_classes[OF world pm qm])
    show "X = Y" by (simp only: xs ys; rule classes)
  qed
  have image: "?h ` ?D = book_C_proposition_domain \<Sigma> B G actual w"
    unfolding book_C_identity_domain_def book_C_proposition_domain_def
    using proposition_h_class[OF world] by (auto simp: image_image)
  show ?thesis unfolding bij_betw_def by (rule conjI[OF injective image])
qed

theorem proposition_jh:
  assumes world: "w \<in> worlds" and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
  shows "book_C_proposition_j \<Sigma> B G actual w (book_C_proposition_h \<Sigma> B G actual w X) = X"
proof -
  have injective: "inj_on (book_C_proposition_h \<Sigma> B G actual w) (book_C_identity_domain (fst w) G (snd w) Prop)"
    using proposition_h_bijection[OF world] unfolding bij_betw_def by (rule conjunct1)
  show ?thesis unfolding book_C_proposition_j_def by (rule inv_into_f_f[OF injective xd])
qed

theorem proposition_hj:
  assumes world: "w \<in> worlds" and yd: "Y \<in> book_C_proposition_domain \<Sigma> B G actual w"
  shows "book_C_proposition_h \<Sigma> B G actual w (book_C_proposition_j \<Sigma> B G actual w Y) = Y"
proof -
  have image: "book_C_proposition_h \<Sigma> B G actual w ` book_C_identity_domain (fst w) G (snd w) Prop =
    book_C_proposition_domain \<Sigma> B G actual w"
    using proposition_h_bijection[OF world] unfolding bij_betw_def by (rule conjunct2)
  have member: "Y \<in> book_C_proposition_h \<Sigma> B G actual w ` book_C_identity_domain (fst w) G (snd w) Prop"
    using yd by (simp only: image)
  show ?thesis unfolding book_C_proposition_j_def by (rule f_inv_into_f[OF member])
qed

theorem proposition_profile_truncation:
  assumes world: "w \<in> worlds" and access: "le w v"
  shows "book_C_proposition_profile \<Sigma> B G actual v P =
    book_C_proposition_profile \<Sigma> B G actual w P \<inter> {u\<in>worlds. le v u}"
proof -
  have trans: "le v u \<Longrightarrow> le w u" for u by (rule book_C_rooted_trans[OF world access]; assumption)
  show ?thesis unfolding book_C_proposition_profile_def using trans by blast
qed

theorem proposition_h_naturality:
  assumes world: "w \<in> worlds" and target: "v \<in> worlds" and access: "le w v"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
  shows "book_C_proposition_h \<Sigma> B G actual v (book_C_term_counterpart G w v Prop X) =
    book_C_proposition_h \<Sigma> B G actual w X \<inter> {u\<in>worlds. le v u}"
proof -
  have ww: "w \<in> book_C_canonical_worlds \<Sigma> B G" by (rule book_C_rooted_world_data(1)[OF world])
  have vv: "v \<in> book_C_canonical_worlds \<Sigma> B G" by (rule book_C_rooted_world_data(1)[OF target])
  obtain P where pm: "P \<in> book_closed_terms (fst w) G Prop"
    and shape: "X = book_C_identity_class (fst w) G (snd w) Prop P"
    using xd unfolding book_C_identity_domain_def by blast
  have pv: "P \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich ww vv access pm])
  show ?thesis by (simp only: shape book_C_term_counterpart_class[OF rich ww vv access pm]
    proposition_h_class[OF target pv] proposition_h_class[OF world pm]; rule proposition_profile_truncation[OF world access])
qed

theorem proposition_domain_future:
  assumes member: "Y \<in> book_C_proposition_domain \<Sigma> B G actual w"
  shows "Y \<subseteq> {v\<in>worlds. le w v}"
  using member unfolding book_C_proposition_domain_def book_C_proposition_profile_def by blast

theorem proposition_profile_at_world:
  assumes world: "w \<in> worlds"
  shows "w \<in> book_C_proposition_profile \<Sigma> B G actual w P \<longleftrightarrow> P \<in> snd w"
  using world book_C_rooted_refl[OF world] unfolding book_C_proposition_profile_def by blast

theorem proposition_domain_truncation:
  assumes world: "w \<in> worlds" and target: "v \<in> worlds" and access: "le w v"
    and member: "Y \<in> book_C_proposition_domain \<Sigma> B G actual w"
  shows "Y \<inter> {u\<in>worlds. le v u} \<in> book_C_proposition_domain \<Sigma> B G actual v"
proof -
  obtain P where pm: "P \<in> book_closed_terms (fst w) G Prop"
    and shape: "Y = book_C_proposition_profile \<Sigma> B G actual w P"
    using member unfolding book_C_proposition_domain_def by blast
  have pv: "P \<in> book_closed_terms (fst v) G Prop" by (rule book_C_closed_terms_future[OF rich
    book_C_rooted_world_data(1)[OF world] book_C_rooted_world_data(1)[OF target] access pm])
  have typed: "book_C_proposition_profile \<Sigma> B G actual v P \<in> book_C_proposition_domain \<Sigma> B G actual v"
    unfolding book_C_proposition_domain_def by (rule imageI[OF pv])
  show ?thesis by (simp only: shape proposition_profile_truncation[OF world access, symmetric]; rule typed)
qed

text \<open>
  The proposition domain consists exactly of the future truth sets of
  closed sentences. The functions hᵗ and jᵗ are actually defined and
  proved inverse on their respective domains. The map hᵗ commutes with
  counterparts and the literal future restriction of proposition sets.
  This completes the inverse-map calculation at type t only. It does
  not supply the inductive functional-type maps, their domain closure,
  or the full modal-model/truth theorem.
\<close>

end

end
