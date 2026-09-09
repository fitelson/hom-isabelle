theory Bacon_Book_Modal_Term_Action
  imports Bacon_Book_Modal_Term_Transport
begin

section \<open>Counterpart laws and naturality of term application\<close>

theorem book_C_term_counterpart_identity:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_C_term_counterpart G w w \<sigma> X = X"
proof -
  obtain A where am: "A \<in> book_closed_terms (fst w) G \<sigma>"
    and shape: "X = book_C_identity_class (fst w) G (snd w) \<sigma> A"
    using xd unfolding book_C_identity_domain_def by blast
  show ?thesis by (simp only: shape; rule book_C_term_counterpart_class[OF rich w w book_C_canonical_le_refl[OF rich w] am])
qed

theorem book_C_term_counterpart_composition:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and u: "u \<in> book_C_canonical_worlds \<Sigma> B G"
    and wv: "book_C_canonical_le G w v" and vu: "book_C_canonical_le G v u"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_C_term_counterpart G v u \<sigma> (book_C_term_counterpart G w v \<sigma> X) = book_C_term_counterpart G w u \<sigma> X"
proof -
  obtain A where am: "A \<in> book_closed_terms (fst w) G \<sigma>"
    and shape: "X = book_C_identity_class (fst w) G (snd w) \<sigma> A"
    using xd unfolding book_C_identity_domain_def by blast
  have av: "A \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v wv am])
  have wu: "book_C_canonical_le G w u" by (rule book_C_canonical_le_trans[OF rich w wv vu])
  show ?thesis by (simp only: shape book_C_term_counterpart_class[OF rich w v wv am]
    book_C_term_counterpart_class[OF rich v u vu av] book_C_term_counterpart_class[OF rich w u wu am])
qed

theorem book_C_term_application_naturality:
  assumes rich: "sg_rich G" and w: "w \<in> book_C_canonical_worlds \<Sigma> B G"
    and v: "v \<in> book_C_canonical_worlds \<Sigma> B G" and access: "book_C_canonical_le G w v"
    and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) (Arr \<sigma> \<tau>)"
    and yd: "Y \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  shows "book_C_term_counterpart G w v \<tau> (book_C_term_app (fst w) G (snd w) \<sigma> \<tau> X Y) =
    book_C_term_app (fst v) G (snd v) \<sigma> \<tau>
      (book_C_term_counterpart G w v (Arr \<sigma> \<tau>) X) (book_C_term_counterpart G w v \<sigma> Y)"
proof -
  interpret W: book_C_identity_world "fst w" G "snd w"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF w])
  interpret V: book_C_identity_world "fst v" G "snd v"
    by (unfold_locales; rule rich book_C_canonical_world_data(4)[OF v])
  obtain F where fm: "F \<in> book_closed_terms (fst w) G (Arr \<sigma> \<tau>)"
    and xs: "X = book_C_identity_class (fst w) G (snd w) (Arr \<sigma> \<tau>) F"
    using xd unfolding book_C_identity_domain_def by blast
  obtain A where am: "A \<in> book_closed_terms (fst w) G \<sigma>"
    and ys: "Y = book_C_identity_class (fst w) G (snd w) \<sigma> A"
    using yd unfolding book_C_identity_domain_def by blast
  have fv: "F \<in> book_closed_terms (fst v) G (Arr \<sigma> \<tau>)" by (rule book_C_closed_terms_future[OF rich w v access fm])
  have av: "A \<in> book_closed_terms (fst v) G \<sigma>" by (rule book_C_closed_terms_future[OF rich w v access am])
  have fa: "NApp F A \<in> book_closed_terms (fst w) G \<tau>" by (rule book_closed_terms_App[OF fm am])
  show ?thesis by (simp only: xs ys W.term_app_classes[OF fm am]
    book_C_term_counterpart_class[OF rich w v access fa]
    book_C_term_counterpart_class[OF rich w v access fm] book_C_term_counterpart_class[OF rich w v access am]
    V.term_app_classes[OF fv av])
qed

text \<open>
  iww is the identity and ivu ∘ iwv = iwu on each typed domain.
  Application commutes with counterparts:
  iwv(Appw(X,Y)) = Appv(iwv(X),iwv(Y)). Each equation follows by
  choosing actual closed representatives and applying the class formulas.
  This verifies the algebraic modalized-structure laws, not nonemptiness,
  quasi-functionality, λ interpretation, or the homomorphism representation
  and truth lemma required for a full modal model.
\<close>

end
