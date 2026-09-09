theory Bacon_Book_Preorder_Powerset
  imports Bacon_Book_Preorder_Category Bacon_Source_Powerset_Action
begin

section \<open>Future worlds, truncation, and the explicit fiber correspondence\<close>

definition book_preorder_future :: "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> 'w set" where
  "book_preorder_future W le w = {v\<in>W. le w v}"

definition book_preorder_truncate :: "('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> 'w set \<Rightarrow> 'w \<Rightarrow> 'w set" where
  "book_preorder_truncate le p v = {x\<in>p. le v x}"

definition book_preorder_powerset :: "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> 'w \<Rightarrow> 'w set set" where
  "book_preorder_powerset W le w = Pow (book_preorder_future W le w)"

definition book_preorder_powerset_transport :: "('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<times> 'w) \<Rightarrow> 'w set \<Rightarrow> 'w set" where
  "book_preorder_powerset_transport le f p = book_preorder_truncate le p (snd f)"

definition book_preorder_powerset_encode :: "'w \<Rightarrow> 'w set \<Rightarrow> ('w \<times> 'w) set" where
  "book_preorder_powerset_encode w p = image (\<lambda>v. (w,v)) p"

definition book_preorder_powerset_decode :: "('w \<times> 'w) set \<Rightarrow> 'w set" where
  "book_preorder_powerset_decode X = image snd X"

lemma book_preorder_encode_pair [simp]:
  "(u,v) \<in> book_preorder_powerset_encode w p \<longleftrightarrow> u = w \<and> v \<in> p"
  by (auto simp: book_preorder_powerset_encode_def)

lemma book_preorder_outgoing:
  assumes world: "w \<in> W"
  shows "paper_outgoing (book_preorder_arrows W le) fst w =
    book_preorder_powerset_encode w (book_preorder_future W le w)"
  using world by (auto simp: paper_outgoing_def book_preorder_arrows_def
    book_preorder_powerset_encode_def book_preorder_future_def)

lemma book_preorder_powerset_encode_type:
  assumes world: "w \<in> W" and fiber: "p \<in> book_preorder_powerset W le w"
  shows "book_preorder_powerset_encode w p \<in> paper_powerset_fiber (book_preorder_arrows W le) fst w"
  using world fiber
  by (auto simp: book_preorder_powerset_def book_preorder_future_def book_preorder_powerset_encode_def
    paper_powerset_fiber_def paper_outgoing_def book_preorder_arrows_def)

lemma book_preorder_powerset_decode_type:
  assumes fiber: "X \<in> paper_powerset_fiber (book_preorder_arrows W le) fst w"
  shows "book_preorder_powerset_decode X \<in> book_preorder_powerset W le w"
  using fiber
  by (auto simp: book_preorder_powerset_decode_def book_preorder_powerset_def book_preorder_future_def
    paper_powerset_fiber_def paper_outgoing_def book_preorder_arrow_member)

lemma book_preorder_powerset_decode_encode:
  "book_preorder_powerset_decode (book_preorder_powerset_encode w p) = p"
  by (simp add: book_preorder_powerset_decode_def book_preorder_powerset_encode_def image_image)

lemma book_preorder_powerset_encode_decode:
  assumes fiber: "X \<in> paper_powerset_fiber (book_preorder_arrows W le) fst w"
  shows "book_preorder_powerset_encode w (book_preorder_powerset_decode X) = X"
proof -
  have origin: "fst a = w" if "a \<in> X" for a
    using fiber that by (auto simp: paper_powerset_fiber_def paper_outgoing_def)
  have agree: "(w,snd a) = a" if "a \<in> X" for a
    using origin[OF that] by (cases a) simp
  have images: "image (\<lambda>a. (w,snd a)) X = image id X"
    by (rule image_cong[OF refl]; simp only: id_apply; rule agree; assumption)
  show ?thesis
    by (simp only: book_preorder_powerset_encode_def book_preorder_powerset_decode_def image_image;
      use images in simp)
qed

theorem book_preorder_powerset_bijection:
  assumes world: "w \<in> W"
  shows "bij_betw (book_preorder_powerset_encode w) (book_preorder_powerset W le w)
    (paper_powerset_fiber (book_preorder_arrows W le) fst w)"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (book_preorder_powerset_encode w) (book_preorder_powerset W le w)"
  proof (rule inj_onI)
    fix p q
    assume "p \<in> book_preorder_powerset W le w" "q \<in> book_preorder_powerset W le w"
      and same: "book_preorder_powerset_encode w p = book_preorder_powerset_encode w q"
    have decoded: "book_preorder_powerset_decode (book_preorder_powerset_encode w p) =
        book_preorder_powerset_decode (book_preorder_powerset_encode w q)"
      by (rule arg_cong[OF same])
    show "p = q" using decoded by (simp only: book_preorder_powerset_decode_encode)
  qed
next
  show "image (book_preorder_powerset_encode w) (book_preorder_powerset W le w) =
      paper_powerset_fiber (book_preorder_arrows W le) fst w"
  proof
    show "image (book_preorder_powerset_encode w) (book_preorder_powerset W le w) \<subseteq>
        paper_powerset_fiber (book_preorder_arrows W le) fst w"
      using book_preorder_powerset_encode_type[OF world] by blast
    show "paper_powerset_fiber (book_preorder_arrows W le) fst w \<subseteq>
        image (book_preorder_powerset_encode w) (book_preorder_powerset W le w)"
    proof
      fix X
      assume fiber: "X \<in> paper_powerset_fiber (book_preorder_arrows W le) fst w"
      show "X \<in> image (book_preorder_powerset_encode w) (book_preorder_powerset W le w)"
        by (rule image_eqI[where x="book_preorder_powerset_decode X"],
          rule book_preorder_powerset_encode_decode[OF fiber, symmetric],
          rule book_preorder_powerset_decode_type[OF fiber])
    qed
  qed
qed

section \<open>The counterpart functions are exactly truncation\<close>

theorem book_preorder_powerset_transport_correspondence:
  assumes arrow: "f \<in> book_preorder_arrows W le"
    and fiber: "p \<in> book_preorder_powerset W le (fst f)"
  shows "paper_powerset_transport (book_preorder_arrows W le) fst snd book_preorder_compose f
      (book_preorder_powerset_encode (fst f) p) =
    book_preorder_powerset_encode (snd f) (book_preorder_powerset_transport le f p)"
proof -
  have target_world: "snd f \<in> W" using arrow by (simp add: book_preorder_arrow_member)
  have subset: "p \<subseteq> W" using fiber
    by (auto simp: book_preorder_powerset_def book_preorder_future_def)
  show ?thesis
  proof (rule set_eqI)
    fix h
    show "(h \<in> paper_powerset_transport (book_preorder_arrows W le) fst snd book_preorder_compose f
        (book_preorder_powerset_encode (fst f) p)) =
      (h \<in> book_preorder_powerset_encode (snd f) (book_preorder_powerset_transport le f p))"
      using target_world subset
      by (cases h; auto simp: paper_powerset_transport_member book_preorder_arrow_member
        book_preorder_compose_def book_preorder_powerset_transport_def book_preorder_truncate_def)
  qed
qed

context book_preorder
begin

lemma book_preorder_truncate_identity:
  assumes fiber: "p \<in> book_preorder_powerset worlds le w"
  shows "book_preorder_truncate le p w = p"
  using fiber by (auto simp: book_preorder_powerset_def book_preorder_future_def book_preorder_truncate_def)

lemma book_preorder_truncate_compose:
  assumes vw: "v \<in> worlds" and uw: "u \<in> worlds" and related: "le v u" and subset: "p \<subseteq> worlds"
  shows "book_preorder_truncate le (book_preorder_truncate le p v) u = book_preorder_truncate le p u"
proof (rule set_eqI)
  fix x
  have extends: "le v x" if xp: "x \<in> p" and ux: "le u x"
    by (rule transitive[OF vw uw subsetD[OF subset xp] related ux])
  show "(x \<in> book_preorder_truncate le (book_preorder_truncate le p v) u) =
      (x \<in> book_preorder_truncate le p u)"
    using extends by (auto simp: book_preorder_truncate_def)
qed

theorem book_preorder_powerset_action:
  "paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
    (book_preorder_powerset worlds le) (book_preorder_powerset_transport le)"
proof unfold_locales
  fix f p
  assume "f \<in> book_preorder_arrows worlds le"
    and fiber: "p \<in> book_preorder_powerset worlds le (fst f)"
  show "book_preorder_powerset_transport le f p \<in> book_preorder_powerset worlds le (snd f)"
    using fiber by (auto simp: book_preorder_powerset_transport_def book_preorder_truncate_def
      book_preorder_powerset_def book_preorder_future_def)
next
  fix w p
  assume "w \<in> worlds" and fiber: "p \<in> book_preorder_powerset worlds le w"
  show "book_preorder_powerset_transport le (book_preorder_identity w) p = p"
    by (simp only: book_preorder_powerset_transport_def book_preorder_identity_def snd_conv;
      rule book_preorder_truncate_identity[OF fiber])
next
  fix f g p
  assume "f \<in> book_preorder_arrows worlds le" and second: "g \<in> book_preorder_arrows worlds le"
    and meeting: "snd f = fst g" and fiber: "p \<in> book_preorder_powerset worlds le (fst f)"
  have vw: "snd f \<in> worlds" and uw: "snd g \<in> worlds" and related: "le (snd f) (snd g)"
    using second by (simp_all add: book_preorder_arrow_member meeting)
  have subset: "p \<subseteq> worlds" using fiber by (auto simp: book_preorder_powerset_def book_preorder_future_def)
  show "book_preorder_powerset_transport le (book_preorder_compose g f) p =
      book_preorder_powerset_transport le g (book_preorder_powerset_transport le f p)"
    by (simp only: book_preorder_powerset_transport_def book_preorder_compose_def snd_conv;
      rule book_preorder_truncate_compose[OF vw uw related subset, symmetric])
qed

corollary book_preorder_arrow_powerset_action:
  "paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
    (paper_powerset_fiber (book_preorder_arrows worlds le) fst)
    (paper_powerset_transport (book_preorder_arrows worlds le) fst snd book_preorder_compose)"
  by (rule Category.paper_powerset_action)

end

context book_pointed_preorder
begin

lemma book_preorder_root_future:
  "book_preorder_future worlds le root = worlds"
  using root_below by (auto simp: book_preorder_future_def)

lemma book_preorder_root_powerset:
  "book_preorder_powerset worlds le root = Pow worlds"
  by (simp only: book_preorder_powerset_def book_preorder_root_future)

end

text \<open>
  Definition 17.2, p.359, is p↑v={x∈p | v≤x}. Example 17.1,
  p.360, has D_w=Pow(W↑w) and i_wv(p)=p↑v. The constructed
  action proves exactly the identity and composition conditions of
  Definition 17.3. The fiber bijection identifies future worlds v
  with outgoing arrows (w,v), and the transport equation proves the
  correspondence with the generic categorical powerset action.

  This is pure HOL set/category structure. No logical domain stock,
  λ interpretation, modal-model existence or completeness is asserted.
\<close>

end
