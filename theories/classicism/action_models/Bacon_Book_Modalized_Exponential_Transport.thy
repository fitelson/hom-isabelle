theory Bacon_Book_Modalized_Exponential_Transport
  imports Bacon_Book_Modalized_Exponential_Codec Bacon_Book_Modalized_Set Bacon_Source_Exponential_Action
begin

section \<open>Truncation is exponential precomposition on the thin category\<close>

definition book_modalized_exponential_transport ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> 'a set) \<Rightarrow>
    'w \<Rightarrow> (('w \<times> 'a) \<Rightarrow> 'b) \<Rightarrow> (('w \<times> 'a) \<Rightarrow> 'b)" where
  "book_modalized_exponential_transport W le A v f =
    (\<lambda>p. if p \<in> book_modalized_exponential_pairs W le A v then f p else undefined)"

lemma book_modalized_exponential_transport_on:
  "(u,a) \<in> book_modalized_exponential_pairs W le A v \<Longrightarrow>
    book_modalized_exponential_transport W le A v f (u,a) = f (u,a)"
  by (simp add: book_modalized_exponential_transport_def)

theorem book_modalized_exponential_transport_correspondence:
  fixes f :: "('w \<times> 'a) \<Rightarrow> 'b"
  assumes world: "v \<in> W"
  shows "paper_exponential_transport (book_preorder_arrows W le) fst snd book_preorder_compose A (w,v)
      (book_modalized_exponential_encode w f) =
    book_modalized_exponential_encode v (book_modalized_exponential_transport W le A v f)"
proof (rule ext)
  fix p :: "('w \<times> 'w) \<times> 'a"
  obtain h a where shape: "p = (h,a)" by (cases p) auto
  show "paper_exponential_transport (book_preorder_arrows W le) fst snd book_preorder_compose A (w,v)
      (book_modalized_exponential_encode w f) p =
    book_modalized_exponential_encode v (book_modalized_exponential_transport W le A v f) p"
    using world by (auto simp: shape paper_exponential_transport_def paper_exponential_pairs_iff
      book_preorder_arrow_member book_preorder_compose_def book_modalized_exponential_encode_def
      book_modalized_exponential_transport_def book_modalized_exponential_pairs_iff)
qed

theorem book_modalized_exponential_transport_type:
  assumes source: "book_modalized_set W le A iA" and target: "book_modalized_set W le B iB"
    and ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v"
    and member: "f \<in> book_modalized_exponential W le A iA B iB w"
  shows "book_modalized_exponential_transport W le A v f \<in> book_modalized_exponential W le A iA B iB v"
proof -
  have source_action: "paper_action W (book_preorder_arrows W le) fst snd book_preorder_compose book_preorder_identity
      A (\<lambda>h. iA (fst h) (snd h))" by (rule book_modalized_set.book_modalized_set_action[OF source])
  have target_action: "paper_action W (book_preorder_arrows W le) fst snd book_preorder_compose book_preorder_identity
      B (\<lambda>h. iB (fst h) (snd h))" by (rule book_modalized_set.book_modalized_set_action[OF target])
  interpret E: paper_action W "book_preorder_arrows W le" fst snd book_preorder_compose book_preorder_identity
    "book_modalized_arrow_exponential W le A iA B iB"
    "paper_exponential_transport (book_preorder_arrows W le) fst snd book_preorder_compose A"
    by (rule paper_exponential_action_from_actions[OF source_action target_action])
  have arrow: "(w,v) \<in> book_preorder_arrows W le" using ww vw related by simp
  have encoded: "book_modalized_exponential_encode w f \<in> book_modalized_arrow_exponential W le A iA B iB w"
    by (rule book_modalized_exponential_encode_type[OF ww member])
  have source_member: "book_modalized_exponential_encode w f \<in> book_modalized_arrow_exponential W le A iA B iB (fst (w,v))"
    using encoded by simp
  have moved: "paper_exponential_transport (book_preorder_arrows W le) fst snd book_preorder_compose A (w,v)
      (book_modalized_exponential_encode w f) \<in> book_modalized_arrow_exponential W le A iA B iB v"
    using E.transport_type[OF arrow source_member] by simp
  have decoded: "book_modalized_exponential_decode v
      (paper_exponential_transport (book_preorder_arrows W le) fst snd book_preorder_compose A (w,v)
        (book_modalized_exponential_encode w f)) \<in> book_modalized_exponential W le A iA B iB v"
    by (rule book_modalized_exponential_decode_type[OF vw moved])
  show ?thesis using decoded by (simp only: book_modalized_exponential_transport_correspondence[OF vw]
    book_modalized_exponential_decode_encode)
qed

lemma book_modalized_exponential_transport_identity:
  assumes member: "f \<in> book_modalized_exponential W le A iA B iB w"
  shows "book_modalized_exponential_transport W le A w f = f"
proof (rule ext)
  fix p
  show "book_modalized_exponential_transport W le A w f p = f p"
  proof (cases "p \<in> book_modalized_exponential_pairs W le A w")
    case True
    show ?thesis by (simp add: book_modalized_exponential_transport_def True)
  next
    case False
    have zero: "f p = undefined" by (rule book_modalized_exponential_normal[OF member False])
    show ?thesis by (simp add: book_modalized_exponential_transport_def False zero)
  qed
qed

context book_preorder
begin

lemma book_modalized_exponential_transport_compose:
  assumes vw: "v \<in> worlds" and uw: "u \<in> worlds" and related: "le v u"
  shows "book_modalized_exponential_transport worlds le A u (book_modalized_exponential_transport worlds le A v f) =
    book_modalized_exponential_transport worlds le A u f"
proof (rule ext)
  fix p
  show "book_modalized_exponential_transport worlds le A u (book_modalized_exponential_transport worlds le A v f) p =
    book_modalized_exponential_transport worlds le A u f p"
  proof (cases "p \<in> book_modalized_exponential_pairs worlds le A u")
    case True
    obtain z a where shape: "p = (z,a)" by (cases p) auto
    have zw: "z \<in> worlds" and uz: "le u z" and argument: "a \<in> A z"
      using True by (simp_all add: shape book_modalized_exponential_pairs_iff)
    have vz: "le v z" by (rule transitive[OF vw uw zw related uz])
    have earlier: "p \<in> book_modalized_exponential_pairs worlds le A v"
      by (simp only: shape book_modalized_exponential_pairs_iff; rule conjI[OF zw conjI[OF vz argument]])
    show ?thesis by (simp only: book_modalized_exponential_transport_def True earlier if_True)
  next
    case False
    show ?thesis by (simp only: book_modalized_exponential_transport_def False if_False)
  qed
qed

end

theorem book_modalized_exponential_is_modalized_set:
  assumes source: "book_modalized_set W le A iA" and target: "book_modalized_set W le B iB"
  shows "book_modalized_set W le (book_modalized_exponential W le A iA B iB)
    (\<lambda>w v. book_modalized_exponential_transport W le A v)"
proof -
  interpret Source: book_modalized_set W le A iA by (rule source)
  show ?thesis
  proof unfold_locales
    fix w v f
    assume ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v"
      and member: "f \<in> book_modalized_exponential W le A iA B iB w"
    show "book_modalized_exponential_transport W le A v f \<in> book_modalized_exponential W le A iA B iB v"
      by (rule book_modalized_exponential_transport_type[OF source target ww vw related member])
  next
    fix w f
    assume "w \<in> W" and member: "f \<in> book_modalized_exponential W le A iA B iB w"
    show "book_modalized_exponential_transport W le A w f = f" by (rule book_modalized_exponential_transport_identity[OF member])
  next
    fix w v u f
    assume "w \<in> W" and vw: "v \<in> W" and uw: "u \<in> W" and "le w v" and related: "le v u"
      and "f \<in> book_modalized_exponential W le A iA B iB w"
    show "book_modalized_exponential_transport W le A u f =
      book_modalized_exponential_transport W le A u (book_modalized_exponential_transport W le A v f)"
      by (rule sym[OF Source.book_modalized_exponential_transport_compose[OF vw uw related]])
  qed
qed

text \<open>
  Transport is literal restriction to the later world's valid inputs,
  with the same normalized off-domain convention. Its fiber preservation
  and the final modalized-set certificate require BOTH actual endpoint
  modalized sets. No fullness, nonempty fiber, PER, quotient, interpretation
  or logical-model assertion is added. Source: Definition 17.9, p.364.
\<close>

end
