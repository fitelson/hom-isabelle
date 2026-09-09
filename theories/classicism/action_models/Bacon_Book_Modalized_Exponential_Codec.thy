theory Bacon_Book_Modalized_Exponential_Codec
  imports Bacon_Book_Modalized_Exponential_Domain Bacon_Source_Exponential_Domain
begin

abbreviation book_modalized_arrow_exponential where
  "book_modalized_arrow_exponential W le A iA B iB w \<equiv>
    paper_exponential_fiber (book_preorder_arrows W le) fst snd book_preorder_compose
      A (\<lambda>h. iA (fst h) (snd h)) B (\<lambda>h. iB (fst h) (snd h)) w"

definition book_modalized_exponential_encode ::
  "'w \<Rightarrow> (('w \<times> 'a) \<Rightarrow> 'b) \<Rightarrow> ((('w \<times> 'w) \<times> 'a) \<Rightarrow> 'b)" where
  "book_modalized_exponential_encode w f = (\<lambda>(h,a). if fst h = w then f (snd h,a) else undefined)"

definition book_modalized_exponential_decode ::
  "'w \<Rightarrow> ((('w \<times> 'w) \<times> 'a) \<Rightarrow> 'b) \<Rightarrow> (('w \<times> 'a) \<Rightarrow> 'b)" where
  "book_modalized_exponential_decode w b = (\<lambda>(v,a). b ((w,v),a))"

lemma book_modalized_exponential_encode_on:
  "book_modalized_exponential_encode w f ((w,v),a) = f (v,a)"
  by (simp add: book_modalized_exponential_encode_def)

lemma book_modalized_exponential_decode_on:
  "book_modalized_exponential_decode w b (v,a) = b ((w,v),a)"
  by (simp add: book_modalized_exponential_decode_def)

theorem book_modalized_exponential_encode_type:
  assumes world: "w \<in> W" and member: "f \<in> book_modalized_exponential W le A iA B iB w"
  shows "book_modalized_exponential_encode w f \<in> book_modalized_arrow_exponential W le A iA B iB w"
proof (rule paper_exponential_fiberI)
  fix p
  assume outside: "p \<notin> paper_exponential_pairs (book_preorder_arrows W le) fst snd A w"
  obtain h a where shape: "p = (h,a)" by (cases p) auto
  show "book_modalized_exponential_encode w f p = undefined"
  proof (cases "fst h = w")
    case True
    have absent: "(snd h,a) \<notin> book_modalized_exponential_pairs W le A w"
      using outside world True by (auto simp: shape paper_exponential_pairs_iff
        book_preorder_arrow_member book_modalized_exponential_pairs_iff)
    have zero: "f (snd h,a) = undefined" by (rule book_modalized_exponential_normal[OF member absent])
    show ?thesis by (simp add: shape book_modalized_exponential_encode_def True zero)
  next
    case False
    show ?thesis by (simp add: shape book_modalized_exponential_encode_def False)
  qed
next
  fix h a
  assume arrow: "h \<in> book_preorder_arrows W le" and origin: "fst h = w" and argument: "a \<in> A (snd h)"
  have target_world: "snd h \<in> W" and related: "le w (snd h)" using arrow origin
    by (simp_all add: book_preorder_arrow_member)
  have result: "f (snd h,a) \<in> B (snd h)"
    by (rule book_modalized_exponential_type[OF member target_world related argument])
  show "book_modalized_exponential_encode w f (h,a) \<in> B (snd h)"
    using result by (simp add: book_modalized_exponential_encode_def origin)
next
  fix h i a
  assume first: "h \<in> book_preorder_arrows W le" and origin: "fst h = w"
    and second: "i \<in> book_preorder_arrows W le" and meeting: "snd h = fst i" and argument: "a \<in> A (snd h)"
  have vw: "snd h \<in> W" and uw: "snd i \<in> W" and wv: "le w (snd h)" and vu: "le (snd h) (snd i)"
    using first second origin meeting by (simp_all add: book_preorder_arrow_member)
  have natural: "iB (snd h) (snd i) (f (snd h,a)) = f (snd i,iA (snd h) (snd i) a)"
    by (rule book_modalized_exponential_natural[OF member vw wv uw vu argument])
  show "iB (fst i) (snd i) (book_modalized_exponential_encode w f (h,a)) =
      book_modalized_exponential_encode w f (book_preorder_compose i h,iA (fst i) (snd i) a)"
    using natural by (simp add: book_modalized_exponential_encode_def book_preorder_compose_def origin meeting)
qed

theorem book_modalized_exponential_decode_type:
  assumes world: "w \<in> W" and member: "b \<in> book_modalized_arrow_exponential W le A iA B iB w"
  shows "book_modalized_exponential_decode w b \<in> book_modalized_exponential W le A iA B iB w"
proof (rule book_modalized_exponentialI)
  fix p
  assume outside: "p \<notin> book_modalized_exponential_pairs W le A w"
  obtain v a where shape: "p = (v,a)" by (cases p) auto
  have absent: "((w,v),a) \<notin> paper_exponential_pairs (book_preorder_arrows W le) fst snd A w"
    using outside by (simp add: shape book_modalized_exponential_pairs_iff paper_exponential_pairs_iff)
  have zero: "b ((w,v),a) = undefined" by (rule paper_exponential_fiber_normal[OF member absent])
  show "book_modalized_exponential_decode w b p = undefined" by (simp only: shape book_modalized_exponential_decode_on zero)
next
  fix v a
  assume vw: "v \<in> W" and related: "le w v" and argument: "a \<in> A v"
  have arrow: "(w,v) \<in> book_preorder_arrows W le" using world vw related by simp
  have origin: "fst (w,v) = w" by simp
  have av: "a \<in> A (snd (w,v))" using argument by simp
  have result: "b ((w,v),a) \<in> B (snd (w,v))" by (rule paper_exponential_fiber_type[OF member arrow origin av])
  show "book_modalized_exponential_decode w b (v,a) \<in> B v"
    using result by (simp only: book_modalized_exponential_decode_on snd_conv)
next
  fix v u a
  assume vw: "v \<in> W" and wv: "le w v" and uw: "u \<in> W" and vu: "le v u" and argument: "a \<in> A v"
  have first: "(w,v) \<in> book_preorder_arrows W le" using world vw wv by simp
  have second: "(v,u) \<in> book_preorder_arrows W le" using vw uw vu by simp
  have origin: "fst (w,v) = w" and meeting: "snd (w,v) = fst (v,u)" by simp_all
  have av: "a \<in> A (snd (w,v))" using argument by simp
  have natural: "iB v u (b ((w,v),a)) = b ((w,u),iA v u a)"
    using paper_exponential_fiber_coherent[OF member first origin second meeting av]
    by (simp add: book_preorder_compose_def)
  show "iB v u (book_modalized_exponential_decode w b (v,a)) =
      book_modalized_exponential_decode w b (u,iA v u a)"
    by (simp only: book_modalized_exponential_decode_on; rule natural)
qed

lemma book_modalized_exponential_decode_encode:
  "book_modalized_exponential_decode w (book_modalized_exponential_encode w f) = f"
  by (rule ext; case_tac x; simp add: book_modalized_exponential_decode_def book_modalized_exponential_encode_def)

lemma book_modalized_exponential_encode_decode:
  fixes b :: "(('w \<times> 'w) \<times> 'a) \<Rightarrow> 'b"
  assumes member: "b \<in> book_modalized_arrow_exponential W le A iA B iB w"
  shows "book_modalized_exponential_encode w (book_modalized_exponential_decode w b) = b"
proof (rule ext)
  fix p :: "('w \<times> 'w) \<times> 'a"
  obtain h a where shape: "p = (h,a)" by (cases p) auto
  show "book_modalized_exponential_encode w (book_modalized_exponential_decode w b) p = b p"
  proof (cases "fst h = w")
    case True
    have pair: "(w,snd h) = h" using True by (cases h) simp
    show ?thesis by (simp add: shape book_modalized_exponential_encode_def book_modalized_exponential_decode_def True pair)
  next
    case False
    have absent: "p \<notin> paper_exponential_pairs (book_preorder_arrows W le) fst snd A w"
      by (simp add: shape paper_exponential_pairs_iff False)
    have zero: "b p = undefined" by (rule paper_exponential_fiber_normal[OF member absent])
    show ?thesis by (simp add: shape book_modalized_exponential_encode_def False zero[unfolded shape])
  qed
qed

theorem book_modalized_exponential_bijection:
  assumes world: "w \<in> W"
  shows "bij_betw (book_modalized_exponential_encode w) (book_modalized_exponential W le A iA B iB w)
    (book_modalized_arrow_exponential W le A iA B iB w)"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (book_modalized_exponential_encode w) (book_modalized_exponential W le A iA B iB w)"
  proof (rule inj_onI)
    fix f g
    assume "f \<in> book_modalized_exponential W le A iA B iB w" and "g \<in> book_modalized_exponential W le A iA B iB w"
      and equal: "book_modalized_exponential_encode w f = book_modalized_exponential_encode w g"
    have decoded: "book_modalized_exponential_decode w (book_modalized_exponential_encode w f) =
        book_modalized_exponential_decode w (book_modalized_exponential_encode w g)" by (rule arg_cong[OF equal])
    show "f = g" using decoded by (simp only: book_modalized_exponential_decode_encode)
  qed
next
  show "book_modalized_exponential_encode w ` book_modalized_exponential W le A iA B iB w =
    book_modalized_arrow_exponential W le A iA B iB w"
  proof
    show "book_modalized_exponential_encode w ` book_modalized_exponential W le A iA B iB w \<subseteq>
      book_modalized_arrow_exponential W le A iA B iB w"
      by (rule image_subsetI; rule book_modalized_exponential_encode_type[OF world]; assumption)
  next
    show "book_modalized_arrow_exponential W le A iA B iB w \<subseteq>
      book_modalized_exponential_encode w ` book_modalized_exponential W le A iA B iB w"
    proof
      fix b
      assume member: "b \<in> book_modalized_arrow_exponential W le A iA B iB w"
      have decoded: "book_modalized_exponential_decode w b \<in> book_modalized_exponential W le A iA B iB w"
        by (rule book_modalized_exponential_decode_type[OF world member])
      show "b \<in> book_modalized_exponential_encode w ` book_modalized_exponential W le A iA B iB w"
        by (rule image_eqI[where x="book_modalized_exponential_decode w b" and f="book_modalized_exponential_encode w"],
          rule sym[OF book_modalized_exponential_encode_decode[OF member]], rule decoded)
    qed
  qed
qed

end
