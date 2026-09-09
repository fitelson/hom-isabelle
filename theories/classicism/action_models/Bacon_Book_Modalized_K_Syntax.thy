theory Bacon_Book_Modalized_K_Syntax
  imports Bacon_Book_Modalized_Exponential_Transport
begin

section \<open>The explicitly normalized curried K family\<close>

definition book_modalized_K_inner ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> 'b set) \<Rightarrow>
    ('w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> ('w \<times> 'b) \<Rightarrow> 'a" where
  "book_modalized_K_inner W le B iA v a p =
    (if p \<in> book_modalized_exponential_pairs W le B v then iA v (fst p) a else undefined)"

definition book_modalized_K ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> 'a set) \<Rightarrow>
    ('w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('w \<Rightarrow> 'b set) \<Rightarrow>
    'w \<Rightarrow> ('w \<times> 'a) \<Rightarrow> ('w \<times> 'b) \<Rightarrow> 'a" where
  "book_modalized_K W le A iA B w p =
    (if p \<in> book_modalized_exponential_pairs W le A w
      then book_modalized_K_inner W le B iA (fst p) (snd p) else undefined)"

lemma book_modalized_K_inner_on:
  assumes pair: "(z,b) \<in> book_modalized_exponential_pairs W le B v"
  shows "book_modalized_K_inner W le B iA v a (z,b) = iA v z a"
  by (simp add: book_modalized_K_inner_def pair)

lemma book_modalized_K_on:
  assumes pair: "(v,a) \<in> book_modalized_exponential_pairs W le A w"
  shows "book_modalized_K W le A iA B w (v,a) = book_modalized_K_inner W le B iA v a"
  by (simp add: book_modalized_K_def pair)

lemma book_modalized_K_value:
  assumes first: "(v,a) \<in> book_modalized_exponential_pairs W le A w"
    and second: "(z,b) \<in> book_modalized_exponential_pairs W le B v"
  shows "book_modalized_K W le A iA B w (v,a) (z,b) = iA v z a"
  by (simp only: book_modalized_K_on[OF first] book_modalized_K_inner_on[OF second])

context book_preorder
begin

lemma book_modalized_K_future_pair_earlier:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and related: "le w v"
    and pair: "p \<in> book_modalized_exponential_pairs worlds le A v"
  shows "p \<in> book_modalized_exponential_pairs worlds le A w"
proof -
  obtain z a where shape: "p = (z,a)" by (cases p) auto
  have zw: "z \<in> worlds" and vz: "le v z" and member: "a \<in> A z"
    using pair by (simp_all add: shape book_modalized_exponential_pairs_iff)
  have wz: "le w z" by (rule transitive[OF ww vw zw related vz])
  show ?thesis by (simp only: shape book_modalized_exponential_pairs_iff;
    rule conjI[OF zw conjI[OF wz member]])
qed

theorem book_modalized_K_truncation:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and related: "le w v"
  shows "book_modalized_exponential_transport worlds le A v (book_modalized_K worlds le A iA B w) =
    book_modalized_K worlds le A iA B v"
proof (rule ext)
  fix p
  show "book_modalized_exponential_transport worlds le A v (book_modalized_K worlds le A iA B w) p =
      book_modalized_K worlds le A iA B v p"
  proof (cases "p \<in> book_modalized_exponential_pairs worlds le A v")
    case True
    have earlier: "p \<in> book_modalized_exponential_pairs worlds le A w"
      by (rule book_modalized_K_future_pair_earlier[OF ww vw related True])
    show ?thesis by (simp only: book_modalized_exponential_transport_def book_modalized_K_def True earlier if_True)
  next
    case False
    show ?thesis by (simp only: book_modalized_exponential_transport_def book_modalized_K_def False if_False)
  qed
qed

end

text \<open>
  Exercise 17.6, p.364, gives k_w(v,a)(z,b)=iA_vz(a) on
  w≤v≤z. Both function levels are normalized outside their own
  valid future pairs. The formula never freezes a value at w or
  restricts future homomorphisms to extensions of global maps.
  Membership in the full modalized exponential is proved separately.
\<close>

end
