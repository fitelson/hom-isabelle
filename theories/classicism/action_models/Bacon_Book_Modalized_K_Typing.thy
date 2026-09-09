theory Bacon_Book_Modalized_K_Typing
  imports Bacon_Book_Modalized_K_Inner
begin

section \<open>Exercise 17.6: K belongs to the full iterated exponential\<close>

theorem book_modalized_K_member:
  assumes source: "book_modalized_set W le A iA" and argument_set: "book_modalized_set W le B iB"
    and ww: "w \<in> W"
  shows "book_modalized_K W le A iA B w \<in>
    book_modalized_exponential W le A iA
      (book_modalized_exponential W le B iB A iA)
      (\<lambda>v u. book_modalized_exponential_transport W le B u) w"
proof -
  interpret A: book_modalized_set W le A iA by (rule source)
  show ?thesis
  proof (rule book_modalized_exponentialI)
    fix p
    assume outside: "p \<notin> book_modalized_exponential_pairs W le A w"
    show "book_modalized_K W le A iA B w p = undefined"
      by (simp add: book_modalized_K_def outside)
  next
    fix v a
    assume vw: "v \<in> W" and wv: "le w v" and am: "a \<in> A v"
    have pair: "(v,a) \<in> book_modalized_exponential_pairs W le A w"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF vw conjI[OF wv am]])
    show "book_modalized_K W le A iA B w (v,a) \<in> book_modalized_exponential W le B iB A iA v"
      by (simp only: book_modalized_K_on[OF pair]; rule book_modalized_K_inner_member[OF source argument_set vw am])
  next
    fix v u a
    assume vw: "v \<in> W" and wv: "le w v" and uw: "u \<in> W" and vu: "le v u" and am: "a \<in> A v"
    have wu: "le w u" by (rule A.transitive[OF ww vw uw wv vu])
    have transported: "iA v u a \<in> A u" by (rule A.counterpart_type[OF vw uw vu am])
    have first_pair: "(v,a) \<in> book_modalized_exponential_pairs W le A w"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF vw conjI[OF wv am]])
    have second_pair: "(u,iA v u a) \<in> book_modalized_exponential_pairs W le A w"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF uw conjI[OF wu transported]])
    show "book_modalized_exponential_transport W le B u (book_modalized_K W le A iA B w (v,a)) =
        book_modalized_K W le A iA B w (u,iA v u a)"
      by (simp only: book_modalized_K_on[OF first_pair] book_modalized_K_on[OF second_pair];
        rule book_modalized_K_inner_transport[OF source vw uw vu am])
  qed
qed

theorem book_modalized_K_natural:
  assumes source: "book_modalized_set W le A iA"
    and ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v"
  shows "book_modalized_exponential_transport W le A v (book_modalized_K W le A iA B w) =
    book_modalized_K W le A iA B v"
proof -
  interpret A: book_modalized_set W le A iA by (rule source)
  show ?thesis by (rule A.book_modalized_K_truncation[OF ww vw related])
qed

text \<open>
  With actual modalized sets A and B, k_w is an element of
  (A⇒(B⇒A))_w for each w∈W. At every legitimate nested pair,
  its value is the source's iA_vz(a), and its counterpart at v
  is exactly k_v. These are the K assertions of Exercise 17.6,
  p.364. S, applicative interpretations, and full logical models
  are separate obligations; none is assumed or claimed here.
\<close>

end
