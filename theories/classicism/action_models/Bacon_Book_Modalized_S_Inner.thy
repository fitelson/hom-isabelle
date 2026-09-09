theory Bacon_Book_Modalized_S_Inner
  imports Bacon_Book_Modalized_S_Syntax
begin

section \<open>The inner application family is a future-cone homomorphism\<close>

context book_modalized_S_data
begin

lemma book_modalized_S_inner_type:
  assumes yw: "y \<in> W" and zw: "z \<in> W" and yz: "le y z"
    and fm: "f \<in> S_A_BC y" and gm: "g \<in> S_AB z"
    and ww: "w \<in> W" and zwr: "le z w" and am: "a \<in> A w"
  shows "book_modalized_S_inner z f g (w,a) \<in> C w"
proof -
  have ywrel: "le y w" by (rule A.transitive[OF yw zw ww yz zwr])
  have ft: "f (w,a) \<in> S_BC w"
    by (rule book_modalized_exponential_type[OF fm ww ywrel am])
  have gt: "g (w,a) \<in> B w"
    by (rule book_modalized_exponential_type[OF gm ww zwr am])
  have result_type: "f (w,a) (w,g (w,a)) \<in> C w"
    by (rule book_modalized_exponential_type[OF ft ww A.reflexive[OF ww] gt])
  show ?thesis using result_type ww zwr am
    by (simp add: book_modalized_S_inner_def book_modalized_exponential_pairs_iff)
qed

lemma book_modalized_S_inner_natural:
  assumes yw: "y \<in> W" and zw: "z \<in> W" and yz: "le y z"
    and fm: "f \<in> S_A_BC y" and gm: "g \<in> S_AB z"
    and ww: "w \<in> W" and zwr: "le z w"
    and uw: "u \<in> W" and wu: "le w u" and am: "a \<in> A w"
  shows "iC w u (book_modalized_S_inner z f g (w,a)) =
    book_modalized_S_inner z f g (u,iA w u a)"
proof -
  have ywrel: "le y w" by (rule A.transitive[OF yw zw ww yz zwr])
  have zu: "le z u" by (rule A.transitive[OF zw ww uw zwr wu])
  have at: "iA w u a \<in> A u" by (rule A.counterpart_type[OF ww uw wu am])
  have ft: "f (w,a) \<in> S_BC w"
    by (rule book_modalized_exponential_type[OF fm ww ywrel am])
  have gt: "g (w,a) \<in> B w"
    by (rule book_modalized_exponential_type[OF gm ww zwr am])
  have bt: "iB w u (g (w,a)) \<in> B u"
    by (rule B.counterpart_type[OF ww uw wu gt])
  have gn: "iB w u (g (w,a)) = g (u,iA w u a)"
    by (rule book_modalized_exponential_natural[OF gm ww zwr uw wu am])
  have fn: "book_modalized_exponential_transport W le B u (f (w,a)) = f (u,iA w u a)"
    by (rule book_modalized_exponential_natural[OF fm ww ywrel uw wu am])
  have inner_natural: "iC w u (f (w,a) (w,g (w,a))) =
      f (w,a) (u,iB w u (g (w,a)))"
    by (rule book_modalized_exponential_natural[OF ft ww A.reflexive[OF ww] uw wu gt])
  have later_pair: "(u,iB w u (g (w,a))) \<in> book_modalized_exponential_pairs W le B u"
    using uw A.reflexive[OF uw] bt by (simp add: book_modalized_exponential_pairs_iff)
  have evaluated: "f (w,a) (u,iB w u (g (w,a))) =
      f (u,iA w u a) (u,iB w u (g (w,a)))"
    using fun_cong[OF fn, of "(u,iB w u (g (w,a)))"]
    by (simp only: book_modalized_exponential_transport_on[OF later_pair])
  show ?thesis
    using inner_natural evaluated gn ww zwr am uw zu at
    by (simp add: book_modalized_S_inner_def book_modalized_exponential_pairs_iff)
qed

theorem book_modalized_S_inner_member:
  assumes yw: "y \<in> W" and zw: "z \<in> W" and yz: "le y z"
    and fm: "f \<in> S_A_BC y" and gm: "g \<in> S_AB z"
  shows "book_modalized_S_inner z f g \<in> S_AC z"
proof (rule book_modalized_exponentialI)
  fix p
  assume outside: "p \<notin> book_modalized_exponential_pairs W le A z"
  show "book_modalized_S_inner z f g p = undefined"
    using outside by (cases p) (simp add: book_modalized_S_inner_def)
next
  fix w a
  assume ww: "w \<in> W" and zwr: "le z w" and am: "a \<in> A w"
  show "book_modalized_S_inner z f g (w,a) \<in> C w"
    by (rule book_modalized_S_inner_type[OF yw zw yz fm gm ww zwr am])
next
  fix w u a
  assume ww: "w \<in> W" and zwr: "le z w" and uw: "u \<in> W"
    and wu: "le w u" and am: "a \<in> A w"
  show "iC w u (book_modalized_S_inner z f g (w,a)) =
      book_modalized_S_inner z f g (u,iA w u a)"
    by (rule book_modalized_S_inner_natural[OF yw zw yz fm gm ww zwr uw wu am])
qed

text \<open>
  The argument uses naturality of g, naturality of f into B ⇒ C, and
  naturality of the particular local homomorphism f(w,a). Thus every
  later-world argument is covered; no extension to a global map is used.
\<close>

end
end
