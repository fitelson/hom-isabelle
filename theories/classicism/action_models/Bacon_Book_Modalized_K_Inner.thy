theory Bacon_Book_Modalized_K_Inner
  imports Bacon_Book_Modalized_K_Syntax
begin

section \<open>The inner constant family is a homomorphism on every future cone\<close>

theorem book_modalized_K_inner_member:
  assumes source: "book_modalized_set W le A iA" and argument_set: "book_modalized_set W le B iB"
    and vw: "v \<in> W" and member: "a \<in> A v"
  shows "book_modalized_K_inner W le B iA v a \<in> book_modalized_exponential W le B iB A iA v"
proof -
  interpret A: book_modalized_set W le A iA by (rule source)
  interpret B: book_modalized_set W le B iB by (rule argument_set)
  show ?thesis
  proof (rule book_modalized_exponentialI)
    fix p
    assume outside: "p \<notin> book_modalized_exponential_pairs W le B v"
    show "book_modalized_K_inner W le B iA v a p = undefined"
      by (simp add: book_modalized_K_inner_def outside)
  next
    fix z b
    assume zw: "z \<in> W" and vz: "le v z" and bm: "b \<in> B z"
    have pair: "(z,b) \<in> book_modalized_exponential_pairs W le B v"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF zw conjI[OF vz bm]])
    have typed: "iA v z a \<in> A z" by (rule A.counterpart_type[OF vw zw vz member])
    show "book_modalized_K_inner W le B iA v a (z,b) \<in> A z"
      by (simp only: book_modalized_K_inner_on[OF pair]; rule typed)
  next
    fix z u b
    assume zw: "z \<in> W" and vz: "le v z" and uw: "u \<in> W" and zu: "le z u" and bm: "b \<in> B z"
    have vu: "le v u" by (rule A.transitive[OF vw zw uw vz zu])
    have transported: "iB z u b \<in> B u" by (rule B.counterpart_type[OF zw uw zu bm])
    have first_pair: "(z,b) \<in> book_modalized_exponential_pairs W le B v"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF zw conjI[OF vz bm]])
    have second_pair: "(u,iB z u b) \<in> book_modalized_exponential_pairs W le B v"
      by (simp only: book_modalized_exponential_pairs_iff; rule conjI[OF uw conjI[OF vu transported]])
    have coherent: "iA z u (iA v z a) = iA v u a"
      by (rule A.counterpart_compose[OF vw zw uw vz zu member, symmetric])
    show "iA z u (book_modalized_K_inner W le B iA v a (z,b)) =
        book_modalized_K_inner W le B iA v a (u,iB z u b)"
      by (simp only: book_modalized_K_inner_on[OF first_pair] book_modalized_K_inner_on[OF second_pair]; rule coherent)
  qed
qed

theorem book_modalized_K_inner_transport:
  assumes source: "book_modalized_set W le A iA"
    and vw: "v \<in> W" and uw: "u \<in> W" and related: "le v u" and member: "a \<in> A v"
  shows "book_modalized_exponential_transport W le B u (book_modalized_K_inner W le B iA v a) =
    book_modalized_K_inner W le B iA u (iA v u a)"
proof -
  interpret A: book_modalized_set W le A iA by (rule source)
  show ?thesis
  proof (rule ext)
    fix p
    show "book_modalized_exponential_transport W le B u (book_modalized_K_inner W le B iA v a) p =
        book_modalized_K_inner W le B iA u (iA v u a) p"
    proof (cases "p \<in> book_modalized_exponential_pairs W le B u")
      case True
      obtain z b where shape: "p = (z,b)" by (cases p) auto
      have zw: "z \<in> W" and uz: "le u z"
        using True by (simp_all add: shape book_modalized_exponential_pairs_iff)
      have earlier: "p \<in> book_modalized_exponential_pairs W le B v"
        by (rule A.book_modalized_K_future_pair_earlier[OF vw uw related True])
      have coherent: "iA v z a = iA u z (iA v u a)"
        by (rule A.counterpart_compose[OF vw uw zw related uz member])
      show ?thesis
        by (simp only: book_modalized_exponential_transport_def book_modalized_K_inner_def
          True earlier if_True shape fst_conv; rule coherent)
    next
      case False
      show ?thesis by (simp only: book_modalized_exponential_transport_def
        book_modalized_K_inner_def False if_False)
    qed
  qed
qed

text \<open>
  The ignored argument b still ranges over the entire B future fiber,
  and its transported value is explicitly typed in the naturality proof.
  The retained a is transported from v to each later world. Inner
  truncation agrees with first transporting a, by A's composition law.
  No nonempty fiber, global-extension assumption, PER or quotient is used.
\<close>

end
