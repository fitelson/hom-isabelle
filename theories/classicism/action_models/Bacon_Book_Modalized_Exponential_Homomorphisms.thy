theory Bacon_Book_Modalized_Exponential_Homomorphisms
  imports Bacon_Book_Modalized_Exponential_Domain Bacon_Book_Modalized_Map
    Bacon_Book_Preorder_Powerset
begin

section \<open>The exponential contains exactly the normalized future homomorphisms\<close>

context book_preorder
begin

theorem book_modalized_exponential_iff_future_map:
  assumes world: "w \<in> worlds"
  shows "f \<in> book_modalized_exponential worlds le A iA B iB w \<longleftrightarrow>
    (\<forall>p. p \<notin> book_modalized_exponential_pairs worlds le A w \<longrightarrow> f p = undefined) \<and>
    book_modalized_map (book_preorder_future worlds le w) le A iA B iB (\<lambda>v a. f (v,a))"
proof
  assume member: "f \<in> book_modalized_exponential worlds le A iA B iB w"
  have normal: "\<forall>p. p \<notin> book_modalized_exponential_pairs worlds le A w \<longrightarrow> f p = undefined"
    by (intro allI impI; rule book_modalized_exponential_normal[OF member]; assumption)
  have family: "book_modalized_map (book_preorder_future worlds le w) le A iA B iB (\<lambda>v a. f (v,a))"
  proof (rule book_modalized_mapI)
    fix v a
    assume vf: "v \<in> book_preorder_future worlds le w" and av: "a \<in> A v"
    have vw: "v \<in> worlds" and wv: "le w v" using vf by (auto simp: book_preorder_future_def)
    show "f (v,a) \<in> B v" by (rule book_modalized_exponential_type[OF member vw wv av])
  next
    fix v u a
    assume vf: "v \<in> book_preorder_future worlds le w" and uf: "u \<in> book_preorder_future worlds le w"
      and vu: "le v u" and av: "a \<in> A v"
    have vw: "v \<in> worlds" and wv: "le w v" using vf by (auto simp: book_preorder_future_def)
    have uw: "u \<in> worlds" using uf by (simp add: book_preorder_future_def)
    show "f (u,iA v u a) = iB v u (f (v,a))"
      by (rule sym[OF book_modalized_exponential_natural[OF member vw wv uw vu av]])
  qed
  show "(\<forall>p. p \<notin> book_modalized_exponential_pairs worlds le A w \<longrightarrow> f p = undefined) \<and>
    book_modalized_map (book_preorder_future worlds le w) le A iA B iB (\<lambda>v a. f (v,a))"
    by (rule conjI[OF normal family])
next
  assume given: "(\<forall>p. p \<notin> book_modalized_exponential_pairs worlds le A w \<longrightarrow> f p = undefined) \<and>
    book_modalized_map (book_preorder_future worlds le w) le A iA B iB (\<lambda>v a. f (v,a))"
  have normal: "\<forall>p. p \<notin> book_modalized_exponential_pairs worlds le A w \<longrightarrow> f p = undefined"
    and family: "book_modalized_map (book_preorder_future worlds le w) le A iA B iB (\<lambda>v a. f (v,a))"
    using given by blast+
  show "f \<in> book_modalized_exponential worlds le A iA B iB w"
  proof (rule book_modalized_exponentialI)
    fix p
    assume "p \<notin> book_modalized_exponential_pairs worlds le A w"
    then show "f p = undefined" using normal by blast
  next
    fix v a
    assume vw: "v \<in> worlds" and wv: "le w v" and av: "a \<in> A v"
    have vf: "v \<in> book_preorder_future worlds le w" using vw wv by (simp add: book_preorder_future_def)
    show "f (v,a) \<in> B v" by (rule book_modalized_map_type[OF family vf av])
  next
    fix v u a
    assume vw: "v \<in> worlds" and wv: "le w v" and uw: "u \<in> worlds" and vu: "le v u" and av: "a \<in> A v"
    have wu: "le w u" by (rule transitive[OF world vw uw wv vu])
    have vf: "v \<in> book_preorder_future worlds le w" using vw wv by (simp add: book_preorder_future_def)
    have uf: "u \<in> book_preorder_future worlds le w" using uw wu by (simp add: book_preorder_future_def)
    show "iB v u (f (v,a)) = f (u,iA v u a)"
      by (rule sym[OF book_modalized_map_natural[OF family vf uf vu av]])
  qed
qed

end

text \<open>
  Definition 17.9(1), p.364, identifies (A⇒B)_w with all
  homomorphisms A↑w→B↑w. This theorem ties the independent
  exponential predicate to the independent typed/natural map predicate
  from Definition 17.4. Transitivity supplies the suppressed w≤u
  guard on a later counterpart target.

  Off-domain normalization removes only irrelevant total-HOL extensions.
  No global homomorphism or extension to worlds below w is required.
  As with the raw map predicate, actual modalized-set endpoints are
  separate when interpreting this equivalence as the book's construction.
\<close>

end
