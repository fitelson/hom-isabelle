theory Bacon_Book_Printed_Binder_Freshening
  imports Bacon_Book_Printed_Free_For Bacon_Book_Alpha_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Prefix_Roundtrip
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Decoder_Freshness
begin

section \<open>The printed test is avoidance of every binder name\<close>

text \<open>
  N is printed-free for x in M iff FV(N)∩Bound(M) is empty.
  Source: Bacon, Definition 3.7, p.70. Unlike the existing exact-capture
  test, the printed test has no exception for unused or shadowed x.
  This equivalence characterizes the printed predicate only; it does
  not identify it pointwise with named_free_for.
\<close>

theorem book_printed_free_for_bound_names:
  "book_printed_free_for N x M \<longleftrightarrow> named_fv N \<inter> named_bound_names M = {}"
  by (induction M) auto

section \<open>An explicit freshened body from the existing binding decoder\<close>

text \<open>
  Let m cover the free-name indices of both M and N. Decode enc(M)
  using the chart [0,…,m−1]. Every decoder binder avoids that chart,
  hence avoids FV(N); the decoded result M′ has exactly enc(M).
  The proved encoding characterization gives M≡αM′.
  This implements the bound-variable freshening discussed immediately
  before Definition 3.7, pp.69–70.

  Representation. The construction is the existing decoder, not an assumed
  fresh variant or a new α definition. Richness supplies the decoder's
  same-type fresh binders. The language guard on M ensures its roundtrip;
  N need not be typed merely to specify the finite names to avoid.
  Partial logical signatures Λ and nonlogical signatures Σ are preserved.
  No β simulation, calculus equivalence or model theorem is claimed here.
\<close>

definition book_binder_freshening_bound ::
  "sgcontext \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> nat" where
  "book_binder_freshening_bound G N M =
    max (source_free_bound (named_to_source G [] M)) (source_free_bound (named_to_source G [] N))"

definition book_binder_freshen ::
  "sgcontext \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term \<Rightarrow> ('c,'l) named_term" where
  "book_binder_freshen G N M =
    source_to_named G [0..<book_binder_freshening_bound G N M] (named_to_source G [] M)"

lemma book_binder_freshening_body_bound:
  "source_free_bound (named_to_source G [] M) \<le> book_binder_freshening_bound G N M"
  unfolding book_binder_freshening_bound_def by (rule max.cobounded1)

lemma book_binder_freshening_payload_bound:
  "source_free_bound (named_to_source G [] N) \<le> book_binder_freshening_bound G N M"
  unfolding book_binder_freshening_bound_def by (rule max.cobounded2)

theorem book_binder_freshen_encoding:
  assumes rich: "sg_rich G" and language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
  shows "named_to_source G [] (book_binder_freshen G N M) = named_to_source G [] M"
  unfolding book_binder_freshen_def
  by (rule named_prefix_roundtrip_encoding[
    OF book_language_named[OF language] book_binder_freshening_body_bound rich])

theorem book_binder_freshen_alpha:
  assumes rich: "sg_rich G" and language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
  shows "named_alpha G M (book_binder_freshen G N M)"
proof -
  have encoding: "named_to_source G [] M = named_to_source G [] (book_binder_freshen G N M)"
    by (rule sym; rule book_binder_freshen_encoding[OF rich language])
  show ?thesis by (rule named_encoding_implies_alpha[OF rich encoding])
qed

theorem book_binder_freshen_language:
  assumes rich: "sg_rich G" and language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
  shows "book_in_language L \<Lambda> \<Sigma> G (book_binder_freshen G N M) \<tau>"
  by (rule iffD1[OF book_alpha_language_iff[OF book_binder_freshen_alpha[OF rich language]] language])

theorem book_binder_freshen_avoids:
  assumes rich: "sg_rich G"
  shows "named_fv N \<inter> named_bound_names (book_binder_freshen G N M) = {}"
proof -
  let ?m = "book_binder_freshening_bound G N M"
  have payload_in_chart: "named_fv N \<subseteq> set [0..< ?m]"
  proof
    fix n
    assume free: "n \<in> named_fv N"
    have before: "n < ?m"
      by (rule named_prefix_free_name[OF book_binder_freshening_payload_bound free])
    show "n \<in> set [0..< ?m]" using before by simp
  qed
  have binder_avoidance: "named_bound_names (book_binder_freshen G N M) \<inter> set [0..< ?m] = {}"
    unfolding book_binder_freshen_def by (rule source_to_named_bound_names_fresh[OF rich])
  show ?thesis using payload_in_chart binder_avoidance by blast
qed

corollary book_binder_freshen_printed_free_for:
  assumes rich: "sg_rich G"
  shows "book_printed_free_for N x (book_binder_freshen G N M)"
  by (rule iffD2[OF book_printed_free_for_bound_names book_binder_freshen_avoids[OF rich]])

theorem book_printed_binder_freshening:
  assumes rich: "sg_rich G" and language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
  shows "\<exists>M'. named_alpha G M M' \<and> book_in_language L \<Lambda> \<Sigma> G M' \<tau> \<and> book_printed_free_for N x M'"
  by (rule exI[where x="book_binder_freshen G N M"],
      rule conjI[OF book_binder_freshen_alpha[OF rich language]],
      rule conjI[OF book_binder_freshen_language[OF rich language] book_binder_freshen_printed_free_for[OF rich]])

corollary book_printed_beta_body_freshening:
  assumes rich: "sg_rich G"
    and body: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
    and payload: "book_in_language L \<Lambda> \<Sigma> G N (G x)"
  shows "\<exists>M'. named_alpha G M M' \<and> book_in_language L \<Lambda> \<Sigma> G M' \<tau> \<and>
    book_printed_free_for N x M' \<and> book_in_language L \<Lambda> \<Sigma> G (NApp (NLam x M') N) \<tau>"
proof -
  let ?M = "book_binder_freshen G N M"
  have alpha: "named_alpha G M ?M" by (rule book_binder_freshen_alpha[OF rich body])
  have language: "book_in_language L \<Lambda> \<Sigma> G ?M \<tau>"
    by (rule book_binder_freshen_language[OF rich body])
  have free_for: "book_printed_free_for N x ?M" by (rule book_binder_freshen_printed_free_for[OF rich])
  have redex: "book_in_language L \<Lambda> \<Sigma> G (NApp (NLam x ?M) N) \<tau>"
    by (rule book_language_App[OF book_language_Lam[OF language] payload])
  show ?thesis by (rule exI[where x="?M"], rule conjI[OF alpha conjI[OF language conjI[OF free_for redex]]])
qed

end
