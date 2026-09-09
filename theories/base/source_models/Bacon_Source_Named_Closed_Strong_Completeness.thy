theory Bacon_Source_Named_Closed_Strong_Completeness
  imports Bacon_Source_Named_Closed_Countermodel Bacon_Source_Named_H_Soundness
begin

section \<open>Closed native consequence over all named models on an explicit carrier\<close>

text \<open>
  For a named sentence set S and named sentence A, S ⊢H A iff every
  named BBK model satisfying S satisfies A, on the displayed canonical
  carrier. Source: the sentence-consequence form of Bacon–Dorr
  Theorem 3.2, pp.44–45, for the represented full F language.

  Isabelle representation. The predicate quantifies over every domain
  family, interpretation, and valuation on
  K = otype × ('c phenkin_full_name) pHc_value. It contains no encoding,
  tagged-domain-image restriction, or reference to a constructed-model
  predicate. Closedness removes adequacy conditions, not assignment
  typing: satisfaction still quantifies only over typed partial assignments.

  Status. Arbitrary sentence sets and signatures in a rich stock, with
  an explicit fixed HOL carrier rather than quantification over carrier
  types. Native soundness is separately carrier-polymorphic. No countability,
  closed signature inhabitants, or independent consistency premise is added.
  This does not extend the theorem to open premise/conclusion completeness,
  the book's general models, R-only syntax, or Classicism semantics.
\<close>

definition paper_named_canonical_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_named_canonical_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set.
     \<forall>J :: (otype \<times> ('c phenkin_full_name) pHc_value) named_assignment \<Rightarrow>
       'c paper_named_term \<Rightarrow> otype \<times> ('c phenkin_full_name) pHc_value.
     \<forall>V :: (otype \<times> ('c phenkin_full_name) pHc_value) \<Rightarrow> bool.
       paper_named_bbk_model \<Sigma> G D J V \<longrightarrow>
       (\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)) \<longrightarrow>
       (\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)))"

lemma paper_named_canonical_consequence_apply:
  fixes \<Sigma> :: "'c ssignature"
    and D :: "otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set"
  assumes consequence: "paper_named_canonical_consequence \<Sigma> G S A"
    and model: "paper_named_bbk_model \<Sigma> G D J V"
    and realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
  shows "\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)"
proof -
  note all_models = consequence[unfolded paper_named_canonical_consequence_def]
  note at_domain = spec[where x=D, OF all_models]
  note at_denote = spec[where x=J, OF at_domain]
  note at_valuation = spec[where x=V, OF at_denote]
  show ?thesis by (rule mp[OF mp[OF at_valuation model] realizes])
qed

theorem paper_named_closed_strong_completeness:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set" and A :: "'c paper_named_term"
  assumes sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S A \<longleftrightarrow> paper_named_canonical_consequence \<Sigma> G S A"
proof
  assume derivation: "paper_named_derivable \<Sigma> G S A"
  show "paper_named_canonical_consequence \<Sigma> G S A"
  proof (unfold paper_named_canonical_consequence_def, intro allI)
    fix D J V
    show "paper_named_bbk_model \<Sigma> G D J V \<longrightarrow>
      (\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)) \<longrightarrow>
      (\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A))"
    proof (intro impI)
      assume model: "paper_named_bbk_model \<Sigma> G D J V"
        and realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
      interpret Named: paper_named_bbk_model \<Sigma> G D J V by (rule model)
      show "\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)"
      proof (intro allI impI)
        fix g
        assume typed: "named_env_typed D G g"
        have adequate: "named_adequate g A" by (simp add: named_adequate_def closed)
        have premise_languages: "named_in_language paper_logical_type \<Sigma> G B Prop"
          if "B \<in> S" for B
          by (rule paper_named_sentence_member_language[OF sentences that])
        have premise_adequacy: "named_adequate g B" if member: "B \<in> S" for B
        proof -
          have sentence: "named_fv B = {}" by (rule paper_named_sentence_member_closed[OF sentences member])
          show "named_adequate g B" by (simp add: named_adequate_def sentence)
        qed
        have premise_truth: "V (J g B)" if member: "B \<in> S" for B
          by (rule mp[OF spec[where x=g, OF bspec[OF realizes member]] typed])
        show "V (J g A)" by (rule Named.paper_named_local_soundness[OF derivation
          premise_languages typed adequate premise_adequacy premise_truth])
      qed
    qed
  qed
next
  assume consequence: "paper_named_canonical_consequence \<Sigma> G S A"
  show "paper_named_derivable \<Sigma> G S A"
  proof (rule ccontr)
    assume not_derivable: "\<not> paper_named_derivable \<Sigma> G S A"
    obtain D :: "otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set"
      and J V where model: "paper_named_bbk_model \<Sigma> G D J V"
      and realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
      and falsifies: "\<forall>g. named_env_typed D G g \<longrightarrow> \<not> V (J g A)"
      using paper_named_closed_countermodel[OF sentences language closed rich not_derivable]
      by (elim exE conjE)
    have all_true: "\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)"
      by (rule paper_named_canonical_consequence_apply[OF consequence model realizes])
    have empty_typed: "named_env_typed D G Map.empty"
      by (simp add: named_env_typed_def)
    have yes: "V (J Map.empty A)"
      by (rule mp[OF spec[where x=Map.empty, OF all_true] empty_typed])
    have no: "\<not> V (J Map.empty A)"
      by (rule mp[OF spec[where x=Map.empty, OF falsifies] empty_typed])
    show False by (rule notE[OF no yes])
  qed
qed

end
