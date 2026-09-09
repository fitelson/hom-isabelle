theory Bacon_Source_Named_Nat_Strong_Completeness
  imports Bacon_Source_Named_Nat_Countermodel Bacon_Source_Named_H_Soundness
begin

section \<open>Closed native consequence over all natural-number-domain named models\<close>

text \<open>
  For a countable declared signature and named sentences S,A, native
  S ⊢H A iff every named BBK model on natural-number domains satisfying
  S satisfies A. Source: the countable-domain sentence-consequence
  refinement of Bacon–Dorr Theorem 3.2, pp.44–45.

  Isabelle representation. The predicate independently quantifies over
  every D:otype → nat set, J:nat named_assignment → named_term → nat,
  and V:nat → bool satisfying the named model clauses. Neither a
  translated validity predicate nor an image-of-tags condition occurs.
  Sentence satisfaction quantifies over all typed partial assignments.
  Closedness supplies adequacy; it does not eliminate typing.

  Scope. Full F, a rich stock G, and countability of the declared names
  ⋃σΣσ, not a countable ambient name type. No additional consistency,
  closed signature inhabitants, or premise-set finiteness is assumed.
  The theorem concerns closed consequence on the fixed carrier nat,
  not arbitrary open completeness or quantification over HOL carrier
  types. General soundness is separately carrier-polymorphic.
\<close>

definition paper_named_nat_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_named_nat_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> nat set.
     \<forall>J :: nat named_assignment \<Rightarrow>
       'c paper_named_term \<Rightarrow> nat.
     \<forall>V :: nat \<Rightarrow> bool.
       paper_named_bbk_model \<Sigma> G D J V \<longrightarrow>
       (\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)) \<longrightarrow>
       (\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)))"

lemma paper_named_nat_consequence_apply:
  fixes \<Sigma> :: "'c ssignature"
    and D :: "otype \<Rightarrow> nat set"
  assumes consequence: "paper_named_nat_consequence \<Sigma> G S A"
    and model: "paper_named_bbk_model \<Sigma> G D J V"
    and realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
  shows "\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)"
proof -
  note all_models = consequence[unfolded paper_named_nat_consequence_def]
  note at_domain = spec[where x=D, OF all_models]
  note at_denote = spec[where x=J, OF at_domain]
  note at_valuation = spec[where x=V, OF at_denote]
  show ?thesis by (rule mp[OF mp[OF at_valuation model] realizes])
qed

theorem paper_named_nat_closed_strong_completeness:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set" and A :: "'c paper_named_term"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
  shows "paper_named_derivable \<Sigma> G S A \<longleftrightarrow> paper_named_nat_consequence \<Sigma> G S A"
proof
  assume derivation: "paper_named_derivable \<Sigma> G S A"
  show "paper_named_nat_consequence \<Sigma> G S A"
  proof (unfold paper_named_nat_consequence_def, intro allI)
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
  assume consequence: "paper_named_nat_consequence \<Sigma> G S A"
  show "paper_named_derivable \<Sigma> G S A"
  proof (rule ccontr)
    assume not_derivable: "\<not> paper_named_derivable \<Sigma> G S A"
    obtain D :: "otype \<Rightarrow> nat set"
      and J V where model: "paper_named_bbk_model \<Sigma> G D J V"
      and realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
      and falsifies: "\<forall>g. named_env_typed D G g \<longrightarrow> \<not> V (J g A)"
      using paper_named_nat_closed_countermodel[OF countable_signature sentences language closed rich not_derivable]
      by (elim exE conjE)
    have all_true: "\<forall>g. named_env_typed D G g \<longrightarrow> V (J g A)"
      by (rule paper_named_nat_consequence_apply[OF consequence model realizes])
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
