theory Bacon_Book_Primitive_Disjunction_Model
  imports Bacon_Book_Disjunction_Formula_Syntax
    Bacon_Book_Full_Environment Bacon_Book_Closed_Values
begin

section \<open>Independent native models with both primitive conjunction and disjunction\<close>

text \<open>
  The native vocabulary contains →, ∀σ, primitive ∧ and primitive ∨.
  Both primitive values have their all-domain truth clauses:
  v((κ(∧)·p)·q) ↔ v(p)∧v(q), and
  v((κ(∨)·p)·q) ↔ v(p)∨v(q).
  Source: §5.2, p.104, and Definition 15.1, p.314.

  This is an independent full-language interface, not an encoded model
  image or a claim of model existence. Every κ(l) is an actual
  assignment-witnessed closed denotation. The inherited implication,
  universal, conjunction and false-proposition clauses remain explicit.
  No Functionality, primitive/defined operator identity, actual equality,
  separation, proof judgment or consistency premise is added.

  Scope: full F over this cumulative basis, with arbitrary nonlogical
  signatures. Other primitives, partial bases and general sublanguages
  require separate results. The later existence theorem must construct
  every field rather than assume this locale.
\<close>

locale book_disjunction_model =
  book_full_environment domain app book_disj_logical_type UNIV signature stock denote
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and signature :: "'c ssignature" and stock :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_disj_term \<Rightarrow> 'v" +
  fixes V :: "'v \<Rightarrow> bool" and \<kappa> :: "book_disj_logical \<Rightarrow> 'v"
  assumes logical_closed_value:
    "book_closed_value (book_disj_logical_type l) (NLogical l) (\<kappa> l)"
    and implication_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BDConjunction (BCMinimal SImp))) p) q) =
       (V p \<longrightarrow> V q)"
    and forall_truth:
    "f \<in> domain (Arr \<sigma> Prop) \<Longrightarrow>
     V (app (Arr \<sigma> Prop) Prop (\<kappa> (BDConjunction (BCMinimal (SBAll \<sigma>)))) f) =
       (\<forall>a\<in>domain \<sigma>. V (app \<sigma> Prop f a))"
    and conjunction_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BDConjunction BCAnd)) p) q) = (V p \<and> V q)"
    and disjunction_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> BDOr) p) q) = (V p \<or> V q)"
    and false_proposition: "\<exists>p\<in>domain Prop. \<not> V p"
begin

lemma book_disjunction_logical_value_type:
  "\<kappa> l \<in> domain (book_disj_logical_type l)"
  by (rule book_closed_value_type[OF logical_closed_value])

lemma book_disjunction_logical_value_at:
  assumes typed: "book_env_typed domain stock g"
  shows "denote g (NLogical l) = \<kappa> l"
  by (rule book_closed_value_at[OF logical_closed_value typed])

lemma book_disjunction_implication_value_type:
  "\<kappa> (BDConjunction (BCMinimal SImp)) \<in> domain (Arr Prop (Arr Prop Prop))"
  using book_disjunction_logical_value_type[where l="BDConjunction (BCMinimal SImp)"]
  by (simp only: book_disj_logical_type.simps book_conj_logical_type.simps book_minimal_logical_type.simps)

lemma book_disjunction_forall_value_type:
  "\<kappa> (BDConjunction (BCMinimal (SBAll \<sigma>))) \<in> domain (Arr (Arr \<sigma> Prop) Prop)"
  using book_disjunction_logical_value_type[where l="BDConjunction (BCMinimal (SBAll \<sigma>))"]
  by (simp only: book_disj_logical_type.simps book_conj_logical_type.simps book_minimal_logical_type.simps)

lemma book_disjunction_and_value_type:
  "\<kappa> (BDConjunction BCAnd) \<in> domain book_disj_type"
  using book_disjunction_logical_value_type[where l="BDConjunction BCAnd"]
  by (simp only: book_disj_logical_type.simps book_conj_logical_type.simps)

lemma book_disjunction_or_value_type:
  "\<kappa> BDOr \<in> domain book_disj_type"
  using book_disjunction_logical_value_type[where l=BDOr]
  by (simp only: book_disj_logical_type.simps)

theorem book_disjunction_assignment_exists:
  "\<exists>g. book_env_typed domain stock g"
  using logical_closed_value[where l="BDConjunction (BCMinimal SImp)"]
  unfolding book_closed_value_def by blast

corollary book_disjunction_domains_nonempty:
  assumes rich: "sg_rich stock"
  shows "domain \<sigma> \<noteq> {}"
proof -
  obtain g where typed: "book_env_typed domain stock g"
    using book_disjunction_assignment_exists by blast
  show ?thesis by (rule book_env_domains_nonempty[OF rich typed])
qed

end

end
