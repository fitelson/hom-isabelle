theory Bacon_Book_Primitive_Conjunction_Model
  imports Bacon_Book_Primitive_Conjunction_Formula_Syntax
    Bacon_Book_Full_Environment Bacon_Book_Closed_Values
begin

section \<open>A full model with primitive conjunction\<close>

text \<open>
  Add a first-class value κ(∧):Dt→t→t to the minimal logical
  vocabulary, with v((κ(∧)·p)·q) iff v(p) and v(q), for every
  p,q∈Dt. The implication and universal clauses remain unchanged at
  the injected minimal symbols. Source: Bacon, §5.2, p.104, and
  Definition 15.1, p.314.

  This is an independent interface over the richer named terms. Each
  κ(l) is witnessed as an actual closed denotation of l. No λ-definition
  of ∧, identity with a defined operator, Functionality, separation, or
  actual-identity condition is required. The truth clause constrains
  material behavior, not identity of primitive and defined operations.

  Scope. The full F grammar and the minimal basis plus primitive ∧ are
  fixed here; arbitrary partial logical bases and admitted sublanguages
  are not claimed. Witnessed closed values retain the explicit definedness
  convention. There is no proof-calculus, consistency, encoding, or
  model-existence premise. The interface itself does not assert that a
  model satisfying these fields exists.
\<close>

locale book_conjunction_model =
  book_full_environment domain app book_conj_logical_type UNIV signature stock denote
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and signature :: "'c ssignature" and stock :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_conj_term \<Rightarrow> 'v" +
  fixes V :: "'v \<Rightarrow> bool" and \<kappa> :: "book_conj_logical \<Rightarrow> 'v"
  assumes logical_closed_value:
    "book_closed_value (book_conj_logical_type l) (NLogical l) (\<kappa> l)"
    and implication_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> (BCMinimal SImp)) p) q) =
       (V p \<longrightarrow> V q)"
    and forall_truth:
    "f \<in> domain (Arr \<sigma> Prop) \<Longrightarrow>
     V (app (Arr \<sigma> Prop) Prop (\<kappa> (BCMinimal (SBAll \<sigma>))) f) =
       (\<forall>a\<in>domain \<sigma>. V (app \<sigma> Prop f a))"
    and conjunction_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> BCAnd) p) q) = (V p \<and> V q)"
    and false_proposition: "\<exists>p\<in>domain Prop. \<not> V p"
begin

lemma book_conjunction_logical_value_type:
  "\<kappa> l \<in> domain (book_conj_logical_type l)"
  by (rule book_closed_value_type[OF logical_closed_value])

lemma book_conjunction_logical_value_at:
  assumes typed: "book_env_typed domain stock g"
  shows "denote g (NLogical l) = \<kappa> l"
  by (rule book_closed_value_at[OF logical_closed_value typed])

lemma book_conjunction_implication_value_type:
  "\<kappa> (BCMinimal SImp) \<in> domain (Arr Prop (Arr Prop Prop))"
  using book_conjunction_logical_value_type[where l="BCMinimal SImp"]
  by (simp only: book_conj_logical_type.simps book_minimal_logical_type.simps)

lemma book_conjunction_forall_value_type:
  "\<kappa> (BCMinimal (SBAll \<sigma>)) \<in> domain (Arr (Arr \<sigma> Prop) Prop)"
  using book_conjunction_logical_value_type[where l="BCMinimal (SBAll \<sigma>)"]
  by (simp only: book_conj_logical_type.simps book_minimal_logical_type.simps)

lemma book_conjunction_and_value_type:
  "\<kappa> BCAnd \<in> domain book_conj_type"
  using book_conjunction_logical_value_type[where l=BCAnd]
  by (simp only: book_conj_logical_type.simps)

theorem book_conjunction_assignment_exists:
  "\<exists>g. book_env_typed domain stock g"
  using logical_closed_value[where l="BCMinimal SImp"]
  unfolding book_closed_value_def by blast

corollary book_conjunction_domains_nonempty:
  assumes rich: "sg_rich stock"
  shows "domain \<sigma> \<noteq> {}"
proof -
  obtain g where typed: "book_env_typed domain stock g"
    using book_conjunction_assignment_exists by blast
  show ?thesis by (rule book_env_domains_nonempty[OF rich typed])
qed

end

end
