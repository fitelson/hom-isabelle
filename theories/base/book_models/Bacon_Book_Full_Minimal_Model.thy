theory Bacon_Book_Full_Minimal_Model
  imports Bacon_Book_Full_Environment Bacon_Book_Closed_Values Bacon_Book_Implication_Valuation
begin

section \<open>A full-language minimal-basis model with witnessed logical denotations\<close>

text \<open>
  The minimal basis Λ⁻ contains →:t→t→t and ∀σ:(σ→t)→t.
  Their values κ(→), κ(∀σ) satisfy material implication and universal
  quantification, and some proposition is false (Bacon, Definition 15.1,
  pp.314–315). A value κ(l) is explicitly witnessed as the interpretation
  of its closed logical term, following Convention 14.3, p.298.

  Isabelle representation. book_full_minimal_model specializes the full
  environment to book_minimal_logical_type. Its logical signature UNIV
  contains only SImp and the SBAll family, not all of the book's richer
  primitive bases. Witnessed closed values are an explicit definedness
  condition; they are not derived from a potentially empty space of total
  assignments in the raw environment. In a rich stock they imply nonempty
  domains, rather than nonemptiness being imposed as an additional field.

  Scope. This is the full typed F language over the minimal basis with
  witnessed logical denotations. It is not an equivalence with Definition
  15.1 for arbitrary admitted 𝒥, arbitrary partial logical signatures, or
  every possible convention concerning closed values when no assignment
  exists. No Functionality, actual-identity clause, separation, soundness,
  completeness, or quotient theorem is asserted by this definition.
\<close>

locale book_full_minimal_model =
  book_full_environment domain app book_minimal_logical_type UNIV signature stock denote
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and signature :: "'c ssignature" and stock :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c, book_minimal_logical) named_term \<Rightarrow> 'v" +
  fixes V :: "'v \<Rightarrow> bool" and \<kappa> :: "book_minimal_logical \<Rightarrow> 'v"
  assumes logical_closed_value:
    "book_closed_value (book_minimal_logical_type l) (NLogical l) (\<kappa> l)"
    and implication_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) p) q) = (V p \<longrightarrow> V q)"
    and forall_truth:
    "f \<in> domain (Arr \<sigma> Prop) \<Longrightarrow>
     V (app (Arr \<sigma> Prop) Prop (\<kappa> (SBAll \<sigma>)) f) =
       (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
    and false_proposition: "\<exists>f \<in> domain Prop. \<not> V f"
begin

lemma book_minimal_logical_value_type:
  "\<kappa> l \<in> domain (book_minimal_logical_type l)"
  by (rule book_closed_value_type[OF logical_closed_value])

lemma book_minimal_logical_value_at:
  assumes typed: "book_env_typed domain stock g"
  shows "denote g (NLogical l) = \<kappa> l"
  by (rule book_closed_value_at[OF logical_closed_value typed])

lemma book_minimal_implication_value_type:
  "\<kappa> SImp \<in> domain (Arr Prop (Arr Prop Prop))"
  using book_minimal_logical_value_type[where l=SImp] by (simp only: book_minimal_logical_type.simps)

lemma book_minimal_forall_value_type:
  "\<kappa> (SBAll \<sigma>) \<in> domain (Arr (Arr \<sigma> Prop) Prop)"
  using book_minimal_logical_value_type[where l="SBAll \<sigma>"] by (simp only: book_minimal_logical_type.simps)

theorem book_minimal_assignment_exists:
  "\<exists>g. book_env_typed domain stock g"
  using logical_closed_value[where l=SImp] unfolding book_closed_value_def by blast

theorem book_minimal_domains_nonempty:
  assumes rich: "sg_rich stock"
  shows "domain \<sigma> \<noteq> {}"
proof -
  obtain g where typed: "book_env_typed domain stock g"
    using book_minimal_assignment_exists by (elim exE)
  show ?thesis by (rule book_env_domains_nonempty[OF rich typed])
qed

theorem book_minimal_leibniz_valuation:
  assumes equivalent: "book_leibniz_equiv domain app V Prop a b"
  shows "V a = V b"
  by (rule book_leibniz_valuation_from_implication[OF book_minimal_implication_value_type implication_truth equivalent])

end

end
