theory Bacon_Source_Relational_Model_Restriction
  imports Bacon_Source_Relational_BBK_Interface
    Bacon_Source_Model_Development.Bacon_Source_Named_BBK_Interface
begin

section \<open>Restricting an F model to the R language\<close>

text \<open>
  Given an F model M=⟨D,J,V⟩, put Dᴿσ=Dσ for σ∈R and
  Dᴿσ={} otherwise. Retain J and V. Every typed Dᴿ-assignment is
  a typed D-assignment, and every R term and R conversion embeds into F.
  Thus these data satisfy the independent R clauses of Definition 3.1.

  Representation: paper_R_restrict_domain changes only the type family.
  Status: a one-way model reduct. No total-assignment completion is used;
  non-R variables remain unassigned. This proves neither that every R
  model extends to F nor R proof conservativity, completeness, or a
  category/profile equivalence between the two semantic classes.
\<close>

definition paper_R_restrict_domain :: "(otype \<Rightarrow> 'v set) \<Rightarrow> otype \<Rightarrow> 'v set" where
  "paper_R_restrict_domain D \<sigma> = (if paper_R_type \<sigma> then D \<sigma> else {})"

lemma paper_R_restrict_domain_on:
  assumes "paper_R_type \<sigma>"
  shows "paper_R_restrict_domain D \<sigma> = D \<sigma>"
  using assms by (simp add: paper_R_restrict_domain_def)

lemma paper_R_restrict_domain_off:
  assumes "\<not> paper_R_type \<sigma>"
  shows "paper_R_restrict_domain D \<sigma> = {}"
  using assms by (simp add: paper_R_restrict_domain_def)

lemma paper_R_restrict_domain_subset:
  "paper_R_restrict_domain D \<sigma> \<subseteq> D \<sigma>"
  by (simp add: paper_R_restrict_domain_def)

lemma paper_R_restricted_env_typed:
  assumes restricted: "named_env_typed (paper_R_restrict_domain D) G g"
  shows "named_env_typed D G g"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "g n = Some a"
  have member: "a \<in> paper_R_restrict_domain D (G n)"
    by (rule named_env_value[OF restricted assigned])
  show "a \<in> D (G n)" by (rule subsetD[OF paper_R_restrict_domain_subset member])
qed

context paper_named_bbk_model
begin

theorem paper_R_reduct_model:
  "paper_R_bbk_model signature stock (paper_R_restrict_domain domain) denote valuation"
proof (rule paper_R_bbk_model.intro)
  show "paper_R_rich stock" by (rule paper_R_rich_from_F[OF stock_rich])
next
  fix \<sigma>
  assume rt: "paper_R_type \<sigma>"
  show "paper_R_restrict_domain domain \<sigma> \<noteq> {}"
    by (simp only: paper_R_restrict_domain_on[OF rt]; rule domain_nonempty)
next
  fix \<sigma>
  assume outside: "\<not> paper_R_type \<sigma>"
  show "paper_R_restrict_domain domain \<sigma> = {}"
    by (rule paper_R_restrict_domain_off[OF outside])
next
  fix A \<sigma> g
  assume language: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and adequate: "named_adequate g A"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_language_result_type[OF language])
  have original: "denote g A \<in> domain \<sigma>"
    by (rule denote_type[OF paper_R_language_embedding[OF language]
      paper_R_restricted_env_typed[OF typed] adequate])
  show "denote g A \<in> paper_R_restrict_domain domain \<sigma>"
    using original by (simp only: paper_R_restrict_domain_on[OF rt])
next
  fix g n a
  assume typed: "named_env_typed (paper_R_restrict_domain domain) stock g" and assigned: "g n = Some a"
  show "denote g (NVar n) = a"
    by (rule denote_var[OF paper_R_restricted_env_typed[OF typed] assigned])
next
  fix F A H B \<sigma> \<tau> \<upsilon> \<rho> g h
  assume fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and hl: "paper_R_in_language signature stock H (Arr \<upsilon> \<rho>)"
    and bl: "paper_R_in_language signature stock B \<upsilon>"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ht: "named_env_typed (paper_R_restrict_domain domain) stock h"
    and ga: "named_adequate g (NApp F A)" and ha: "named_adequate h (NApp H B)"
    and heads: "denote g F = denote h H" and args: "denote g A = denote h B"
  show "denote g (NApp F A) = denote h (NApp H B)"
    by (rule denote_application_cong[OF paper_R_language_embedding[OF fl]
      paper_R_language_embedding[OF al] paper_R_language_embedding[OF hl]
      paper_R_language_embedding[OF bl] paper_R_restricted_env_typed[OF gt]
      paper_R_restricted_env_typed[OF ht] ga ha heads args])
next
  fix A \<sigma> g h
  assume al: "paper_R_in_language signature stock A \<sigma>"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ht: "named_env_typed (paper_R_restrict_domain domain) stock h"
    and ga: "named_adequate g A" and ha: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  show "denote g A = denote h A"
    by (rule denote_locality[OF paper_R_language_embedding[OF al]
      paper_R_restricted_env_typed[OF gt] paper_R_restricted_env_typed[OF ht] ga ha agree])
next
  fix A B \<sigma> g
  assume conversion: "paper_R_raw_beta_eta stock \<sigma> A B"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and bl: "paper_R_in_language signature stock B \<sigma>"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  show "denote g A = denote g B"
    by (rule denote_beta_eta[OF paper_R_raw_beta_eta_embedding[OF conversion]
      paper_R_language_embedding[OF al] paper_R_language_embedding[OF bl]
      paper_R_restricted_env_typed[OF gt] ga gb])
next
  fix A g
  assume al: "paper_R_in_language signature stock A Prop"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g" and ga: "named_adequate g A"
  show "valuation (denote g (NApp (NLogical SNot) A)) = (\<not> valuation (denote g A))"
    by (rule valuation_neg[OF paper_R_language_embedding[OF al] paper_R_restricted_env_typed[OF gt] ga])
next
  fix A B g
  assume al: "paper_R_in_language signature stock A Prop" and bl: "paper_R_in_language signature stock B Prop"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  show "valuation (denote g (NApp (NApp (NLogical SAnd) A) B)) =
      (valuation (denote g A) \<and> valuation (denote g B))"
    by (rule valuation_conj[OF paper_R_language_embedding[OF al] paper_R_language_embedding[OF bl]
      paper_R_restricted_env_typed[OF gt] ga gb])
next
  fix A B g
  assume al: "paper_R_in_language signature stock A Prop" and bl: "paper_R_in_language signature stock B Prop"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  show "valuation (denote g (NApp (NApp (NLogical SOr) A) B)) =
      (valuation (denote g A) \<or> valuation (denote g B))"
    by (rule valuation_disj[OF paper_R_language_embedding[OF al] paper_R_language_embedding[OF bl]
      paper_R_restricted_env_typed[OF gt] ga gb])
next
  fix F \<sigma> g n
  assume fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g F" and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  have original: "valuation (denote g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_forall[OF paper_R_language_embedding[OF fl] paper_R_restricted_env_typed[OF gt] ga nt fresh])
  show "valuation (denote g (NApp (NLogical (SAll \<sigma>)) F)) =
      (\<forall>a\<in>paper_R_restrict_domain domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    using original by (simp only: paper_R_restrict_domain_on[OF rt])
next
  fix F \<sigma> g n
  assume fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g F" and nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  have original: "valuation (denote g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    by (rule valuation_exists[OF paper_R_language_embedding[OF fl] paper_R_restricted_env_typed[OF gt] ga nt fresh])
  show "valuation (denote g (NApp (NLogical (SEx \<sigma>)) F)) =
      (\<exists>a\<in>paper_R_restrict_domain domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    using original by (simp only: paper_R_restrict_domain_on[OF rt])
next
  fix A B \<sigma> g
  assume al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    and gt: "named_env_typed (paper_R_restrict_domain domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  show "valuation (denote g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) = (denote g A = denote g B)"
    by (rule valuation_identity[OF paper_R_language_embedding[OF al] paper_R_language_embedding[OF bl]
      paper_R_restricted_env_typed[OF gt] ga gb])
qed

end

theorem paper_R_model_restriction:
  assumes model: "paper_named_bbk_model \<Sigma> G D J V"
  shows "paper_R_bbk_model \<Sigma> G (paper_R_restrict_domain D) J V"
proof -
  interpret Source: paper_named_bbk_model \<Sigma> G D J V by (rule model)
  show ?thesis by (rule Source.paper_R_reduct_model)
qed

end
