theory Bacon_Book_Environment
  imports Bacon_Book_Applicative_Structure Bacon_Book_Language
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
begin

section \<open>Typed interpretation before the environment condition\<close>

text \<open>
  J assigns values to named terms at total typed assignments. Application
  uses the book's Appστ, not the paper's heterogeneous congruence field.
  Source: Bacon, Definitions 14.11 and 14.13, pp.296 and 302.

  The admitted set is an explicit syntactic parameter for the selected
  term collection. Source use for a general λ-language requires its
  independent language conditions; setting admitted = UNIV gives the full
  typed grammar over Λ and Σ. We do not assert that every arbitrary
  admitted set is a source λ-language. No nonemptiness, Functionality,
  valuation, or separation premise is inserted into these conditions.
\<close>

locale book_interpretation_structure = book_applicative_structure domain app
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes logical_type :: "'l \<Rightarrow> otype" and logical_signature :: "'l set"
    and signature :: "'c ssignature" and stock :: sgcontext
    and admitted :: "('c,'l) named_term set"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v"
  assumes denote_type:
    "A \<in> admitted \<Longrightarrow> book_in_language logical_type logical_signature signature stock A \<sigma> \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> denote g A \<in> domain \<sigma>"
    and denote_var:
    "NVar n \<in> admitted \<Longrightarrow> book_env_typed domain stock g \<Longrightarrow> denote g (NVar n) = g n"
    and denote_app:
    "F \<in> admitted \<Longrightarrow> A \<in> admitted \<Longrightarrow> NApp F A \<in> admitted \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock F (Arr \<sigma> \<tau>) \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock A \<sigma> \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow>
     denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (denote g A)"

section \<open>The environment condition uses the intersection of free names\<close>

text \<open>
  Jg(M) = Jh(N) when M ≡βη N and g,h agree on FV(M) ∩ FV(N).
  Source: the displayed third clause of Definition 14.13, p.302,
  checked visually.

  Both interpreted endpoints belong to the chosen term collection and
  signature. Raw typed βη is the ambient conversion relation; no extra
  assertion is made about membership of intermediate expressions in the
  chosen sublanguage. Total assignment typing is retained on both sides.
\<close>

locale book_environment_conditions = book_interpretation_structure +
  assumes environment:
    "A \<in> admitted \<Longrightarrow> B \<in> admitted \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock A \<sigma> \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock B \<sigma> \<Longrightarrow>
     named_raw_beta_eta logical_type stock \<sigma> A B \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> book_env_typed domain stock h \<Longrightarrow>
     (\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n) \<Longrightarrow>
     denote g A = denote h B"
begin

theorem book_denote_conversion:
  assumes aa: "A \<in> admitted" and ba: "B \<in> admitted"
    and al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and bl: "book_in_language logical_type logical_signature signature stock B \<sigma>"
    and conversion: "named_raw_beta_eta logical_type stock \<sigma> A B"
    and typed: "book_env_typed domain stock g"
  shows "denote g A = denote g B"
  by (rule environment[OF aa ba al bl conversion typed typed]) (rule refl)

theorem book_denote_locality:
  assumes aa: "A \<in> admitted"
    and al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "denote g A = denote h A"
proof -
  have raw: "named_raw_beta_eta logical_type stock \<sigma> A A"
    by (rule named_conversion_to_raw, rule named_beta_eta_in_language.Refl, rule book_language_named[OF al])
  show ?thesis
  proof (rule environment[OF aa aa al al raw gt ht])
    fix n
    assume shared: "n \<in> named_fv A \<inter> named_fv A"
    have member: "n \<in> named_fv A" using shared by simp
    show "g n = h n" by (rule agree[OF member])
  qed
qed

end

end
