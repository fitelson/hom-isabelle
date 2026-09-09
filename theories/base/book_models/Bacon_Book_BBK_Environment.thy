theory Bacon_Book_BBK_Environment
  imports Bacon_Book_BBK_Application Bacon_Book_Named_Translation
    Bacon_Book_Environment_Equivalence Bacon_Book_Full_Environment
begin

section \<open>A BBK interpretation supplies the book's structural environment\<close>

text \<open>
  Put Jbook(g,A) = J(g,trG(A)), and use the typed application operation
  already extracted from BBK variable applications. The result satisfies
  the book's environment condition on the full minimal language.
  Source: Bacon, Definitions 14.1, 14.11 and 14.13, pp.290,296,302.

  Representation. A total G-typed book assignment is typed on every
  finite prefix. Language translation supplies target typing and signature
  guards there. Exact FV preservation transfers locality. For raw named
  βη with in-language endpoints, rich G supplies the proved
  signature-relative conversion in a sufficiently large prefix.

  Status. This is a same-carrier structural bridge from pbbk_model,
  not a book logical model or valuation theorem. No Functionality,
  closed-term denotability, new carrier, or book-model premise is added.
  The intersection condition is recovered by the proved assignment-pasting
  equivalence, not imposed as an extra BBK field.
\<close>

lemma book_env_pbbk_prefix:
  assumes typed: "book_env_typed D G g"
  shows "pbbk_env_typed D (source_prefix G m) g"
proof (unfold pbbk_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume index: "lookup (source_prefix G m) n = Some \<sigma>"
  have bound: "n < m" using index by (auto simp: source_prefix_def lookup_def split: if_splits)
  have original: "lookup (source_prefix G m) n = Some (G n)"
    by (rule source_prefix_lookup[OF bound])
  have same_type: "G n = \<sigma>" using index original by simp
  have member: "g n \<in> D (G n)" by (rule book_env_at[where n=n, OF typed])
  show "g n \<in> D \<sigma>" using member by (simp only: same_type)
qed

context pbbk_model
begin

definition pbbk_book_denote ::
  "sgcontext \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'c book_named_term \<Rightarrow> 'v" where
  "pbbk_book_denote G g A = denote g (book_named_to_pterm G A)"

theorem pbbk_book_denote_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and typed: "book_env_typed domain G g"
  shows "pbbk_book_denote G g A \<in> domain \<tau>"
proof -
  let ?m = "source_free_bound (named_to_source G [] A)"
  have target_language: "pterm_in_language signature (source_prefix G ?m) (book_named_to_pterm G A) \<tau>"
    by (rule book_named_translation_language_prefix[OF language order_refl])
  note parts = target_language[unfolded pterm_in_language_def]
  show ?thesis unfolding pbbk_book_denote_def
    by (rule denote_type[OF conjunct1[OF parts] conjunct2[OF parts] book_env_pbbk_prefix[OF typed]])
qed

theorem pbbk_book_denote_var:
  assumes typed: "book_env_typed domain G g"
  shows "pbbk_book_denote G g (NVar n) = g n"
proof -
  have index: "lookup (source_prefix G (Suc n)) n = Some (G n)"
    by (rule source_prefix_lookup, rule lessI)
  have env: "pbbk_env_typed domain (source_prefix G (Suc n)) g"
    by (rule book_env_pbbk_prefix[OF typed])
  show ?thesis by (simp only: pbbk_book_denote_def book_named_translation_Var;
    rule denote_var[OF index env])
qed

theorem pbbk_book_denote_app:
  assumes fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
    and typed: "book_env_typed domain G g"
  shows "pbbk_book_denote G g (NApp F A) =
    pbbk_book_app \<sigma> \<tau> (pbbk_book_denote G g F) (pbbk_book_denote G g A)"
proof -
  let ?m = "max (source_free_bound (named_to_source G [] F)) (source_free_bound (named_to_source G [] A))"
  have fb: "source_free_bound (named_to_source G [] F) \<le> ?m" by simp
  have ab: "source_free_bound (named_to_source G [] A) \<le> ?m" by simp
  have f_language: "pterm_in_language signature (source_prefix G ?m) (book_named_to_pterm G F) (Arr \<sigma> \<tau>)"
    by (rule book_named_translation_language_prefix[OF fl fb])
  have a_language: "pterm_in_language signature (source_prefix G ?m) (book_named_to_pterm G A) \<sigma>"
    by (rule book_named_translation_language_prefix[OF al ab])
  note fd = f_language[unfolded pterm_in_language_def]
  note ad = a_language[unfolded pterm_in_language_def]
  have env: "pbbk_env_typed domain (source_prefix G ?m) g" by (rule book_env_pbbk_prefix[OF typed])
  show ?thesis by (simp only: pbbk_book_denote_def book_named_translation_App;
    rule pbbk_book_app_represents[OF conjunct1[OF fd] conjunct1[OF ad]
      conjunct2[OF fd] conjunct2[OF ad] env])
qed

theorem pbbk_book_denote_locality:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and gt: "book_env_typed domain G g" and ht: "book_env_typed domain G h"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "pbbk_book_denote G g A = pbbk_book_denote G h A"
proof -
  let ?m = "source_free_bound (named_to_source G [] A)"
  have target_language: "pterm_in_language signature (source_prefix G ?m) (book_named_to_pterm G A) \<tau>"
    by (rule book_named_translation_language_prefix[OF language order_refl])
  note parts = target_language[unfolded pterm_in_language_def]
  have genv: "pbbk_env_typed domain (source_prefix G ?m) g" by (rule book_env_pbbk_prefix[OF gt])
  have henv: "pbbk_env_typed domain (source_prefix G ?m) h" by (rule book_env_pbbk_prefix[OF ht])
  have target_agree: "g n = h n" if "n \<in> pbbk_fv (book_named_to_pterm G A)" for n
  proof -
    have free: "n \<in> named_fv A" using that by (simp only: book_named_translation_fv)
    show ?thesis by (rule agree[OF free])
  qed
  show ?thesis unfolding pbbk_book_denote_def
    by (rule denote_locality[OF conjunct1[OF parts] conjunct1[OF parts]
      conjunct2[OF parts] genv henv target_agree])
qed

theorem pbbk_book_denote_conversion:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and bl: "book_in_language book_minimal_logical_type UNIV signature G B \<tau>"
    and raw: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and typed: "book_env_typed domain G g"
  shows "pbbk_book_denote G g A = pbbk_book_denote G g B"
proof -
  obtain N where prefixes: "\<forall>m\<ge>N. pbeta_eta_equiv_in_signature signature (source_prefix G m) \<tau>
    (book_named_to_pterm G A) (book_named_to_pterm G B)"
    using book_named_translation_conversion_eventual[OF rich raw al bl] by (elim exE)
  have conversion: "pbeta_eta_equiv_in_signature signature (source_prefix G N) \<tau>
    (book_named_to_pterm G A) (book_named_to_pterm G B)"
    by (rule mp[OF spec[where x=N, OF prefixes] order_refl])
  have asig: "pterm_in_signature signature (book_named_to_pterm G A)"
    by (rule book_named_translation_in_signature[OF al])
  have bsig: "pterm_in_signature signature (book_named_to_pterm G B)"
    by (rule book_named_translation_in_signature[OF bl])
  have env: "pbbk_env_typed domain (source_prefix G N) g" by (rule book_env_pbbk_prefix[OF typed])
  show ?thesis unfolding pbbk_book_denote_def by (rule denote_beta_eta[OF conversion asig bsig env])
qed

theorem pbbk_book_separated_environment:
  assumes rich: "sg_rich G"
  shows "book_environment_separated domain pbbk_book_app book_minimal_logical_type UNIV
    signature G UNIV (pbbk_book_denote G)"
  apply unfold_locales
       apply (rule pbbk_book_app_type; assumption)
      apply (rule pbbk_book_denote_type; assumption)
     apply (rule pbbk_book_denote_var; assumption)
    apply (rule pbbk_book_denote_app; assumption)
   apply (rule pbbk_book_denote_locality; assumption)
  apply (rule pbbk_book_denote_conversion[OF rich]; assumption)
  done

theorem pbbk_book_full_environment:
  assumes rich: "sg_rich G"
  shows "book_full_environment domain pbbk_book_app book_minimal_logical_type UNIV
    signature G (pbbk_book_denote G)"
proof -
  have separated: "book_environment_separated domain pbbk_book_app book_minimal_logical_type UNIV
    signature G UNIV (pbbk_book_denote G)"
    by (rule pbbk_book_separated_environment[OF rich])
  interpret Book: book_environment_conditions domain pbbk_book_app book_minimal_logical_type UNIV
    signature G UNIV "pbbk_book_denote G"
    by (rule iffD2[OF book_environment_conditions_iff_separated separated])
  show ?thesis by unfold_locales
qed

end

end
