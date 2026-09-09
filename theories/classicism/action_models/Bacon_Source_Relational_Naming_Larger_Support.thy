theory Bacon_Source_Relational_Naming_Larger_Support
  imports Bacon_Source_Relational_Naming_Chart_Independence
begin

section \<open>A common larger chart preserves each term's value\<close>

text \<open>
  Several terms can be evaluated using one chart on the union of their
  supports. Extra markers do not occur freely in a replaced term, and
  none is an original variable name of that term. Extra payloads must
  still be typed to make the larger overriding assignment typed.
  No additional interpretation or model condition is introduced.
\<close>

lemma paper_R_naming_larger_override_agrees:
  assumes chart: "paper_R_naming_chart G L N x"
    and support: "paper_R_naming_support A \<subseteq> L" and avoid: "named_vars A \<subseteq> N"
    and free: "n \<in> named_fv (paper_R_naming_replace x A)"
  shows "paper_R_naming_override L x g n = paper_R_naming_override (paper_R_naming_support A) x g n"
proof -
  let ?K = "paper_R_naming_support A"
  have restricted: "paper_R_naming_chart G ?K (named_vars A) x"
    by (rule paper_R_naming_chart_restrict[OF chart support avoid])
  have large_inj: "inj_on x L" by (rule paper_R_naming_chart_injective[OF chart])
  have small_inj: "inj_on x ?K" by (rule paper_R_naming_chart_injective[OF restricted])
  have alternatives: "n \<in> named_fv A \<or> n \<in> x ` ?K"
    using paper_R_naming_replace_fv_bound[where x=x and A=A] free by blast
  show ?thesis
  proof (cases "n \<in> named_fv A")
    case True
    have large: "paper_R_naming_override L x g n = g n"
      by (rule paper_R_naming_override_agrees[OF chart avoid True])
    have small: "paper_R_naming_override ?K x g n = g n"
      by (rule paper_R_naming_override_agrees[OF restricted subset_refl True])
    show ?thesis by (simp only: large small)
  next
    case False
    obtain k where key: "k \<in> ?K" and shape: "n = x k" using alternatives False by blast
    have large_key: "k \<in> L" by (rule subsetD[OF support key])
    have large: "paper_R_naming_override L x g (x k) = Some (snd k)"
      by (rule paper_R_naming_override_lookup[OF large_inj large_key])
    have small: "paper_R_naming_override ?K x g (x k) = Some (snd k)"
      by (rule paper_R_naming_override_lookup[OF small_inj key])
    show ?thesis by (simp only: shape large small)
  qed
qed

context paper_R_bbk_model
begin

theorem paper_R_naming_larger_support_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and chart: "paper_R_naming_chart stock L N x"
    and support: "paper_R_naming_support A \<subseteq> L" and avoid: "named_vars A \<subseteq> N"
    and payloads: "\<forall>k\<in>L. snd k \<in> domain (fst k)"
  shows "denote (paper_R_naming_override L x g) (paper_R_naming_replace x A) =
    paper_R_naming_chart_denote x g A"
proof -
  let ?K = "paper_R_naming_support A"
  let ?B = "paper_R_naming_replace x A"
  have restricted: "paper_R_naming_chart stock ?K (named_vars A) x"
    by (rule paper_R_naming_chart_restrict[OF chart support avoid])
  have old_language: "paper_R_in_language signature stock ?B \<tau>"
    by (rule paper_R_naming_replace_language[OF language chart support])
  have large_type: "named_env_typed domain stock (paper_R_naming_override L x g)"
    by (rule paper_R_naming_override_typed[OF typed chart payloads])
  have small_type: "named_env_typed domain stock (paper_R_naming_override ?K x g)"
    by (rule paper_R_naming_term_override_typed[OF language restricted typed])
  have large_adequate: "named_adequate (paper_R_naming_override L x g) ?B"
    by (rule paper_R_naming_override_adequate[OF adequate support])
  have small_adequate: "named_adequate (paper_R_naming_override ?K x g) ?B"
    by (rule paper_R_naming_override_adequate[OF adequate subset_refl])
  show ?thesis unfolding paper_R_naming_chart_denote_def
  proof (rule denote_locality[OF old_language large_type small_type large_adequate small_adequate])
    fix n
    assume free: "n \<in> named_fv ?B"
    show "paper_R_naming_override L x g n = paper_R_naming_override ?K x g n"
      by (rule paper_R_naming_larger_override_agrees[OF chart support avoid free])
  qed
qed

corollary paper_R_naming_common_chart_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
    and common: "paper_R_naming_chart stock L N x"
    and support: "paper_R_naming_support A \<subseteq> L" and avoid: "named_vars A \<subseteq> N"
    and payloads: "\<forall>k\<in>L. snd k \<in> domain (fst k)"
    and individual: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) y"
  shows "denote (paper_R_naming_override L x g) (paper_R_naming_replace x A) =
    paper_R_naming_chart_denote y g A"
proof -
  have restricted: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    by (rule paper_R_naming_chart_restrict[OF common support avoid])
  have large: "denote (paper_R_naming_override L x g) (paper_R_naming_replace x A) =
      paper_R_naming_chart_denote x g A"
    by (rule paper_R_naming_larger_support_denote[OF language typed adequate common support avoid payloads])
  have same: "paper_R_naming_chart_denote x g A = paper_R_naming_chart_denote y g A"
    by (rule paper_R_naming_chart_denote_independent[OF language typed adequate restricted individual])
  show ?thesis by (rule trans[OF large same])
qed

section \<open>Locality in the original free variables\<close>

theorem paper_R_naming_chart_denote_locality:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and chart: "paper_R_naming_chart stock (paper_R_naming_support A) (named_vars A) x"
    and first: "named_env_typed domain stock g" and second: "named_env_typed domain stock h"
    and first_adequate: "named_adequate g A" and second_adequate: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "paper_R_naming_chart_denote x g A = paper_R_naming_chart_denote x h A"
proof -
  let ?K = "paper_R_naming_support A"
  let ?B = "paper_R_naming_replace x A"
  have old_language: "paper_R_in_language signature stock ?B \<tau>"
    by (rule paper_R_naming_replace_language[OF language chart subset_refl])
  have gt: "named_env_typed domain stock (paper_R_naming_override ?K x g)"
    by (rule paper_R_naming_term_override_typed[OF language chart first])
  have ht: "named_env_typed domain stock (paper_R_naming_override ?K x h)"
    by (rule paper_R_naming_term_override_typed[OF language chart second])
  have ga: "named_adequate (paper_R_naming_override ?K x g) ?B"
    by (rule paper_R_naming_override_adequate[OF first_adequate subset_refl])
  have ha: "named_adequate (paper_R_naming_override ?K x h) ?B"
    by (rule paper_R_naming_override_adequate[OF second_adequate subset_refl])
  show ?thesis unfolding paper_R_naming_chart_denote_def
  proof (rule denote_locality[OF old_language gt ht ga ha])
    fix n
    assume free: "n \<in> named_fv ?B"
    show "paper_R_naming_override ?K x g n = paper_R_naming_override ?K x h n"
    proof (cases "n \<in> x ` ?K")
      case True
      show ?thesis by (simp only: paper_R_naming_override_def True if_True)
    next
      case False
      have original: "n \<in> named_fv A"
        using paper_R_naming_replace_fv_bound[where x=x and A=A] free False by blast
      show ?thesis by (simp only: paper_R_naming_override_outside[OF False] agree[OF original])
    qed
  qed
qed

end

end
