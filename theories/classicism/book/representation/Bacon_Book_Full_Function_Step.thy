theory Bacon_Book_Full_Function_Step
  imports Bacon_Book_Function_Representation_Transport Bacon_Book_Full_Term_Application_Map
begin

section \<open>The canonical function step at arbitrary full types\<close>

locale book_full_function_step = Frame: book_full_C_canonical_frame \<Sigma> B G actual
  for \<Sigma> :: "('c::countable) ssignature" and B :: "'c ssignature" and G :: sgcontext and actual :: "'c book_C_world" +
  fixes \<sigma> \<tau> :: otype
    and DA :: "'c book_C_world \<Rightarrow> 'a set"
    and dA :: "'c book_C_world \<Rightarrow> 'c book_C_world \<Rightarrow> 'a \<Rightarrow> 'a"
    and hA :: "'c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> 'a"
    and DB :: "'c book_C_world \<Rightarrow> 'b set"
    and dB :: "'c book_C_world \<Rightarrow> 'c book_C_world \<Rightarrow> 'b \<Rightarrow> 'b"
    and hB :: "'c book_C_world \<Rightarrow> 'c book_named_term set \<Rightarrow> 'b"
  assumes argument_bijection: "book_modalized_bijection (book_full_C_rooted_worlds \<Sigma> B G actual) (book_C_canonical_le G)
      (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<sigma>) (\<lambda>w v X. book_C_term_counterpart G w v \<sigma> X) DA dA hA"
    and result_bijection: "book_modalized_bijection (book_full_C_rooted_worlds \<Sigma> B G actual) (book_C_canonical_le G)
      (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<tau>) (\<lambda>w v X. book_C_term_counterpart G w v \<tau> X) DB dB hB"
begin

abbreviation W where "W \<equiv> book_full_C_rooted_worlds \<Sigma> B G actual"
abbreviation le where "le \<equiv> book_C_canonical_le G"
abbreviation terms where "terms \<rho> w \<equiv> book_C_identity_domain (fst w) G (snd w) \<rho>"
abbreviation counterpart where "counterpart \<rho> w v X \<equiv> book_C_term_counterpart G w v \<rho> X"
abbreviation application where "application w X Y \<equiv> book_C_term_app (fst w) G (snd w) \<sigma> \<tau> X Y"

sublocale Step: book_function_representation W le
  "terms \<sigma>" "counterpart \<sigma>" DA dA hA "terms \<tau>" "counterpart \<tau>" DB dB hB
  "terms (Arr \<sigma> \<tau>)" "counterpart (Arr \<sigma> \<tau>)" application
proof -
  interpret A: book_modalized_bijection W le "terms \<sigma>" "counterpart \<sigma>" DA dA hA by (rule argument_bijection)
  interpret B: book_modalized_bijection W le "terms \<tau>" "counterpart \<tau>" DB dB hB by (rule result_bijection)
  interpret F: book_modalized_set W le "terms (Arr \<sigma> \<tau>)" "counterpart (Arr \<sigma> \<tau>)"
    by (rule Frame.full_term_modalized_set)
  show "book_function_representation W le
    (terms \<sigma>) (counterpart \<sigma>) DA dA hA (terms \<tau>) (counterpart \<tau>) DB dB hB
    (terms (Arr \<sigma> \<tau>)) (counterpart (Arr \<sigma> \<tau>)) application"
  proof unfold_locales
    fix w f a
    assume ww: "w \<in> W" and fm: "f \<in> terms (Arr \<sigma> \<tau>) w" and am: "a \<in> terms \<sigma> w"
    interpret T: book_C_identity_world "fst w" G "snd w"
      by (rule book_full_C_world_identity_algebra[OF Frame.rich Frame.book_full_C_rooted_world_data(1)[OF ww]])
    show "application w f a \<in> terms \<tau> w" by (rule T.term_app_typed[OF fm am])
  next
    fix w v f a
    assume ww: "w \<in> W" and vw: "v \<in> W" and access: "le w v"
      and fm: "f \<in> terms (Arr \<sigma> \<tau>) w" and am: "a \<in> terms \<sigma> w"
    show "counterpart \<tau> w v (application w f a) = application v (counterpart (Arr \<sigma> \<tau>) w v f) (counterpart \<sigma> w v a)"
      by (rule book_C_term_application_naturality[OF Frame.rich Frame.full_rooted_base_world[OF ww]
        Frame.full_rooted_base_world[OF vw] access fm am])
  qed
qed

theorem canonical_function_bijection:
  "book_modalized_bijection W le (terms (Arr \<sigma> \<tau>)) (counterpart (Arr \<sigma> \<tau>)) Step.function_domain
    (\<lambda>w v g. book_modalized_exponential_transport W le DA v g) Step.function_h"
proof (rule Step.function_representation_bijection)
  fix w f g
  assume ww: "w \<in> W" and fm: "f \<in> terms (Arr \<sigma> \<tau>) w" and gm: "g \<in> terms (Arr \<sigma> \<tau>) w"
    and agrees: "\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> terms \<sigma> v \<Longrightarrow>
      application v (counterpart (Arr \<sigma> \<tau>) w v f) a = application v (counterpart (Arr \<sigma> \<tau>) w v g) a"
  show "f = g" by (rule Frame.full_term_quasi_functional[OF ww fm gm agrees])
qed

theorem canonical_function_homomorphism:
  "w \<in> W \<Longrightarrow> f \<in> terms (Arr \<sigma> \<tau>) w \<Longrightarrow>
    Step.function_h w f \<in> book_modalized_exponential W le DA dA DB dB w"
  by (rule Step.function_h_homomorphism; assumption)

end

text \<open>
  At arbitrary object-language types σ,τ, the canonical construction
  supplies all source premises of the generic function step, including
  quasi-functionality. Only the already constructed lower-type modalized
  bijections remain as induction hypotheses. The resulting function
  domain and h are actual constructions. This uniform step is not yet
  an all-type recursion on one explicitly represented set universe.
\<close>

end
