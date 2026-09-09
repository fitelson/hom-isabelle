theory Bacon_Book_Full_Individual_Functions
  imports Bacon_Book_Function_Representation_Transport Bacon_Book_Full_Term_Application_Map
begin

context book_full_C_canonical_frame
begin

abbreviation individual_terms where
  "individual_terms w \<equiv> book_C_identity_domain (fst w) G (snd w) Ind"
abbreviation individual_counterpart where
  "individual_counterpart w v X \<equiv> book_C_term_counterpart G w v Ind X"
abbreviation individual_functions where
  "individual_functions w \<equiv> book_C_identity_domain (fst w) G (snd w) (Arr Ind Ind)"
abbreviation individual_function_counterpart where
  "individual_function_counterpart w v X \<equiv> book_C_term_counterpart G w v (Arr Ind Ind) X"
abbreviation individual_function_app where
  "individual_function_app w X Y \<equiv> book_C_term_app (fst w) G (snd w) Ind Ind X Y"

theorem full_individual_bijection:
  "book_modalized_bijection worlds le individual_terms individual_counterpart
    individual_terms individual_counterpart (\<lambda>w a. a)"
proof -
  interpret I: book_modalized_set worlds le individual_terms individual_counterpart by (rule full_term_modalized_set)
  show ?thesis
  proof unfold_locales
    show "book_modalized_map worlds le individual_terms individual_counterpart individual_terms individual_counterpart (\<lambda>w a. a)"
      by (rule book_modalized_map_identity)
    show "\<And>w. w \<in> worlds \<Longrightarrow> bij_betw (\<lambda>a. a) (individual_terms w) (individual_terms w)"
      by (simp add: bij_betw_def)
  qed
qed

sublocale EE: book_function_representation worlds le
  individual_terms individual_counterpart individual_terms individual_counterpart "\<lambda>w a. a"
  individual_terms individual_counterpart individual_terms individual_counterpart "\<lambda>w a. a"
  individual_functions individual_function_counterpart individual_function_app
proof -
  interpret I: book_modalized_bijection worlds le individual_terms individual_counterpart
    individual_terms individual_counterpart "\<lambda>w a. a" by (rule full_individual_bijection)
  interpret F: book_modalized_set worlds le individual_functions individual_function_counterpart by (rule full_term_modalized_set)
  show "book_function_representation worlds le
    individual_terms individual_counterpart individual_terms individual_counterpart (\<lambda>w a. a)
    individual_terms individual_counterpart individual_terms individual_counterpart (\<lambda>w a. a)
    individual_functions individual_function_counterpart individual_function_app"
  proof unfold_locales
    fix w f a
    assume ww: "w \<in> worlds" and fm: "f \<in> individual_functions w" and am: "a \<in> individual_terms w"
    interpret T: book_C_identity_world "fst w" G "snd w"
      by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
    show "individual_function_app w f a \<in> individual_terms w" by (rule T.term_app_typed[OF fm am])
  next
    fix w v f a
    assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
      and fm: "f \<in> individual_functions w" and am: "a \<in> individual_terms w"
    show "individual_counterpart w v (individual_function_app w f a) =
      individual_function_app v (individual_function_counterpart w v f) (individual_counterpart w v a)"
      by (rule book_C_term_application_naturality[OF rich full_rooted_base_world[OF ww] full_rooted_base_world[OF vw] access fm am])
  qed
qed

theorem full_individual_function_bijection:
  "book_modalized_bijection worlds le individual_functions individual_function_counterpart EE.function_domain
    (\<lambda>w v g. book_modalized_exponential_transport worlds le individual_terms v g) EE.function_h"
proof (rule EE.function_representation_bijection)
  fix w f g
  assume ww: "w \<in> worlds" and fm: "f \<in> individual_functions w" and gm: "g \<in> individual_functions w"
    and agrees: "\<And>v a. v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow> a \<in> individual_terms v \<Longrightarrow>
      individual_function_app v (individual_function_counterpart w v f) a =
      individual_function_app v (individual_function_counterpart w v g) a"
  show "f = g" by (rule full_term_quasi_functional[OF ww fm gm agrees])
qed

theorem full_individual_function_jh:
  assumes ww: "w \<in> worlds" and fm: "f \<in> individual_functions w"
  shows "EE.function_j w (EE.function_h w f) = f"
  by (rule EE.function_jh[OF ww fm]; rule full_term_quasi_functional[OF ww]; assumption)

theorem full_individual_function_hj:
  "g \<in> EE.function_domain w \<Longrightarrow> EE.function_h w (EE.function_j w g) = g"
  by (rule EE.function_hj; assumption)

theorem full_individual_function_homomorphism:
  "w \<in> worlds \<Longrightarrow> f \<in> individual_functions w \<Longrightarrow>
    EE.function_h w f \<in> book_modalized_exponential worlds le individual_terms individual_counterpart
      individual_terms individual_counterpart w"
  by (rule EE.function_h_homomorphism; assumption)

end

text \<open>
  Dᵉ=Tᵉ and hᵉ is the identity, as on p.400. The generic step is
  instantiated at e→e using the actual full-C term domains, application,
  counterparts and the proved all-type quasi-functionality theorem.
  The result is a domain of genuine future homomorphisms with inverse
  maps, not an assumed function representation or a PER domain.
  This concrete non-relational type does not yet establish the recursive
  representation at all types or the complete modal-model certificate.
\<close>

end
