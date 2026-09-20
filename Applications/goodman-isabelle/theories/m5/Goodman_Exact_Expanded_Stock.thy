theory Goodman_Exact_Expanded_Stock
  imports
    "Goodman_Integration_Logical_Stock.Goodman_Exact_Stock_Correspondence"
    "Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Translation"
    "Goodman_Exact_Stock_Action.Bacon_PP_ZF_Exact_Logical_Stock_Action"
begin

section \<open>All closed terms over one additional pure unary value\<close>

definition gi_M5_expanded_signature :: "string \<Rightarrow> string ssignature" where
  "gi_M5_expanded_signature k \<tau> = (if \<tau> = gb_unary then {k} else {})"

definition gi_M5_basis_constants :: "string \<Rightarrow> ZF \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF" where
  "gi_M5_basis_constants k K c \<tau> =
    (if c = k \<and> \<tau> = gb_unary then K else pp_e_default \<tau>)"

definition gi_M5_expanded_closed_den :: "string \<Rightarrow> ZF \<Rightarrow> oterm \<Rightarrow> ZF" where
  "gi_M5_expanded_closed_den k K M = pp_e_eval (gi_M5_basis_constants k K) pp_e_closed_env M"

definition gi_M5_expanded_basis :: "string \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow> ZF set" where
  "gi_M5_expanded_basis k K \<sigma> =
    {x. \<exists>M. [] \<turnstile> M : \<sigma> \<and>
      oterm_in_string_signature (gi_M5_expanded_signature k) M \<and>
      x = gi_M5_expanded_closed_den k K M}"

definition gi_M5_named_expanded_basis ::
  "string \<Rightarrow> ZF \<Rightarrow> sgcontext \<Rightarrow> otype \<Rightarrow> ZF set" where
  "gi_M5_named_expanded_basis k K G \<sigma> =
    {x. \<exists>A. book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma> \<and>
      named_fv A = {} \<and>
      x = gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A}"

text \<open>
  The auxiliary signature admits k only at t→t. The generating family
  includes every closed well-typed term over that signature, including
  arbitrary abstractions and higher-order quantifiers; it is not merely
  an applicative-expression grammar. The carriers remain pp_b_domain.

  C_K is an auxiliary interpreter used to specify this generating family.
  It is NOT the eventual Goodman interpretation of Pure or Fun. A later
  model may classify the local-identity saturation of this basis as pure
  and choose a new fundamental proposition. Those operations are not
  performed or presumed correct in this theory.
\<close>

lemma gi_M5_signature_occurrence_iff:
  "oterm_in_string_signature (gi_M5_expanded_signature k) (Const c \<tau>) \<longleftrightarrow>
    c = k \<and> \<tau> = gb_unary"
  by (auto simp: gi_M5_expanded_signature_def)

lemma gi_M5_signature_translation_guard:
  "gi_constants_admitted (\<lambda>c \<tau>. c) \<Sigma> M = oterm_in_string_signature \<Sigma> M"
  by (induction M) simp_all

lemma gi_M5_logical_in_expanded_signature:
  assumes logical: "pp_logical_vocabulary M"
  shows "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  using logical unfolding pp_logical_vocabulary_def
  by (induction M) auto

lemma gi_M5_expanded_basisI:
  assumes typed: "[] \<turnstile> M : \<sigma>"
    and admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
  shows "gi_M5_expanded_closed_den k K M \<in> gi_M5_expanded_basis k K \<sigma>"
  unfolding gi_M5_expanded_basis_def using typed admitted by blast

lemma gi_M5_expanded_basisE:
  assumes member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  obtains M where "[] \<turnstile> M : \<sigma>"
    "oterm_in_string_signature (gi_M5_expanded_signature k) M"
    "x = gi_M5_expanded_closed_den k K M"
  using member unfolding gi_M5_expanded_basis_def by blast

theorem gi_M5_expanded_basis_countable:
  "countable (gi_M5_expanded_basis k K \<sigma>)"
proof -
  let ?T = "{M. [] \<turnstile> M : \<sigma> \<and> oterm_in_string_signature (gi_M5_expanded_signature k) M}"
  have terms: "countable ?T" by simp
  have image: "gi_M5_expanded_basis k K \<sigma> = gi_M5_expanded_closed_den k K ` ?T"
    unfolding gi_M5_expanded_basis_def by auto
  show ?thesis unfolding image by (rule countable_image[OF terms])
qed

locale gi_exact_expanded_stock =
  fixes k :: string and K :: ZF
  assumes fresh_pure: "k \<noteq> pp_pure_name"
    and fresh_fun: "k \<noteq> pp_fun_name"
    and K_typed: "Elem K (pp_e_domain gb_unary)"
    and K_invariant: "\<And>i. pp_b_action gb_unary i K = K"
begin

lemma gi_M5_basis_constants_typed:
  "Elem (gi_M5_basis_constants k K c \<tau>) (pp_e_domain \<tau>)"
  using K_typed by (auto simp: gi_M5_basis_constants_def intro: pp_e_default_in_domain)

lemma gi_M5_basis_constants_action:
  "pp_b_action \<tau> i (gi_M5_basis_constants k K c \<tau>) = gi_M5_basis_constants k K c \<tau>"
  using K_invariant pp_b_structure_action_default[OF pp_b_mset_structure_all]
  by (auto simp: gi_M5_basis_constants_def)

sublocale Basis: pp_e_equivariant_constants "gi_M5_basis_constants k K"
proof
  show "Elem (gi_M5_basis_constants k K c \<sigma>) (pp_e_domain \<sigma>)" for c \<sigma>
    by (rule gi_M5_basis_constants_typed)
next
  show "pp_b_action \<sigma> i (gi_M5_basis_constants k K c \<sigma>) = gi_M5_basis_constants k K c \<sigma>" for \<sigma> i c
    by (rule gi_M5_basis_constants_action)
qed

lemma gi_M5_basis_named_constant_value:
  "gi_M5_basis_constants k K k gb_unary = K"
  by (simp only: gi_M5_basis_constants_def; simp)

lemma gi_M5_basis_reserved_names_default:
  "gi_M5_basis_constants k K pp_pure_name \<tau> = pp_e_default \<tau> \<and>
    gi_M5_basis_constants k K pp_fun_name \<tau> = pp_e_default \<tau>"
  using fresh_pure fresh_fun by (auto simp: gi_M5_basis_constants_def)

theorem gi_M5_basis_eval_action:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and source: "pp_e_env_typed \<Gamma> \<rho>"
    and related: "pp_e_env_action \<Gamma> i \<rho> \<eta>"
  shows "pp_b_action \<tau> i (pp_e_eval (gi_M5_basis_constants k K) \<rho> M) =
    pp_e_eval (gi_M5_basis_constants k K) \<eta> M"
  by (rule Basis.pp_e_eval_action[OF typed source related])

lemma gi_M5_expanded_closed_den_typed:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "Elem (gi_M5_expanded_closed_den k K M) (pp_e_domain \<sigma>)"
  using Basis.pp_e_eval_type[OF typed pp_e_empty_env_typed]
  by (simp only: gi_M5_expanded_closed_den_def pp_e_dom_def)

lemma gi_M5_expanded_closed_den_invariant:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "pp_b_action \<sigma> i (gi_M5_expanded_closed_den k K M) = gi_M5_expanded_closed_den k K M"
  unfolding gi_M5_expanded_closed_den_def
  by (rule gi_M5_basis_eval_action[OF typed pp_e_empty_env_typed pp_e_closed_env_action])

lemma gi_M5_expanded_closed_eval_independent:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "pp_e_eval (gi_M5_basis_constants k K) \<rho> M = gi_M5_expanded_closed_den k K M"
  unfolding gi_M5_expanded_closed_den_def
proof (rule Basis.gi_exact_eval_agrees_on_context[OF typed pp_e_empty_env_typed pp_e_empty_env_typed])
  fix n \<tau>
  assume impossible: "lookup [] n = Some \<tau>"
  then show "\<rho> n = pp_e_closed_env n" by (simp add: lookup_def)
qed

theorem gi_M5_expanded_basis_typed:
  assumes member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  shows "Elem x (pp_e_domain \<sigma>)"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>" and shape: "x = gi_M5_expanded_closed_den k K M"
    using member by (blast elim: gi_M5_expanded_basisE)
  show ?thesis unfolding shape by (rule gi_M5_expanded_closed_den_typed[OF typed])
qed

theorem gi_M5_expanded_basis_invariant:
  assumes member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  shows "pp_b_action \<sigma> i x = x"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>" and shape: "x = gi_M5_expanded_closed_den k K M"
    using member by (blast elim: gi_M5_expanded_basisE)
  show ?thesis unfolding shape by (rule gi_M5_expanded_closed_den_invariant[OF typed])
qed

theorem gi_M5_expanded_basis_application:
  assumes fs: "F \<in> gi_M5_expanded_basis k K (Arr \<sigma> \<tau>)"
    and xs: "x \<in> gi_M5_expanded_basis k K \<sigma>"
  shows "F \<acute> x \<in> gi_M5_expanded_basis k K \<tau>"
proof -
  obtain M where mt: "[] \<turnstile> M : Arr \<sigma> \<tau>"
    and ms: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
    and fm: "F = gi_M5_expanded_closed_den k K M"
    using fs by (rule gi_M5_expanded_basisE)
  obtain N where nt: "[] \<turnstile> N : \<sigma>"
    and ns: "oterm_in_string_signature (gi_M5_expanded_signature k) N"
    and xn: "x = gi_M5_expanded_closed_den k K N"
    using xs by (rule gi_M5_expanded_basisE)
  have app_type: "[] \<turnstile> App M N : \<tau>" by (rule has_type.App[OF mt nt])
  have app_signature: "oterm_in_string_signature (gi_M5_expanded_signature k) (App M N)"
    using ms ns by simp
  have member: "gi_M5_expanded_closed_den k K (App M N) \<in> gi_M5_expanded_basis k K \<tau>"
    by (rule gi_M5_expanded_basisI[OF app_type app_signature])
  show ?thesis using member by (simp only: gi_M5_expanded_closed_den_def pp_e_eval.simps fm xn)
qed

theorem gi_M5_expanded_basis_contains_logical:
  assumes typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
  shows "pp_e_closed_den M \<in> gi_M5_expanded_basis k K \<sigma>"
proof -
  have admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
    by (rule gi_M5_logical_in_expanded_signature[OF logical])
  have member: "gi_M5_expanded_closed_den k K M \<in> gi_M5_expanded_basis k K \<sigma>"
    by (rule gi_M5_expanded_basisI[OF typed admitted])
  have no_constants: "consts_of M = {}" using logical unfolding pp_logical_vocabulary_def .
  have same_value: "gi_M5_expanded_closed_den k K M = pp_e_closed_den M"
    unfolding gi_M5_expanded_closed_den_def pp_e_closed_den_def
    by (rule pp_e_eval_const_free[OF no_constants])
  show ?thesis using member by (simp only: same_value)
qed

theorem gi_M5_expanded_basis_contains_K:
  "K \<in> gi_M5_expanded_basis k K gb_unary"
proof -
  have typed: "[] \<turnstile> Const k gb_unary : gb_unary" by (rule has_type.Const)
  have admitted: "oterm_in_string_signature (gi_M5_expanded_signature k) (Const k gb_unary)"
    by (simp add: gi_M5_expanded_signature_def)
  have member: "gi_M5_expanded_closed_den k K (Const k gb_unary) \<in> gi_M5_expanded_basis k K gb_unary"
    by (rule gi_M5_expanded_basisI[OF typed admitted])
  show ?thesis using member
    by (simp only: gi_M5_expanded_closed_den_def pp_e_eval.simps gi_M5_basis_named_constant_value)
qed

section \<open>The complete closed named language gives exactly the same family\<close>

theorem gi_M5_named_expanded_basis_equal:
  assumes rich: "sg_rich G"
  shows "gi_M5_named_expanded_basis k K G \<sigma> = gi_M5_expanded_basis k K \<sigma>"
proof (rule set_eqI)
  fix x
  show "x \<in> gi_M5_named_expanded_basis k K G \<sigma> \<longleftrightarrow> x \<in> gi_M5_expanded_basis k K \<sigma>"
  proof
    assume member: "x \<in> gi_M5_named_expanded_basis k K G \<sigma>"
    obtain A where language: "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G A \<sigma>"
      and closed_term: "named_fv A = {}"
      and shape: "x = gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A"
      using member unfolding gi_M5_named_expanded_basis_def by blast
    have decoded_type: "[] \<turnstile> gi_exact_decode G A : \<sigma>"
      by (rule gi_closed_named_decode_type[OF language closed_term])
    have decoded_signature: "oterm_in_string_signature (gi_M5_expanded_signature k) (gi_exact_decode G A)"
      using book_named_translation_in_signature[OF language]
      by (simp only: gi_exact_decode_def pterm_string_signature_iff)
    have independent:
        "gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) A =
          gi_exact_named_denote (gi_M5_basis_constants k K) G pp_e_closed_env A"
      by (rule gi_exact_named_closed_assignment_independent[OF closed_term])
    have value_eq: "x = gi_M5_expanded_closed_den k K (gi_exact_decode G A)"
      using trans[OF shape independent]
      by (simp only: gi_exact_named_denote_def gi_exact_decode_def gi_M5_expanded_closed_den_def)
    show "x \<in> gi_M5_expanded_basis k K \<sigma>"
      by (simp only: value_eq; rule gi_M5_expanded_basisI[OF decoded_type decoded_signature])
  next
    assume member: "x \<in> gi_M5_expanded_basis k K \<sigma>"
    obtain M where typed: "[] \<turnstile> M : \<sigma>"
      and signature: "oterm_in_string_signature (gi_M5_expanded_signature k) M"
      and shape: "x = gi_M5_expanded_closed_den k K M"
      using member by (rule gi_M5_expanded_basisE)
    let ?A = "gi_to_book G [] (\<lambda>c \<tau>. c) M"
    have admitted: "gi_constants_admitted (\<lambda>c \<tau>. c) (gi_M5_expanded_signature k) M"
      by (simp only: gi_M5_signature_translation_guard; rule signature)
    have language: "book_in_language book_minimal_logical_type UNIV (gi_M5_expanded_signature k) G ?A \<sigma>"
      by (rule gi_to_book_language[OF rich typed _ admitted]; simp)
    have closed_term: "named_fv ?A = {}" by (rule gi_closed_translation[OF rich typed])
    have translated:
        "gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) ?A =
          pp_e_eval (gi_M5_basis_constants k K) (\<lambda>i. gi_exact_default_assignment G ([] ! i)) M"
      by (rule Basis.gi_exact_denotation_translation[OF rich typed _ _ gi_exact_default_assignment_typed]; simp)
    have value_eq: "x = gi_exact_named_denote (gi_M5_basis_constants k K) G (gi_exact_default_assignment G) ?A"
      by (simp only: shape translated gi_M5_expanded_closed_eval_independent[OF typed])
    show "x \<in> gi_M5_named_expanded_basis k K G \<sigma>"
      unfolding gi_M5_named_expanded_basis_def
      by (rule CollectI, rule exI[where x="?A"], rule conjI[OF language conjI[OF closed_term value_eq]])
  qed
qed

theorem gi_M5_expanded_basis_contains_native_logical:
  assumes logical: "gb_closed_logical G \<sigma> A"
  shows "gi_exact_native_closed_den G A \<in> gi_M5_expanded_basis k K \<sigma>"
  by (simp only: gi_exact_native_closed_den_decoded[OF logical];
    rule gi_M5_expanded_basis_contains_logical[
      OF gi_goodman_closed_logical_decode_denotation(1,2)[OF logical]])

end

text \<open>
  The complete expanded language has been covered in both directions:
  every named closed term decodes to an admitted old term with the same
  exact value, and every admitted old term has a closed named translation.
  No claim about all pure values follows merely from countability of this
  generating family; local-identity saturation and the rebuilt Goodman
  interpretation remain separate. In particular, C_K is not used here
  as a purported interpretation satisfying the Pure/Fun axioms.
\<close>

end
