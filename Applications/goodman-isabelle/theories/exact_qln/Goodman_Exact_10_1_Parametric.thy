theory Goodman_Exact_10_1_Parametric
  imports Goodman_Exact_10_1_Transfer
begin

section \<open>Theorem 10.1 for an arbitrary type of constant names\<close>

text \<open>
  The checked named Theorem 10.1 (Goodman_Exact_10_1_Transfer) takes string
  constant names. Bacon's branch gluing itself is pointwise in the constant
  and its type, hence alphabet-independent; the only string-specific step is
  the exact evaluator, which decodes string named terms to the constructor
  syntax whose constants are strings.

  This theory makes the theorem parametric in the name type 'c without
  re-proving the 336-line action induction and without injecting the whole
  signature into strings. A closed term mentions finitely many constants;
  those are coded injectively into strings, term by term, the string theorem
  is applied to the renamed term with the correspondingly renamed family,
  and the result is transported back. The t-generated fragment and the
  countable branch family (indexed by n :: nat) are retained unchanged.
  Nothing here asserts that the signature is countable.
\<close>

subsection \<open>Named constants, the polymorphic fragment, and constant renaming\<close>

fun gi_named_consts :: "('c, 'l) named_term \<Rightarrow> 'c set" where
  "gi_named_consts (NVar n) = {}"
| "gi_named_consts (NConst c \<sigma>) = {c}"
| "gi_named_consts (NLogical l) = {}"
| "gi_named_consts (NApp F A) = gi_named_consts F \<union> gi_named_consts A"
| "gi_named_consts (NLam n A) = gi_named_consts A"

lemma gi_named_consts_finite: "finite (gi_named_consts M)"
  by (induction M) simp_all

lemma gi_named_consts_map: "gi_named_consts (map_named_term f id M) = f ` gi_named_consts M"
  by (induction M) (simp_all add: image_Un)

lemma gi_named_fv_map: "named_fv (map_named_term f id M) = named_fv M"
  by (induction M) simp_all

fun gi_exact_poly_propositional_term ::
  "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "gi_exact_poly_propositional_term G (NVar n) = True"
| "gi_exact_poly_propositional_term G (NConst c \<sigma>) = pp_e_propositional_type \<sigma>"
| "gi_exact_poly_propositional_term G (NLogical l) =
    pp_e_propositional_type (book_minimal_logical_type l)"
| "gi_exact_poly_propositional_term G (NApp F A) =
    (gi_exact_poly_propositional_term G F \<and> gi_exact_poly_propositional_term G A)"
| "gi_exact_poly_propositional_term G (NLam n A) =
    (pp_e_propositional_type (G n) \<and> gi_exact_poly_propositional_term G A)"

lemma gi_exact_poly_propositional_string:
  "gi_exact_poly_propositional_term G M = gi_exact_named_propositional_term G M"
  by (induction M) simp_all

lemma gi_exact_poly_propositional_map:
  "gi_exact_poly_propositional_term G (map_named_term f id M) = gi_exact_poly_propositional_term G M"
  by (induction M) simp_all

lemma gi_exact_logical_translation_map:
  "map_pterm f (book_minimal_logical_translation l) = book_minimal_logical_translation l"
  by (cases l) simp_all

lemma gi_exact_named_to_pterm_map:
  "book_minimal_to_pterm (named_to_source G ns (map_named_term f id M)) =
    map_pterm f (book_minimal_to_pterm (named_to_source G ns M))"
  by (induction M arbitrary: ns) (simp_all add: gi_exact_logical_translation_map)

lemma gi_exact_decode_map:
  "gi_exact_decode G (map_named_term f id M) =
    pterm_to_oterm (map_pterm f (book_named_to_pterm G M))"
  by (simp only: gi_exact_decode_def book_named_to_pterm_def gi_exact_named_to_pterm_map)

lemma gi_has_ptype_map:
  assumes "has_ptype \<Gamma> P \<tau>"
  shows "has_ptype \<Gamma> (map_pterm f P) \<tau>"
  using assms by (induction rule: has_ptype.induct) (simp_all, blast+)

subsection \<open>Typing and fragment membership of the renamed decoding\<close>

lemma gi_exact_poly_pterm_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
  shows "has_ptype [] (book_named_to_pterm G M) \<tau>"
proof -
  have named: "has_ntype book_minimal_logical_type G M \<tau>"
    using book_language_named[OF language] unfolding named_in_language_def by blast
  have source: "has_stype book_minimal_logical_type [] (named_to_source G [] M) \<tau>"
    by (rule named_to_source_closed_type[OF named closed_term])
  show ?thesis unfolding book_named_to_pterm_def by (rule book_minimal_to_pterm_type[OF source])
qed

lemma gi_exact_renamed_decode_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
  shows "[] \<turnstile> gi_exact_decode G (map_named_term f id M) : \<tau>"
  unfolding gi_exact_decode_map
  by (rule pterm_to_preserves_typing[OF gi_has_ptype_map[OF gi_exact_poly_pterm_type[OF language closed_term]]])

lemma gi_exact_renamed_decode_fragment:
  assumes fragment: "gi_exact_poly_propositional_term G M"
  shows "pp_e_propositional_term (gi_exact_decode G (map_named_term f id M))"
  using fragment
  by (simp only: gi_exact_named_propositional_decode_iff gi_exact_poly_propositional_string[symmetric]
      gi_exact_poly_propositional_map)

subsection \<open>Constants of a decoded string term, and constant agreement of the evaluator\<close>

lemma gi_exact_logical_translation_consts:
  "consts_of (pterm_to_oterm (book_minimal_logical_translation l)) = {}"
  by (cases l) simp_all

lemma gi_exact_decode_consts_encoding:
  "consts_of (pterm_to_oterm (book_minimal_to_pterm (named_to_source G ns M))) \<subseteq> gi_named_consts M"
  by (induction M arbitrary: ns) (auto simp: gi_exact_logical_translation_consts)

lemma gi_exact_decode_consts:
  "consts_of (gi_exact_decode G M) \<subseteq> gi_named_consts M"
  by (simp only: gi_exact_decode_def book_named_to_pterm_def gi_exact_decode_consts_encoding)

lemma pp_e_eval_constant_agreement:
  assumes agree: "\<And>c \<sigma>. c \<in> consts_of N \<Longrightarrow> C c \<sigma> = C' c \<sigma>"
  shows "pp_e_eval C \<rho> N = pp_e_eval C' \<rho> N"
  using agree
proof (induction N arbitrary: \<rho>)
  case (Lam \<sigma> M)
  have body: "\<And>\<rho>. pp_e_eval C \<rho> M = pp_e_eval C' \<rho> M" by (rule Lam.IH) (simp add: Lam.prems)
  show ?case by (simp only: pp_e_eval.simps body)
next
  case (Forall \<sigma> M)
  have body: "\<And>\<rho>. pp_e_eval C \<rho> M = pp_e_eval C' \<rho> M" by (rule Forall.IH) (simp add: Forall.prems)
  show ?case by (simp only: pp_e_eval.simps body)
next
  case (Exists \<sigma> M)
  have body: "\<And>\<rho>. pp_e_eval C \<rho> M = pp_e_eval C' \<rho> M" by (rule Exists.IH) (simp add: Exists.prems)
  show ?case by (simp only: pp_e_eval.simps body)
qed simp_all

lemma gi_exact_named_denote_constant_agreement:
  assumes agree: "\<And>c \<sigma>. c \<in> gi_named_consts M \<Longrightarrow> C c \<sigma> = C' c \<sigma>"
  shows "gi_exact_named_denote C G g M = gi_exact_named_denote C' G g M"
  unfolding gi_exact_named_denote_def gi_exact_decode_def[symmetric]
  by (rule pp_e_eval_constant_agreement) (use agree gi_exact_decode_consts[of G M] in blast)

subsection \<open>An injective string code for the finitely many constants of a term\<close>

lemma gi_exact_finite_string_injection:
  assumes finite: "finite (K :: 'c set)"
  shows "\<exists>\<iota> :: 'c \<Rightarrow> string. inj_on \<iota> K"
proof -
  obtain f :: "'c \<Rightarrow> nat" and m where "f ` K = {i. i < m}" and inj: "inj_on f K"
    using finite_imp_inj_to_nat_seg[OF finite] by blast
  have "inj_on (\<lambda>c. replicate (f c) (CHR ''a'')) K"
    using inj unfolding inj_on_def by simp
  then show ?thesis by blast
qed

definition gi_exact_name_code :: "'c book_named_term \<Rightarrow> 'c \<Rightarrow> string" where
  "gi_exact_name_code M = (SOME \<iota>. inj_on \<iota> (gi_named_consts M))"

lemma gi_exact_name_code_inj: "inj_on (gi_exact_name_code M) (gi_named_consts M)"
  unfolding gi_exact_name_code_def
  by (rule someI_ex[OF gi_exact_finite_string_injection[OF gi_named_consts_finite]])

definition gi_exact_name_decode :: "'c book_named_term \<Rightarrow> string \<Rightarrow> 'c" where
  "gi_exact_name_decode M = inv_into (gi_named_consts M) (gi_exact_name_code M)"

lemma gi_exact_name_decode_code:
  "c \<in> gi_named_consts M \<Longrightarrow> gi_exact_name_decode M (gi_exact_name_code M c) = c"
  unfolding gi_exact_name_decode_def by (rule inv_into_f_f[OF gi_exact_name_code_inj])

subsection \<open>The polymorphic evaluator and its agreement with the string evaluator\<close>

definition gi_exact_poly_denote ::
  "('c \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> 'c book_named_term \<Rightarrow> ZF" where
  "gi_exact_poly_denote C G g M =
    gi_exact_named_denote (\<lambda>s \<sigma>. C (gi_exact_name_decode M s) \<sigma>) G g
      (map_named_term (gi_exact_name_code M) id M)"

lemma pp_e_eval_pterm_rename:
  "pp_e_eval C \<rho> (pterm_to_oterm (map_pterm f P)) =
    pp_e_eval (\<lambda>c \<sigma>. C (f c) \<sigma>) \<rho> (pterm_to_oterm P)"
  by (induction P arbitrary: \<rho>) simp_all

lemma gi_book_named_to_pterm_map:
  "book_named_to_pterm G (map_named_term f id M) = map_pterm f (book_named_to_pterm G M)"
  by (simp only: book_named_to_pterm_def gi_exact_named_to_pterm_map)

lemma gi_exact_named_denote_rename:
  "gi_exact_named_denote C G g (map_named_term f id M) =
    gi_exact_named_denote (\<lambda>c \<sigma>. C (f c) \<sigma>) G g M"
  unfolding gi_exact_named_denote_def gi_book_named_to_pterm_map
  by (rule pp_e_eval_pterm_rename)

theorem gi_exact_poly_denote_string:
  "gi_exact_poly_denote C G g M = gi_exact_named_denote C G g M"
proof -
  have renamed: "gi_exact_poly_denote C G g M =
      gi_exact_named_denote (\<lambda>c \<sigma>. C (gi_exact_name_decode M (gi_exact_name_code M c)) \<sigma>) G g M"
    unfolding gi_exact_poly_denote_def by (rule gi_exact_named_denote_rename)
  show ?thesis unfolding renamed
    by (rule gi_exact_named_denote_constant_agreement) (simp add: gi_exact_name_decode_code)
qed

lemma gi_exact_poly_denote_closed_assignment_independent:
  assumes closed_term: "named_fv M = {}"
  shows "gi_exact_poly_denote C G g M = gi_exact_poly_denote C G h M"
  unfolding gi_exact_poly_denote_def
  by (rule gi_exact_named_closed_assignment_independent) (simp add: gi_named_fv_map closed_term)

subsection \<open>The alphabet-independent branch gluing\<close>

definition gi_exact_poly_glued ::
  "(nat \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ZF" where
  "gi_exact_poly_glued A c \<sigma> =
    (if pp_e_propositional_type \<sigma> then pp_e_branch_glue \<sigma> (\<lambda>n. A n c \<sigma>) else pp_e_default \<sigma>)"

lemma gi_exact_poly_glued_as_string:
  "gi_exact_poly_glued A c \<sigma> = pp_e_Bacon_glued_constants (\<lambda>n s. A n c) s \<sigma>"
  by (simp add: gi_exact_poly_glued_def pp_e_Bacon_glued_constants_def)

lemma gi_exact_poly_glued_typed:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "Elem (gi_exact_poly_glued A c \<sigma>) (pp_e_domain \<sigma>)"
  unfolding gi_exact_poly_glued_as_string[where s="''''"]
  by (rule pp_e_Bacon_glued_constants_typed) (rule family; assumption)

lemma gi_exact_poly_glued_action:
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and prop_type: "pp_e_propositional_type \<sigma>"
  shows "pp_b_action \<sigma> [n] (gi_exact_poly_glued A c \<sigma>) = A n c \<sigma>"
  unfolding gi_exact_poly_glued_as_string[where s="''''"]
  by (rule pp_e_Bacon_glued_constants_action[OF _ prop_type]) (rule family; assumption)

lemma gi_exact_poly_glued_renamed:
  assumes member: "c \<in> gi_named_consts M"
  shows "pp_e_Bacon_glued_constants (\<lambda>n s \<sigma>. A n (gi_exact_name_decode M s) \<sigma>)
      (gi_exact_name_code M c) \<sigma> = gi_exact_poly_glued A c \<sigma>"
  by (simp add: pp_e_Bacon_glued_constants_def gi_exact_poly_glued_def gi_exact_name_decode_code[OF member])

subsection \<open>Theorem 10.1 for closed named terms over an arbitrary name type\<close>

theorem gi_exact_Bacon_10_1_parametric_action:
  fixes A :: "nat \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ZF"
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_poly_propositional_term G M"
  shows "pp_b_action \<tau> [n] (gi_exact_poly_denote (gi_exact_poly_glued A) G g M) =
    gi_exact_poly_denote (A n) G h M"
proof -
  let ?\<iota> = "gi_exact_name_code M"
  let ?M' = "map_named_term ?\<iota> id M"
  let ?A' = "\<lambda>n s \<sigma>. A n (gi_exact_name_decode M s) \<sigma>"
  have family': "\<And>n s \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (?A' n s \<sigma>) (pp_e_domain \<sigma>)"
    by (rule family)
  have typed: "[] \<turnstile> gi_exact_decode G ?M' : \<tau>"
    by (rule gi_exact_renamed_decode_type[OF language closed_term])
  have decoded_fragment: "pp_e_propositional_term (gi_exact_decode G ?M')"
    by (rule gi_exact_renamed_decode_fragment[OF fragment])
  have closed': "named_fv ?M' = {}" by (simp add: gi_named_fv_map closed_term)
  have string_action: "pp_b_action \<tau> [n]
      (pp_e_eval (pp_e_Bacon_glued_constants ?A') pp_e_closed_env (gi_exact_decode G ?M')) =
      pp_e_eval (?A' n) pp_e_closed_env (gi_exact_decode G ?M')"
    by (rule pp_e_Bacon_10_1_term_action[OF family' typed decoded_fragment])
  have glued_agree: "gi_exact_named_denote (\<lambda>s \<sigma>. gi_exact_poly_glued A (gi_exact_name_decode M s) \<sigma>) G g ?M' =
      gi_exact_named_denote (pp_e_Bacon_glued_constants ?A') G g ?M'"
  proof (rule gi_exact_named_denote_constant_agreement)
    fix s \<sigma> assume "s \<in> gi_named_consts ?M'"
    then obtain c where member: "c \<in> gi_named_consts M" and s: "s = ?\<iota> c"
      by (auto simp: gi_named_consts_map)
    show "gi_exact_poly_glued A (gi_exact_name_decode M s) \<sigma> = pp_e_Bacon_glued_constants ?A' s \<sigma>"
      unfolding s gi_exact_name_decode_code[OF member] by (rule gi_exact_poly_glued_renamed[OF member, symmetric])
  qed
  have left: "gi_exact_poly_denote (gi_exact_poly_glued A) G g M =
      pp_e_eval (pp_e_Bacon_glued_constants ?A') pp_e_closed_env (gi_exact_decode G ?M')"
    unfolding gi_exact_poly_denote_def glued_agree
    by (rule gi_exact_closed_named_decoder_value[OF closed'])
  have right: "gi_exact_poly_denote (A n) G h M =
      pp_e_eval (?A' n) pp_e_closed_env (gi_exact_decode G ?M')"
    unfolding gi_exact_poly_denote_def
    by (rule gi_exact_closed_named_decoder_value[OF closed'])
  show ?thesis unfolding left right by (rule string_action)
qed

corollary gi_exact_Bacon_10_1_parametric_truth_branch:
  fixes A :: "nat \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ZF"
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and language: "book_theory_formula \<Sigma> G M"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_poly_propositional_term G M"
  shows "pp_e_holds (gi_exact_poly_denote (gi_exact_poly_glued A) G g M) [n] =
    pp_e_holds (gi_exact_poly_denote (A n) G h M) []"
proof -
  have action: "pp_b_action Prop [n] (gi_exact_poly_denote (gi_exact_poly_glued A) G g M) =
      gi_exact_poly_denote (A n) G h M"
    by (rule gi_exact_Bacon_10_1_parametric_action[OF family language closed_term fragment])
  have root_truth: "pp_e_holds (pp_b_action Prop [n] (gi_exact_poly_denote (gi_exact_poly_glued A) G g M)) [] =
      pp_e_holds (gi_exact_poly_denote (A n) G h M) []"
    by (rule arg_cong[where f="\<lambda>p. pp_e_holds p []", OF action])
  show ?thesis using root_truth by simp
qed

theorem gi_exact_Bacon_10_1_parametric:
  fixes A :: "nat \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> ZF"
  assumes family: "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow> Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "\<exists>C :: 'c \<Rightarrow> otype \<Rightarrow> ZF.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_e_domain \<sigma>)) \<and>
    (\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow> pp_b_action \<sigma> [n] (C c \<sigma>) = A n c \<sigma>) \<and>
    (\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow>
      gi_exact_poly_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n] (gi_exact_poly_denote C G g M) = gi_exact_poly_denote (A n) G h M)"
proof (rule exI[where x="gi_exact_poly_glued A"], intro conjI)
  show "\<forall>c \<sigma>. Elem (gi_exact_poly_glued A c \<sigma>) (pp_e_domain \<sigma>)"
    by (intro allI; rule gi_exact_poly_glued_typed[OF family])
next
  show "\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow> pp_b_action \<sigma> [n] (gi_exact_poly_glued A c \<sigma>) = A n c \<sigma>"
    by (intro allI impI; rule gi_exact_poly_glued_action[OF family]; assumption)
next
  show "\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow>
      gi_exact_poly_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n] (gi_exact_poly_denote (gi_exact_poly_glued A) G g M) = gi_exact_poly_denote (A n) G h M"
    by (intro allI impI; rule gi_exact_Bacon_10_1_parametric_action[OF family]; assumption)
qed

text \<open>
  For every type 'c of constant names, every family A of interpretations
  indexed by the branches n :: nat and typed at t-generated types, the
  glued interpretation gi_exact_poly_glued A realizes A n on the branch [n]
  for every closed named term of the t-generated fragment, evaluated by
  gi_exact_poly_denote. At 'c = string the evaluator coincides with the
  existing gi_exact_named_denote (gi_exact_poly_denote_string), so this
  strictly generalizes gi_exact_Bacon_10_1_named. The name coding is chosen
  per term on its finitely many constants; no injection of all names into
  strings and no countability of the signature is used or asserted. The
  branch family remains countable, and type e remains excluded, as in Bacon.
\<close>

end
