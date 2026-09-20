theory Goodman_Exact_10_1_Transfer
  imports
    "Goodman_Integration_Logical_Stock.Goodman_Exact_Stock_Correspondence"
    "Goodman_Exact_Legacy_06.Bacon_PP_ZF_Exact_10_1"
begin

section \<open>The t-generated fragment in the named minimal language\<close>

text \<open>
  Bacon's gluing construction applies to types generated from t by →,
  not to types involving the individual type e. The named fragment below
  checks the occurrence types of constants and logical symbols and the
  type of every abstraction binder. Bare variables introduce no new type
  annotation. Closedness and ordinary typing ensure that a term in this
  fragment also has a t-generated result type, as proved below.

  This is a syntactic predicate on the full named minimal grammar, not
  a definition in terms of the desired gluing equation. The decoding
  theorem proves its correspondence to the original fragment predicate.
\<close>

fun gi_exact_named_propositional_term ::
  "sgcontext \<Rightarrow> string book_named_term \<Rightarrow> bool" where
  "gi_exact_named_propositional_term G (NVar n) = True"
| "gi_exact_named_propositional_term G (NConst c \<sigma>) = pp_e_propositional_type \<sigma>"
| "gi_exact_named_propositional_term G (NLogical l) =
    pp_e_propositional_type (book_minimal_logical_type l)"
| "gi_exact_named_propositional_term G (NApp F A) =
    (gi_exact_named_propositional_term G F \<and> gi_exact_named_propositional_term G A)"
| "gi_exact_named_propositional_term G (NLam n A) =
    (pp_e_propositional_type (G n) \<and> gi_exact_named_propositional_term G A)"

lemma gi_exact_minimal_logical_propositional_fragment:
  "pp_e_propositional_term (pterm_to_oterm (book_minimal_logical_translation l)) =
    pp_e_propositional_type (book_minimal_logical_type l)"
  by (cases l) simp_all

lemma gi_exact_named_propositional_encoding:
  "pp_e_propositional_term
      (pterm_to_oterm (book_minimal_to_pterm (named_to_source G ns M))) =
    gi_exact_named_propositional_term G M"
  by (induction M arbitrary: ns)
    (simp_all add: gi_exact_minimal_logical_propositional_fragment)

theorem gi_exact_named_propositional_decode_iff:
  "pp_e_propositional_term (gi_exact_decode G M) \<longleftrightarrow>
    gi_exact_named_propositional_term G M"
  by (simp only: gi_exact_decode_def book_named_to_pterm_def
      gi_exact_named_propositional_encoding)

lemma gi_exact_old_propositional_result_type:
  assumes term_type: "\<Gamma> \<turnstile> M : \<tau>"
    and fragment: "pp_e_propositional_term M"
    and context_types: "\<forall>\<sigma>\<in>set \<Gamma>. pp_e_propositional_type \<sigma>"
  shows "pp_e_propositional_type \<tau>"
  using term_type fragment context_types
  by (induction rule: has_type.induct)
    (auto simp: lookup_def intro: nth_mem split: if_splits)

theorem gi_exact_closed_named_propositional_result_type:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "pp_e_propositional_type \<tau>"
proof -
  have decoded_type: "[] \<turnstile> gi_exact_decode G M : \<tau>"
    by (rule gi_closed_named_decode_type[OF language closed_term])
  have decoded_fragment: "pp_e_propositional_term (gi_exact_decode G M)"
    by (simp only: gi_exact_named_propositional_decode_iff; rule fragment)
  show ?thesis
    by (rule gi_exact_old_propositional_result_type[OF decoded_type decoded_fragment]; simp)
qed

section \<open>Every closed named term has its actual decoded denotation\<close>

lemma gi_exact_closed_named_decoder_value:
  assumes closed_term: "named_fv M = {}"
  shows "gi_exact_named_denote C G g M = pp_e_eval C pp_e_closed_env (gi_exact_decode G M)"
proof -
  have independent: "gi_exact_named_denote C G g M =
      gi_exact_named_denote C G pp_e_closed_env M"
    by (rule gi_exact_named_closed_assignment_independent[OF closed_term])
  show ?thesis using independent
    by (simp only: gi_exact_named_denote_def gi_exact_decode_def)
qed

text \<open>
  Closed-assignment independence is structural. The displayed lemma does
  not require the all-Empty old assignment to be a total G-typed assignment,
  nor does it assume a logical or constant-free term. This allows the next
  theorem to retain arbitrary nonlogical interpretations at t-generated
  types rather than replacing them by the default interpretation.
\<close>

section \<open>Bacon's Theorem 10.1 for all closed named terms of the fragment\<close>

theorem gi_exact_Bacon_10_1_named_action:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau>"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "pp_b_action \<tau> [n]
      (gi_exact_named_denote (pp_e_Bacon_glued_constants A) G g M) =
    gi_exact_named_denote (A n) G h M"
proof -
  have decoded_type: "[] \<turnstile> gi_exact_decode G M : \<tau>"
    by (rule gi_closed_named_decode_type[OF language closed_term])
  have decoded_fragment: "pp_e_propositional_term (gi_exact_decode G M)"
    by (simp only: gi_exact_named_propositional_decode_iff; rule fragment)
  have decoded_action:
      "pp_b_action \<tau> [n]
        (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env (gi_exact_decode G M)) =
        pp_e_eval (A n) pp_e_closed_env (gi_exact_decode G M)"
    by (rule pp_e_Bacon_10_1_term_action[OF family decoded_type decoded_fragment])
  show ?thesis
    by (simp only: gi_exact_closed_named_decoder_value[OF closed_term]; rule decoded_action)
qed

corollary gi_exact_Bacon_10_1_named_truth_branch:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and language: "book_theory_formula \<Sigma> G M"
    and closed_term: "named_fv M = {}"
    and fragment: "gi_exact_named_propositional_term G M"
  shows "pp_e_holds (gi_exact_named_denote (pp_e_Bacon_glued_constants A) G g M) [n] =
    pp_e_holds (gi_exact_named_denote (A n) G h M) []"
proof -
  have action: "pp_b_action Prop [n]
      (gi_exact_named_denote (pp_e_Bacon_glued_constants A) G g M) =
      gi_exact_named_denote (A n) G h M"
    by (rule gi_exact_Bacon_10_1_named_action[OF family language closed_term fragment])
  have root_truth:
      "pp_e_holds (pp_b_action Prop [n]
        (gi_exact_named_denote (pp_e_Bacon_glued_constants A) G g M)) [] =
        pp_e_holds (gi_exact_named_denote (A n) G h M) []"
    by (rule arg_cong[where f="\<lambda>p. pp_e_holds p []", OF action])
  show ?thesis using root_truth by simp
qed

theorem gi_exact_Bacon_10_1_named:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_e_domain \<sigma>)) \<and>
    (\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
      pp_b_action \<sigma> [n] (C c \<sigma>) = A n c \<sigma>) \<and>
    (\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow>
      gi_exact_named_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n] (gi_exact_named_denote C G g M) =
        gi_exact_named_denote (A n) G h M)"
proof (rule exI[where x="pp_e_Bacon_glued_constants A"], intro conjI)
  show "\<forall>c \<sigma>. Elem (pp_e_Bacon_glued_constants A c \<sigma>) (pp_e_domain \<sigma>)"
    by (intro allI; rule pp_e_Bacon_glued_constants_typed[OF family])
next
  show "\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
      pp_b_action \<sigma> [n] (pp_e_Bacon_glued_constants A c \<sigma>) = A n c \<sigma>"
    by (intro allI impI; rule pp_e_Bacon_glued_constants_action[OF family]; assumption)
next
  show "\<forall>n G \<Sigma> M \<tau> g h.
      book_in_language book_minimal_logical_type UNIV \<Sigma> G M \<tau> \<longrightarrow>
      named_fv M = {} \<longrightarrow>
      gi_exact_named_propositional_term G M \<longrightarrow>
      pp_b_action \<tau> [n] (gi_exact_named_denote (pp_e_Bacon_glued_constants A) G g M) =
        gi_exact_named_denote (A n) G h M"
    by (intro allI impI; rule gi_exact_Bacon_10_1_named_action[OF family]; assumption)
qed

text \<open>
  One exact interpretation C simultaneously realizes the given countable
  sequence of interpretations on the branches [n]. The theorem covers
  every closed named string term in the syntactically specified fragment,
  not only terms obtained by forward translation from the old syntax.
  Family typing is required only at t-generated types, exactly as in the
  preserved construction; C itself is typed at every represented type.

  No richness premise is needed for this decoder-based transfer, and g,h
  may be arbitrary because M is closed. This is the exact branch-gluing
  result, relative to HOL–ZF. It neither identifies the glued constants
  with the separate generic-seed interpretation nor proves PP or a new
  completeness theorem.
\<close>

end
