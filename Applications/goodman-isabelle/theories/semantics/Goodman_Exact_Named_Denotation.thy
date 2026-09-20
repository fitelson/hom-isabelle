theory Goodman_Exact_Named_Denotation
  imports Goodman_Exact_Applicative_Adapter
    "Bacon_Book_Environment_Development.Bacon_Book_Named_Translation"
begin

section \<open>Named terms interpreted in Bacon's exact carriers\<close>

text \<open>
  For a named term A, first use the core's existing binding translation
  book_named_to_pterm, then the proved string-syntax decoder pterm_to_oterm.
  Evaluate that term with the exact appendix evaluator pp_e_eval.
  This definition neither modifies the carriers nor supplies additional
  denotations. The nonlogical names in this first adapter are strings.

  We establish variables, constants, application, typing, and same-term
  locality. We do not yet assert βη preservation between different terms,
  the book environment condition, primitive logical truth clauses, the
  old-to-new all-type denotation equation, or global soundness.
\<close>

definition gi_exact_named_denote ::
  "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow> sgcontext \<Rightarrow>
    (nat \<Rightarrow> ZF) \<Rightarrow> string book_named_term \<Rightarrow> ZF" where
  "gi_exact_named_denote C G g A =
    pp_e_eval C g (pterm_to_oterm (book_named_to_pterm G A))"

lemma gi_exact_named_denote_var:
  "gi_exact_named_denote C G g (NVar n) = g n"
  by (simp only: gi_exact_named_denote_def book_named_translation_Var
      pterm_to_oterm.simps pp_e_eval.simps)

lemma gi_exact_named_denote_const:
  "gi_exact_named_denote C G g (NConst c \<sigma>) = C c \<sigma>"
  by (simp only: gi_exact_named_denote_def book_named_translation_Const
      pterm_to_oterm.simps pp_e_eval.simps)

lemma gi_exact_named_denote_app:
  "gi_exact_named_denote C G g (NApp F A) =
    gi_exact_app \<sigma> \<tau>
      (gi_exact_named_denote C G g F) (gi_exact_named_denote C G g A)"
  by (simp only: gi_exact_named_denote_def book_named_translation_App
      pterm_to_oterm.simps pp_e_eval.simps gi_exact_app_value)

section \<open>Total assignments are typed on every finite prefix\<close>

lemma gi_exact_assignment_prefix:
  assumes assignment_type: "book_env_typed gi_exact_domain G g"
  shows "pp_e_env_typed (source_prefix G m) g"
proof (unfold pp_e_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume index_type: "lookup (source_prefix G m) n = Some \<sigma>"
  have index_bound: "n < m"
    using index_type
    by (auto simp: source_prefix_def lookup_def split: if_splits)
  have stock_lookup: "lookup (source_prefix G m) n = Some (G n)"
    by (rule source_prefix_lookup[OF index_bound])
  have same_type: "G n = \<sigma>"
    using stock_lookup index_type by simp
  have assigned_member: "Elem (g n) (pp_e_domain (G n))"
    by (rule gi_exact_assignment_lookup[OF assignment_type])
  show "Elem (g n) (pp_e_domain \<sigma>)"
    using assigned_member same_type by simp
qed

context pp_e_constants
begin

theorem gi_exact_named_denote_type:
  assumes term_language:
      "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and assignment_type: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_named_denote C G g A \<in> gi_exact_domain \<tau>"
proof -
  let ?m = "source_free_bound (named_to_source G [] A)"
  have translated_language:
      "pterm_in_language \<Sigma> (source_prefix G ?m)
        (book_named_to_pterm G A) \<tau>"
    by (rule book_named_translation_language_prefix[OF term_language le_refl])
  have translated_type:
      "has_ptype (source_prefix G ?m) (book_named_to_pterm G A) \<tau>"
    using translated_language unfolding pterm_in_language_def by blast
  have decoded_type:
      "source_prefix G ?m \<turnstile>
        pterm_to_oterm (book_named_to_pterm G A) : \<tau>"
    by (rule pterm_to_preserves_typing[OF translated_type])
  have prefix_assignment: "pp_e_env_typed (source_prefix G ?m) g"
    by (rule gi_exact_assignment_prefix[OF assignment_type])
  have denotation_member:
      "pp_e_dom \<tau>
        (pp_e_eval C g (pterm_to_oterm (book_named_to_pterm G A)))"
    by (rule pp_e_eval_type[OF decoded_type prefix_assignment])
  show ?thesis
    using denotation_member
    by (simp only: gi_exact_named_denote_def gi_exact_domain_member pp_e_dom_def)
qed

end

section \<open>Same-term locality of exact denotation\<close>

lemma gi_exact_pterm_eval_locality:
  assumes agreement: "\<And>n. n \<in> pbbk_fv A \<Longrightarrow> g n = h n"
  shows "pp_e_eval C g (pterm_to_oterm A) =
    pp_e_eval C h (pterm_to_oterm A)"
  using agreement
proof (induction A arbitrary: g h)
  case (PVar n)
  have same_variable: "g n = h n"
    by (rule PVar.prems; simp only: pbbk_fv.simps singleton_iff)
  show ?case by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_variable)
next
  case (PConst c \<sigma>)
  show ?case by (simp only: pterm_to_oterm.simps pp_e_eval.simps)
next
  case (PApp A B)
  have left_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PApp.prems; simp only: pbbk_fv.simps; rule UnI1[OF free_name])
  have right_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv B" for n
    by (rule PApp.prems; simp only: pbbk_fv.simps; rule UnI2[OF free_name])
  have same_left: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PApp.IH(1); rule left_agreement; assumption)
  have same_right: "pp_e_eval C g (pterm_to_oterm B) = pp_e_eval C h (pterm_to_oterm B)"
    by (rule PApp.IH(2); rule right_agreement; assumption)
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_left same_right)
next
  case (PLam \<sigma> A)
  have same_body:
      "pp_e_eval C (extend_env x g) (pterm_to_oterm A) =
        pp_e_eval C (extend_env x h) (pterm_to_oterm A)" for x
  proof (rule PLam.IH)
    fix n
    assume free_name: "n \<in> pbbk_fv A"
    show "extend_env x g n = extend_env x h n"
      using PLam.prems free_name by (cases n) auto
  qed
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_body)
next
  case (PEq \<sigma> A B)
  have left_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PEq.prems; simp only: pbbk_fv.simps; rule UnI1[OF free_name])
  have right_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv B" for n
    by (rule PEq.prems; simp only: pbbk_fv.simps; rule UnI2[OF free_name])
  have same_left: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PEq.IH(1); rule left_agreement; assumption)
  have same_right: "pp_e_eval C g (pterm_to_oterm B) = pp_e_eval C h (pterm_to_oterm B)"
    by (rule PEq.IH(2); rule right_agreement; assumption)
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_left same_right)
next
  case (PNeg A)
  have body_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PNeg.prems; simp only: pbbk_fv.simps; rule free_name)
  have same_body: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PNeg.IH; rule body_agreement; assumption)
  show ?case by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_body)
next
  case (PConj A B)
  have left_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PConj.prems; simp only: pbbk_fv.simps; rule UnI1[OF free_name])
  have right_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv B" for n
    by (rule PConj.prems; simp only: pbbk_fv.simps; rule UnI2[OF free_name])
  have same_left: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PConj.IH(1); rule left_agreement; assumption)
  have same_right: "pp_e_eval C g (pterm_to_oterm B) = pp_e_eval C h (pterm_to_oterm B)"
    by (rule PConj.IH(2); rule right_agreement; assumption)
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_left same_right)
next
  case (PDisj A B)
  have left_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PDisj.prems; simp only: pbbk_fv.simps; rule UnI1[OF free_name])
  have right_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv B" for n
    by (rule PDisj.prems; simp only: pbbk_fv.simps; rule UnI2[OF free_name])
  have same_left: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PDisj.IH(1); rule left_agreement; assumption)
  have same_right: "pp_e_eval C g (pterm_to_oterm B) = pp_e_eval C h (pterm_to_oterm B)"
    by (rule PDisj.IH(2); rule right_agreement; assumption)
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_left same_right)
next
  case (PImp A B)
  have left_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv A" for n
    by (rule PImp.prems; simp only: pbbk_fv.simps; rule UnI1[OF free_name])
  have right_agreement: "g n = h n" if free_name: "n \<in> pbbk_fv B" for n
    by (rule PImp.prems; simp only: pbbk_fv.simps; rule UnI2[OF free_name])
  have same_left: "pp_e_eval C g (pterm_to_oterm A) = pp_e_eval C h (pterm_to_oterm A)"
    by (rule PImp.IH(1); rule left_agreement; assumption)
  have same_right: "pp_e_eval C g (pterm_to_oterm B) = pp_e_eval C h (pterm_to_oterm B)"
    by (rule PImp.IH(2); rule right_agreement; assumption)
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_left same_right)
next
  case (PForall \<sigma> A)
  have same_body:
      "pp_e_eval C (extend_env x g) (pterm_to_oterm A) =
        pp_e_eval C (extend_env x h) (pterm_to_oterm A)" for x
  proof (rule PForall.IH)
    fix n
    assume free_name: "n \<in> pbbk_fv A"
    show "extend_env x g n = extend_env x h n"
      using PForall.prems free_name by (cases n) auto
  qed
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_body)
next
  case (PExists \<sigma> A)
  have same_body:
      "pp_e_eval C (extend_env x g) (pterm_to_oterm A) =
        pp_e_eval C (extend_env x h) (pterm_to_oterm A)" for x
  proof (rule PExists.IH)
    fix n
    assume free_name: "n \<in> pbbk_fv A"
    show "extend_env x g n = extend_env x h n"
      using PExists.prems free_name by (cases n) auto
  qed
  show ?case
    by (simp only: pterm_to_oterm.simps pp_e_eval.simps same_body)
qed

theorem gi_exact_named_denote_locality:
  assumes agreement: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "gi_exact_named_denote C G g A = gi_exact_named_denote C G h A"
proof (unfold gi_exact_named_denote_def, rule gi_exact_pterm_eval_locality)
  fix n
  assume translated_free: "n \<in> pbbk_fv (book_named_to_pterm G A)"
  have named_free: "n \<in> named_fv A"
    using translated_free by (simp only: book_named_translation_fv)
  show "g n = h n" by (rule agreement[OF named_free])
qed

corollary gi_exact_named_closed_assignment_independent:
  assumes closed_term: "named_fv A = {}"
  shows "gi_exact_named_denote C G g A = gi_exact_named_denote C G h A"
  by (rule gi_exact_named_denote_locality; simp only: closed_term empty_iff)

text \<open>
  The locality result is structural and therefore does not need typed
  assignments or a typed constant interpretation. The typing theorem
  above does require the locale pp_e_constants, which types every
  string/type constant value. This is stronger than typing only the
  declared signature and must remain visible until a separate completion
  of undeclared constants has been proved.

  The next semantic obligation is typed βη preservation for the decoded
  terms. Same-term locality proved here is not the environment condition
  for two convertible terms.
\<close>

end
