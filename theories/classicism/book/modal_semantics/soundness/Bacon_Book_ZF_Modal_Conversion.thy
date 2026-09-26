theory Bacon_Book_ZF_Modal_Conversion
  imports
    Bacon_Book_ZF_Modal_Identity_Clauses
    Bacon_Book_Environment_Development.Bacon_Book_Contextual_Reduction_Language
    Bacon_Book_Environment_Development.Bacon_Book_Variable_Substitution_Language
begin

section \<open>Substitution, beta and eta as equalities of values at every world\<close>

text \<open>
  The semantic substitution lemma is proved for arbitrary term types,
  worlds and typed assignments, with the source's named_free_for guard.
  Under a binder the moved assignment is updated, the substituted term is
  transported by naturality, and coincidence removes the binder from the
  replacement's evaluation. Beta and eta contractions then give equal
  values, and named_compatible_step lifts that equality through every
  context, comparing whole future graphs under abstraction. These are
  equalities of denotations, not merely truth at a world, which is what
  the H conversion constructors need at formula type.
\<close>

context book_ZF_modal_interpretation
begin

theorem denote_subst:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G A \<tau>"
    and replacement: "book_in_language book_minimal_logical_type UNIV signature G B (G x)"
    and free_for: "named_free_for B x A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (named_subst x B A) = J w (g(x := J w g B)) A"
  using language free_for ww typed
proof (induction A arbitrary: \<tau> w g)
  case (NVar n)
  have bm: "J w g B \<in> explode (D (G x) w)" by (rule denote_type[OF NVar.prems(3) replacement NVar.prems(4)])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(x := J w g B))" by (rule book_env_update[OF NVar.prems(4) bm])
  show ?case
  proof (cases "n = x")
    case True
    show ?thesis by (simp only: True named_subst.simps simp_thms if_True denote_variable[OF NVar.prems(3) updated] fun_upd_same)
  next
    case False
    show ?thesis
      by (simp only: named_subst.simps if_False False denote_variable[OF NVar.prems(3) updated]
        denote_variable[OF NVar.prems(3,4)] fun_upd_other[OF False])
  qed
next
  case (NConst c \<sigma>)
  have declared: "c \<in> signature \<sigma>" using NConst.prems(1) by (simp only: book_language_const_iff; blast)
  have bm: "J w g B \<in> explode (D (G x) w)" by (rule denote_type[OF NConst.prems(3) replacement NConst.prems(4)])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(x := J w g B))" by (rule book_env_update[OF NConst.prems(4) bm])
  show ?case by (simp only: named_subst.simps denote_constant[OF NConst.prems(3) declared NConst.prems(4)]
    denote_constant[OF NConst.prems(3) declared updated])
next
  case (NLogical l)
  have bm: "J w g B \<in> explode (D (G x) w)" by (rule denote_type[OF NLogical.prems(3) replacement NLogical.prems(4)])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(x := J w g B))" by (rule book_env_update[OF NLogical.prems(4) bm])
  show ?case by (simp only: named_subst.simps denote_logical[OF NLogical.prems(3,4)] denote_logical[OF NLogical.prems(3) updated])
next
  case (NApp F A)
  obtain \<sigma> where fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<tau>)"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
    by (rule book_language_App_obtain[OF NApp.prems(1)]; rule that; assumption)
  have ff: "named_free_for B x F" and fa: "named_free_for B x A" using NApp.prems(2) by simp_all
  have bm: "J w g B \<in> explode (D (G x) w)" by (rule denote_type[OF NApp.prems(3) replacement NApp.prems(4)])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(x := J w g B))" by (rule book_env_update[OF NApp.prems(4) bm])
  have fs: "book_in_language book_minimal_logical_type UNIV signature G (named_subst x B F) (Arr \<sigma> \<tau>)"
    and as: "book_in_language book_minimal_logical_type UNIV signature G (named_subst x B A) \<sigma>"
    by (rule book_variable_subst_language[OF fl replacement], rule book_variable_subst_language[OF al replacement])
  show ?case
    by (simp only: named_subst.simps denote_application[OF NApp.prems(3) fs as NApp.prems(4)]
      denote_application[OF NApp.prems(3) fl al updated] NApp.IH(1)[OF fl ff NApp.prems(3,4)] NApp.IH(2)[OF al fa NApp.prems(3,4)])
next
  case (NLam n A)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language book_minimal_logical_type UNIV signature G A \<rho>"
    by (rule book_language_Lam_obtain[OF NLam.prems(1)]; rule that; assumption)
  have bm: "J w g B \<in> explode (D (G x) w)" by (rule denote_type[OF NLam.prems(3) replacement NLam.prems(4)])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(x := J w g B))" by (rule book_env_update[OF NLam.prems(4) bm])
  show ?case
  proof (cases "n = x")
    case True
    have same: "named_subst x B (NLam n A) = NLam n A" by (simp only: named_subst.simps True simp_thms if_True)
    show ?thesis
      by (simp only: same; rule denote_coincidence[OF NLam.prems(1) NLam.prems(3,4) updated]; simp add: True)
  next
    case False
    have inner: "named_free_for B x A" and guard: "n \<notin> named_fv B \<or> x \<notin> named_fv A"
      using NLam.prems(2) False by simp_all
    show ?thesis
    proof (cases "x \<in> named_fv A")
      case xfree: False
      have same: "named_subst x B (NLam n A) = NLam n A"
        by (simp only: named_subst.simps False if_False named_subst_fresh[OF xfree])
      show ?thesis
        by (simp only: same; rule denote_coincidence[OF NLam.prems(1) NLam.prems(3,4) updated]; insert xfree; auto)
    next
      case xfree: True
      have nfresh: "n \<notin> named_fv B" using guard xfree by blast
      have subst_body: "book_in_language book_minimal_logical_type UNIV signature G (named_subst x B A) \<rho>"
        by (rule book_variable_subst_language[OF body replacement])
      have step: "named_subst x B (NLam n A) = NLam n (named_subst x B A)"
        by (simp only: named_subst.simps False if_False)
      show ?thesis
      proof (simp only: step denote_abstraction[OF NLam.prems(3) subst_body NLam.prems(4)]
          denote_abstraction[OF NLam.prems(3) body updated],
          rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
        fix p
        assume member: "Elem p (book_ZF_pairs W R (D (G n)) w)"
        have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
          and am: "Snd p \<in> explode (D (G n) (Fst p))"
          using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
        let ?v = "Fst p" and ?a = "Snd p"
        have moved: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> ?v)) G (book_ZF_move i G w ?v g)"
          by (rule assignment_move_typed[OF NLam.prems(3) vw access NLam.prems(4)])
        have moved_updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> ?v)) G ((book_ZF_move i G w ?v g)(n := ?a))"
          by (rule book_env_update[OF moved am])
        have ih: "J ?v ((book_ZF_move i G w ?v g)(n := ?a)) (named_subst x B A) =
          J ?v (((book_ZF_move i G w ?v g)(n := ?a))(x := J ?v ((book_ZF_move i G w ?v g)(n := ?a)) B)) A"
          by (rule NLam.IH[OF body inner vw moved_updated])
        have drop: "J ?v ((book_ZF_move i G w ?v g)(n := ?a)) B = J ?v (book_ZF_move i G w ?v g) B"
          by (rule denote_coincidence[OF replacement vw moved_updated moved]; insert nfresh; auto)
        have natural: "J ?v (book_ZF_move i G w ?v g) B = i (G x) w ?v (J w g B)"
          by (rule denote_natural[OF replacement NLam.prems(3) vw access NLam.prems(4), symmetric])
        have swap: "((book_ZF_move i G w ?v g)(n := ?a))(x := i (G x) w ?v (J w g B)) =
          (book_ZF_move i G w ?v (g(x := J w g B)))(n := ?a)"
          by (simp only: book_ZF_move_update fun_upd_twist[OF False])
        show "J ?v ((book_ZF_move i G w ?v g)(n := ?a)) (named_subst x B A) =
          J ?v ((book_ZF_move i G w ?v (g(x := J w g B)))(n := ?a)) A"
          by (simp only: ih drop natural swap)
      qed
    qed
  qed
qed

theorem denote_beta_contract:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G M \<tau>"
    and step: "named_beta_contract M N"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g M = J w g N"
  using step language
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  obtain \<sigma> where lam: "book_in_language book_minimal_logical_type UNIV signature G (NLam x A) (Arr \<sigma> \<tau>)"
    and bl: "book_in_language book_minimal_logical_type UNIV signature G B \<sigma>"
    by (rule book_language_App_obtain[OF beta.prems]; rule that; assumption)
  obtain \<rho> where arrow: "Arr \<sigma> \<tau> = Arr (G x) \<rho>"
    and body: "book_in_language book_minimal_logical_type UNIV signature G A \<rho>"
    by (rule book_language_Lam_obtain[OF lam]; rule that; assumption)
  have st: "\<sigma> = G x" using arrow by simp
  have bt: "book_in_language book_minimal_logical_type UNIV signature G B (G x)" using bl by (simp only: st)
  show ?case
    by (simp only: unary_abstraction_value[OF body bt ww typed] denote_subst[OF body bt beta.hyps ww typed])
qed

theorem denote_eta_contract:
  assumes language: "book_in_language book_minimal_logical_type UNIV signature G M \<tau>"
    and step: "named_eta_contract M N"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g M = J w g N"
  using step language
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  obtain \<rho> where arrow: "\<tau> = Arr (G x) \<rho>"
    and body: "book_in_language book_minimal_logical_type UNIV signature G (NApp F (NVar x)) \<rho>"
    by (rule book_language_Lam_obtain[OF eta.prems]; rule that; assumption)
  obtain \<sigma> where fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<rho>)"
    and xl: "book_in_language book_minimal_logical_type UNIV signature G (NVar x) \<sigma>"
    by (rule book_language_App_obtain[OF body]; rule that; assumption)
  have st: "\<sigma> = G x" using xl by (simp only: book_language_var_iff)
  have fx: "book_in_language book_minimal_logical_type UNIV signature G F (Arr (G x) \<rho>)" using fl by (simp only: st)
  have fm: "J w g F \<in> explode (D (Arr (G x) \<rho>) w)" by (rule denote_type[OF ww fx typed])
  have graph: "J w g F = Lambda (book_ZF_pairs W R (D (G x)) w) (app (J w g F))" by (rule function_graph[OF ww fm])
  show ?case
  proof (simp only: denote_abstraction[OF ww body typed], subst graph, rule iffD2[OF Lambda_ext],
      rule conjI[OF refl], intro allI impI)
    fix p
    assume member: "Elem p (book_ZF_pairs W R (D (G x)) w)"
    have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
      and am: "Snd p \<in> explode (D (G x) (Fst p))"
      using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
    let ?v = "Fst p" and ?a = "Snd p"
    have moved: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> ?v)) G (book_ZF_move i G w ?v g)"
      by (rule assignment_move_typed[OF ww vw access typed])
    have moved_updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> ?v)) G ((book_ZF_move i G w ?v g)(x := ?a))"
      by (rule book_env_update[OF moved am])
    have applied: "J ?v ((book_ZF_move i G w ?v g)(x := ?a)) (NApp F (NVar x)) =
      app (J ?v ((book_ZF_move i G w ?v g)(x := ?a)) F) (Opair ?v ?a)"
      by (simp only: denote_application[OF vw fx book_language_Var moved_updated]
        denote_variable[OF vw moved_updated] fun_upd_same)
    have drop: "J ?v ((book_ZF_move i G w ?v g)(x := ?a)) F = J ?v (book_ZF_move i G w ?v g) F"
      by (rule denote_coincidence[OF fx vw moved_updated moved]; insert eta.hyps; auto)
    have natural: "J ?v (book_ZF_move i G w ?v g) F = i (Arr (G x) \<rho>) w ?v (J w g F)"
      by (rule denote_natural[OF fx ww vw access typed, symmetric])
    have restricted: "i (Arr (G x) \<rho>) w ?v (J w g F) = book_ZF_restrict W R (D (G x)) ?v (J w g F)"
      by (rule function_restriction[OF ww vw access fm])
    have current: "Elem (Opair ?v ?a) (book_ZF_pairs W R (D (G x)) ?v)"
      using vw am reflexive[OF vw] by (simp only: book_ZF_pairs_member explode_Elem)
    have shape: "Opair ?v ?a = p" by (rule book_ZF_pairs_data(4)[OF member])
    show "J ?v ((book_ZF_move i G w ?v g)(x := ?a)) (NApp F (NVar x)) = app (J w g F) p"
      by (simp only: applied drop natural restricted book_ZF_restrict_app[OF current]; simp only: shape)
  qed
qed

theorem denote_compatible_step:
  assumes step: "named_compatible_step S M N"
    and roots: "\<And>M N \<rho> v h. S M N \<Longrightarrow> book_in_language book_minimal_logical_type UNIV signature G M \<rho> \<Longrightarrow>
      v \<in> explode W \<Longrightarrow> book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> v)) G h \<Longrightarrow> J v h M = J v h N"
    and root_language: "\<And>M N \<rho>. S M N \<Longrightarrow> book_in_language book_minimal_logical_type UNIV signature G M \<rho> \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV signature G N \<rho>"
    and language: "book_in_language book_minimal_logical_type UNIV signature G M \<tau>"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g M = J w g N"
  using step language ww typed
proof (induction arbitrary: \<tau> w g rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule roots[OF root.hyps root.prems])
next
  case (App_left M M' N)
  obtain \<sigma> where head: "book_in_language book_minimal_logical_type UNIV signature G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language book_minimal_logical_type UNIV signature G N \<sigma>"
    by (rule book_language_App_obtain[OF App_left.prems(1)]; rule that; assumption)
  have head': "book_in_language book_minimal_logical_type UNIV signature G M' (Arr \<sigma> \<tau>)"
    by (rule book_compatible_step_language[OF App_left.hyps root_language head])
  show ?case
    by (simp only: denote_application[OF App_left.prems(2) head argument App_left.prems(3)]
      denote_application[OF App_left.prems(2) head' argument App_left.prems(3)] App_left.IH[OF head App_left.prems(2,3)])
next
  case (App_right N N' M)
  obtain \<sigma> where head: "book_in_language book_minimal_logical_type UNIV signature G M (Arr \<sigma> \<tau>)"
    and argument: "book_in_language book_minimal_logical_type UNIV signature G N \<sigma>"
    by (rule book_language_App_obtain[OF App_right.prems(1)]; rule that; assumption)
  have argument': "book_in_language book_minimal_logical_type UNIV signature G N' \<sigma>"
    by (rule book_compatible_step_language[OF App_right.hyps root_language argument])
  show ?case
    by (simp only: denote_application[OF App_right.prems(2) head argument App_right.prems(3)]
      denote_application[OF App_right.prems(2) head argument' App_right.prems(3)] App_right.IH[OF argument App_right.prems(2,3)])
next
  case (Lam_body M M' n)
  obtain \<rho> where arrow: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language book_minimal_logical_type UNIV signature G M \<rho>"
    by (rule book_language_Lam_obtain[OF Lam_body.prems(1)]; rule that; assumption)
  have body': "book_in_language book_minimal_logical_type UNIV signature G M' \<rho>"
    by (rule book_compatible_step_language[OF Lam_body.hyps root_language body])
  show ?case
  proof (simp only: denote_abstraction[OF Lam_body.prems(2) body Lam_body.prems(3)]
      denote_abstraction[OF Lam_body.prems(2) body' Lam_body.prems(3)],
      rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix p
    assume member: "Elem p (book_ZF_pairs W R (D (G n)) w)"
    have vw: "Fst p \<in> explode W" and access: "R w (Fst p)"
      and am: "Snd p \<in> explode (D (G n) (Fst p))"
      using book_ZF_pairs_data[OF member] by (auto simp only: explode_Elem)
    have moved: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> (Fst p))) G ((book_ZF_move i G w (Fst p) g)(n := Snd p))"
      by (rule book_env_update[OF assignment_move_typed[OF Lam_body.prems(2) vw access Lam_body.prems(3)] am])
    show "J (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) M = J (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) M'"
      by (rule Lam_body.IH[OF body vw moved])
  qed
qed

theorem beta_contract_language:
  assumes step: "named_beta_contract M N"
    and language: "book_in_language book_minimal_logical_type UNIV signature G M \<rho>"
  shows "book_in_language book_minimal_logical_type UNIV signature G N \<rho>"
  using step language
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  obtain \<sigma> where lam: "book_in_language book_minimal_logical_type UNIV signature G (NLam x A) (Arr \<sigma> \<rho>)"
    and bl: "book_in_language book_minimal_logical_type UNIV signature G B \<sigma>"
    by (rule book_language_App_obtain[OF beta.prems]; rule that; assumption)
  obtain \<rho>' where arrow: "Arr \<sigma> \<rho> = Arr (G x) \<rho>'"
    and body: "book_in_language book_minimal_logical_type UNIV signature G A \<rho>'"
    by (rule book_language_Lam_obtain[OF lam]; rule that; assumption)
  have st: "\<sigma> = G x" and rt: "\<rho>' = \<rho>" using arrow by simp_all
  show ?case by (rule book_variable_subst_language[OF body[unfolded rt]]; simp only: st[symmetric]; rule bl)
qed

theorem eta_contract_language:
  assumes step: "named_eta_contract M N"
    and language: "book_in_language book_minimal_logical_type UNIV signature G M \<rho>"
  shows "book_in_language book_minimal_logical_type UNIV signature G N \<rho>"
  using step language
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  obtain \<rho>' where arrow: "\<rho> = Arr (G x) \<rho>'"
    and body: "book_in_language book_minimal_logical_type UNIV signature G (NApp F (NVar x)) \<rho>'"
    by (rule book_language_Lam_obtain[OF eta.prems]; rule that; assumption)
  obtain \<sigma> where fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> \<rho>')"
    and xl: "book_in_language book_minimal_logical_type UNIV signature G (NVar x) \<sigma>"
    by (rule book_language_App_obtain[OF body]; rule that; assumption)
  have st: "\<sigma> = G x" using xl by (simp only: book_language_var_iff)
  show ?case using fl by (simp only: arrow st)
qed

theorem denote_beta_step:
  assumes step: "named_compatible_step named_beta_contract M N"
    and language: "book_in_language book_minimal_logical_type UNIV signature G M \<tau>"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g M = J w g N"
  by (rule denote_compatible_step[OF step _ _ language ww typed];
    (rule denote_beta_contract | rule beta_contract_language); assumption)

theorem denote_eta_step:
  assumes step: "named_compatible_step named_eta_contract M N"
    and language: "book_in_language book_minimal_logical_type UNIV signature G M \<tau>"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g M = J w g N"
  by (rule denote_compatible_step[OF step _ _ language ww typed];
    (rule denote_eta_contract | rule eta_contract_language); assumption)

end

end
