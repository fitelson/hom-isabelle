theory Bacon_Book_ZF_Generic_Abstraction
  imports Bacon_Book_ZF_Combinatory_Evaluation
begin

context book_ZF_modal_model
begin

theorem generic_comb_abstract_current:
  assumes ct: "book_comb_typed signature G A \<tau>"
    and ww: "w \<in> explode W"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and am: "a \<in> explode (D (G n) w)"
  shows "app (generic_comb_eval G w g (book_comb_abstract G n A)) (Opair w a) =
    generic_comb_eval G w (g(n := a)) A"
  using ct ww env am
proof (induction arbitrary: w g a rule: book_comb_typed.induct)
  case (Var m)
  show ?case
  proof (cases "n = m")
    case True
    have identity: "app (generic_identity w (G n)) (Opair w a) = a"
      by (rule generic_identity_future[OF Var.prems(1,1) reflexive[OF Var.prems(1)] Var.prems(3)])
    show ?thesis using identity
      by (simp add: True)
  next
    case False
    have different: "m \<noteq> n" using False by blast
    have gm: "g m \<in> explode (D (G m) w)" by (rule book_env_at[OF Var.prems(2)])
    have constant_value: "app (app (book_ZF_k W R D i w (G m) (G n)) (Opair w (g m))) (Opair w a) = g m"
      by (rule generic_k_current[OF Var.prems(1) gm Var.prems(3)])
    show ?thesis using constant_value
      by (simp add: False different generic_comb_eval_apply)
  qed
next
  case (Const c \<sigma>)
  have val_typed: "i \<sigma> root w (I c \<sigma>) \<in> explode (D \<sigma> w)"
    by (rule transport_type[OF root_world Const.prems(1) root_below[OF Const.prems(1)] constants[OF Const.hyps]])
  show ?case
    by (simp only: book_comb_abstract.simps book_comb_type.simps generic_comb_eval_apply generic_comb_eval.simps;
      rule generic_k_current[OF Const.prems(1) val_typed Const.prems(3)])
next
  case (Logical l)
  have val_typed: "i (book_minimal_logical_type l) root w (book_ZF_logical_root W R D i root l)
      \<in> explode (D (book_minimal_logical_type l) w)"
    by (rule transport_type[OF root_world Logical.prems(1) root_below[OF Logical.prems(1)] logical_root_type])
  show ?case
    by (simp only: book_comb_abstract.simps book_comb_type.simps generic_comb_eval_apply generic_comb_eval.simps;
      rule generic_k_current[OF Logical.prems(1) val_typed Logical.prems(3)])
next
  case K
  show ?case
    by (simp only: book_comb_abstract.simps book_comb_type.simps generic_comb_eval_apply generic_comb_eval.simps;
      rule generic_k_current[OF K.prems(1) k_member_at[OF K.prems(1)] K.prems(3)])
next
  case S
  show ?case
    by (simp only: book_comb_abstract.simps book_comb_type.simps generic_comb_eval_apply generic_comb_eval.simps;
      rule generic_k_current[OF S.prems(1) s_member_at[OF S.prems(1)] S.prems(3)])
next
  case Id
  show ?case
    by (simp only: book_comb_abstract.simps book_comb_type.simps generic_comb_eval_apply generic_comb_eval.simps;
      rule generic_k_current[OF Id.prems(1) generic_identity_type[OF Id.prems(1)] Id.prems(3)])
next
  case (App F \<sigma> \<tau> A)
  have ft: "generic_comb_eval G w g (book_comb_abstract G n F)
      \<in> explode (D (Arr (G n) (Arr \<sigma> \<tau>)) w)"
    by (rule generic_comb_eval_type[OF book_comb_abstract_typed[OF App.hyps(1)] App.prems(1,2)])
  have at: "generic_comb_eval G w g (book_comb_abstract G n A) \<in> explode (D (Arr (G n) \<sigma>) w)"
    by (rule generic_comb_eval_type[OF book_comb_abstract_typed[OF App.hyps(2)] App.prems(1,2)])
  show ?case
    by (simp only: book_comb_abstract.simps generic_comb_eval_apply generic_comb_eval.simps
      generic_s_current[OF App.prems(1) ft at App.prems(3)]
      App.IH(1)[OF App.prems] App.IH(2)[OF App.prems])
qed

theorem generic_comb_abstract_future:
  assumes ct: "book_comb_typed signature G A \<tau>"
    and ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and am: "a \<in> explode (D (G n) v)"
  shows "app (generic_comb_eval G w g (book_comb_abstract G n A)) (Opair v a) =
    generic_comb_eval G v ((book_ZF_move i G w v g)(n := a)) A"
proof -
  let ?F = "generic_comb_eval G w g (book_comb_abstract G n A)"
  have ft: "?F \<in> explode (D (Arr (G n) \<tau>) w)"
    by (rule generic_comb_eval_type[OF book_comb_abstract_typed[OF ct] ww env])
  have restricted: "app ?F (Opair v a) = app (i (Arr (G n) \<tau>) w v ?F) (Opair v a)"
    by (rule sym[OF generic_restricted_application[OF ww vw wv ft am]])
  have natural: "i (Arr (G n) \<tau>) w v ?F =
    generic_comb_eval G v (book_ZF_move i G w v g) (book_comb_abstract G n A)"
    by (rule generic_comb_eval_natural[OF book_comb_abstract_typed[OF ct] ww vw wv env])
  show ?thesis using restricted
    by (simp only: natural generic_comb_abstract_current[OF ct vw assignment_move_typed[OF ww vw wv env] am])
qed

theorem generic_comb_abstract_graph:
  assumes ct: "book_comb_typed signature G A \<tau>"
    and ww: "w \<in> explode W"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "generic_comb_eval G w g (book_comb_abstract G n A) =
    Lambda (book_ZF_pairs W R (D (G n)) w)
      (\<lambda>p. generic_comb_eval G (Fst p) ((book_ZF_move i G w (Fst p) g)(n := Snd p)) A)"
  by (rule function_as_lambda[OF ww generic_comb_eval_type[OF book_comb_abstract_typed[OF ct] ww env]];
    simp only: Fst Snd; rule generic_comb_abstract_future[OF ct ww _ _ env]; assumption)

end

text \<open>
  Closure under abstraction is derived: the combinatory value belongs to
  the chosen function domain and equals the full future Lambda graph.
  In particular, this is not merely a current-world beta calculation.
  All assignment and future-domain guards are retained, so no separate
  nonemptiness assumption is needed.
\<close>

end
