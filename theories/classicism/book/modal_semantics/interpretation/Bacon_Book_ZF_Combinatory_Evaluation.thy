theory Bacon_Book_ZF_Combinatory_Evaluation
  imports Bacon_Book_ZF_Generic_Combinators Bacon_Book_Combinatory_Translation
begin

context book_ZF_modal_model
begin

fun generic_comb_eval :: "sgcontext \<Rightarrow> ZF \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> 'c book_comb \<Rightarrow> ZF" where
  "generic_comb_eval G w g (BCVar n) = g n"
| "generic_comb_eval G w g (BCConst c \<sigma>) = i \<sigma> root w (I c \<sigma>)"
| "generic_comb_eval G w g (BCLogical l) =
    i (book_minimal_logical_type l) root w (book_ZF_logical_root W R D i root l)"
| "generic_comb_eval G w g (BCK \<sigma> \<tau>) = book_ZF_k W R D i w \<sigma> \<tau>"
| "generic_comb_eval G w g (BCS \<sigma> \<tau> \<rho>) = book_ZF_s W R D w \<sigma> \<tau> \<rho>"
| "generic_comb_eval G w g (BCId \<sigma>) = generic_identity w \<sigma>"
| "generic_comb_eval G w g (BCApp \<sigma> \<tau> F A) =
    app (generic_comb_eval G w g F) (Opair w (generic_comb_eval G w g A))"

lemma generic_comb_eval_apply:
  "generic_comb_eval G w g (book_comb_apply G F A) =
    app (generic_comb_eval G w g F) (Opair w (generic_comb_eval G w g A))"
  by (simp only: book_comb_apply_def generic_comb_eval.simps)

theorem generic_comb_eval_type:
  assumes ct: "book_comb_typed signature G A \<tau>" and ww: "w \<in> explode W"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "generic_comb_eval G w g A \<in> explode (D \<tau> w)"
  using ct ww env
proof (induction arbitrary: w g rule: book_comb_typed.induct)
  case (Var n)
  show ?case by (simp only: generic_comb_eval.simps; rule book_env_at[OF Var.prems(2)])
next
  case (Const c \<sigma>)
  show ?case by (simp only: generic_comb_eval.simps;
    rule transport_type[OF root_world Const.prems(1) root_below[OF Const.prems(1)] constants[OF Const.hyps]])
next
  case (Logical l)
  show ?case by (simp only: generic_comb_eval.simps;
    rule transport_type[OF root_world Logical.prems(1) root_below[OF Logical.prems(1)] logical_root_type])
next
  case K
  show ?case by (simp only: generic_comb_eval.simps; rule k_member_at[OF K.prems(1)])
next
  case S
  show ?case by (simp only: generic_comb_eval.simps; rule s_member_at[OF S.prems(1)])
next
  case Id
  show ?case by (simp only: generic_comb_eval.simps; rule generic_identity_type[OF Id.prems(1)])
next
  case App
  show ?case by (simp only: generic_comb_eval.simps;
    rule generic_app_type[OF App.prems(1) App.IH(1)[OF App.prems] App.IH(2)[OF App.prems]])
qed

theorem generic_comb_eval_natural:
  assumes ct: "book_comb_typed signature G A \<tau>"
    and ww: "w \<in> explode W" and vw: "v \<in> explode W" and wv: "R w v"
    and env: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "i \<tau> w v (generic_comb_eval G w g A) =
    generic_comb_eval G v (book_ZF_move i G w v g) A"
  using ct ww vw wv env
proof (induction arbitrary: w v g rule: book_comb_typed.induct)
  case (Var n)
  show ?case by (simp only: generic_comb_eval.simps book_ZF_move_def)
next
  case (Const c \<sigma>)
  show ?case by (simp only: generic_comb_eval.simps;
    rule sym[OF transport_composition[OF root_world Const.prems(1,2)
      root_below[OF Const.prems(1)] Const.prems(3) constants[OF Const.hyps]]])
next
  case (Logical l)
  show ?case by (simp only: generic_comb_eval.simps;
    rule sym[OF transport_composition[OF root_world Logical.prems(1,2)
      root_below[OF Logical.prems(1)] Logical.prems(3) logical_root_type]])
next
  case K
  show ?case by (simp only: generic_comb_eval.simps; rule generic_k_transport[OF K.prems(1,2,3)])
next
  case S
  show ?case by (simp only: generic_comb_eval.simps; rule generic_s_transport[OF S.prems(1,2,3)])
next
  case Id
  show ?case by (simp only: generic_comb_eval.simps; rule generic_identity_transport[OF Id.prems(1,2,3)])
next
  case (App F \<sigma> \<tau> A)
  let ?f = "generic_comb_eval G w g F"
  let ?a = "generic_comb_eval G w g A"
  have ft: "?f \<in> explode (D (Arr \<sigma> \<tau>) w)"
    by (rule generic_comb_eval_type[OF App.hyps(1) App.prems(1,4)])
  have at: "?a \<in> explode (D \<sigma> w)"
    by (rule generic_comb_eval_type[OF App.hyps(2) App.prems(1,4)])
  have moved: "i \<sigma> w v ?a \<in> explode (D \<sigma> v)"
    by (rule transport_type[OF App.prems(1,2,3) at])
  have natural: "i \<tau> w v (app ?f (Opair w ?a)) = app ?f (Opair v (i \<sigma> w v ?a))"
    by (rule function_natural[OF App.prems(1,1,2) reflexive[OF App.prems(1)] App.prems(3) ft at])
  have restricted: "app ?f (Opair v (i \<sigma> w v ?a)) =
    app (i (Arr \<sigma> \<tau>) w v ?f) (Opair v (i \<sigma> w v ?a))"
    by (rule sym[OF generic_restricted_application[OF App.prems(1,2,3) ft moved]])
  show ?case using trans[OF natural restricted]
    by (simp only: generic_comb_eval.simps App.IH(1)[OF App.prems] App.IH(2)[OF App.prems])
qed

text \<open>
  Evaluation is defined on the auxiliary combinatory syntax, before
  interpreting any lambda abstraction. Type closure and naturality use
  only the independent modal-model fields. No proof-theoretic validity
  or canonical-model premise is used.
\<close>

end

end
