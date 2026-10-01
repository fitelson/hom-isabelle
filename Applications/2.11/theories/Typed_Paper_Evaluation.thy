theory Typed_Paper_Evaluation
  imports Typed_Paper_Interpretation Typed_Paper_Premodel
begin

abbreviation pt_eval where
  "pt_eval G A h g \<equiv> paper_ZF_action_eval pa_Ar Fst Snd pa_compose pa_id paper_D paper_T paper_I G A h g"

theorem pt_eval_agrees:
  assumes interp: "book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T
      (pt_signature S) (pt_I V) G J"
    and logical: "\<And>w l. Elem w raw_W \<Longrightarrow> paper_R_type (paper_logical_type l) \<Longrightarrow>
      paper_enc (paper_logical_type l) w (src_T (paper_logical_type l) raw_root w (V l)) =
      paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
    and typed: "paper_R_has_type G A a" and names: "named_in_signature S A"
    and arrow: "Elem h pa_Ar" and origin: "Fst h = raw_root"
    and bt: "book_env_typed (\<lambda>a. explode (src_D a (Snd h))) G b"
    and agree: "pt_agree G (Snd h) g b" and adequate: "named_adequate g A"
  shows "pt_eval G A h g = Some (paper_enc a (Snd h) (J (Snd h) b (pt_term A)))"
proof -
  interpret J: book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T
    "pt_signature S" "pt_I V" G J by (rule interp)
  show ?thesis using typed names arrow origin bt agree adequate
  proof (induction arbitrary: h g b rule: paper_R_has_type.induct)
    case (Var n)
    have ww: "Snd h \<in> explode raw_W"
      using pa_arrow_data(2)[OF Var.prems(2)] by (simp only: explode_Elem)
    obtain x where gx: "g n = Some x"
      by (rule named_adequate_value[OF Var.prems(6)]) simp
    have xe: "x = paper_enc (G n) (Snd h) (b n)"
      using Var.prems(5) gx by (auto simp only: pt_agree_def)
    show ?case
      by (simp only: paper_ZF_action_eval.simps pt_term.simps gx xe
        J.denote_variable[OF ww Var.prems(4)])
  next
    case (Const a c)
    have we: "Elem (Snd h) raw_W" by (rule pa_arrow_data(2)[OF Const.prems(2)])
    have ww: "Snd h \<in> explode raw_W" using we by (simp only: explode_Elem)
    have ce: "Inl c \<in> pt_signature S a" using Const.prems(1) by simp
    have transport: "paper_T a h (paper_I a c) =
      paper_enc a (Snd h) (src_T a raw_root (Snd h) (src_I c a))"
      by (simp only: paper_T_def paper_I_def Const.prems(3)
        paper_dec_enc[OF raw_worlds(1) src_I_type])
    show ?case
      by (simp only: paper_ZF_action_eval.simps pt_term.simps
        J.denote_constant[OF ww ce Const.prems(4)] pt_I_def sum.case
        transport)
  next
    case (Logical l)
    have we: "Elem (Snd h) raw_W" by (rule pa_arrow_data(2)[OF Logical.prems(2)])
    have ww: "Snd h \<in> explode raw_W" using we by (simp only: explode_Elem)
    have le: "Inr l \<in> pt_signature S (paper_logical_type l)" by simp
    show ?case
      by (simp only: paper_ZF_action_eval.simps pt_term.simps
        J.denote_constant[OF ww le Logical.prems(4)] pt_I_def sum.case
        logical[OF we Logical.hyps])
  next
    case (App F a c A)
    have we: "Elem (Snd h) raw_W" by (rule pa_arrow_data(2)[OF App.prems(2)])
    have ww: "Snd h \<in> explode raw_W" using we by (simp only: explode_Elem)
    have fn: "named_in_signature S F" and an: "named_in_signature S A"
      using App.prems(1) by simp_all
    have fa: "named_adequate g F" and aa: "named_adequate g A"
      using App.prems(6) by (auto simp only: named_adequate_def named_fv.simps)
    have fl: "book_in_language book_minimal_logical_type UNIV (pt_signature S) G (pt_term F) (Arr a c)"
      by (rule pt_R_language) (simp only: paper_R_in_language_def App.hyps(1) fn simp_thms)
    have al: "book_in_language book_minimal_logical_type UNIV (pt_signature S) G (pt_term A) a"
      by (rule pt_R_language) (simp only: paper_R_in_language_def App.hyps(2) an simp_thms)
    let ?f = "J (Snd h) b (pt_term F)"
    let ?x = "J (Snd h) b (pt_term A)"
    have xm: "Elem ?x (src_D a (Snd h))"
      using J.denote_type[OF ww al App.prems(4)] by (simp only: explode_Elem)
    have fe: "pt_eval G F h g = Some (paper_enc (Arr a c) (Snd h) ?f)"
      by (rule App.IH(1)[OF fn App.prems(2,3,4,5) fa])
    have ae: "pt_eval G A h g = Some (paper_enc a (Snd h) ?x)"
      by (rule App.IH(2)[OF an App.prems(2,3,4,5) aa])
    have graph: "isFun (paper_enc (Arr a c) (Snd h) ?f)"
      by (simp only: paper_enc_arrow isFun_Lambda)
    have domain: "Domain (paper_enc (Arr a c) (Snd h) ?f) =
      paper_ZF_pair_code pa_Ar Fst Snd (paper_D a) (Snd h)"
      by (simp only: paper_enc_arrow domain_Lambda)
    have pair: "Elem (Opair (pa_id (Snd h)) (paper_enc a (Snd h) ?x))
      (Domain (paper_enc (Arr a c) (Snd h) ?f))"
      by (simp only: domain pa_id_def pa_pair_member we raw_rel_refl paper_enc_type[OF xm] simp_thms)
    have evaluated: "pt_eval G (NApp F A) h g =
      Some (app (paper_enc (Arr a c) (Snd h) ?f) (Opair (pa_id (Snd h)) (paper_enc a (Snd h) ?x)))"
      by (rule paper_ZF_action_eval_application[OF fe ae graph pair])
    show ?case
      apply (subst evaluated)
      by (simp only: pt_term.simps J.denote_application[OF ww fl al App.prems(4)]
        pa_id_def paper_enc_app[OF we we raw_rel_refl xm])
  next
    case (Lam A a n)
    have we: "Elem (Snd h) raw_W" by (rule pa_arrow_data(2)[OF Lam.prems(2)])
    have ww: "Snd h \<in> explode raw_W" using we by (simp only: explode_Elem)
    have an: "named_in_signature S A" using Lam.prems(1) by simp
    have al: "book_in_language book_minimal_logical_type UNIV (pt_signature S) G (pt_term A) a"
      by (rule pt_R_language) (simp only: paper_R_in_language_def Lam.hyps(1) an simp_thms)
    let ?E = "paper_enc (Arr (G n) a) (Snd h) (J (Snd h) b (pt_term (NLam n A)))"
    have graph: "?E = Lambda (paper_ZF_pair_code pa_Ar Fst Snd (paper_D (G n)) (Snd h)) (app ?E)"
      by (rule paper_enc_graph)
    have body: "paper_ZF_action_abstraction_body pa_compose paper_T G n (pt_eval G A) h g z =
      Some (app ?E z)"
      if zm: "Elem z (paper_ZF_pair_code pa_Ar Fst Snd (paper_D (G n)) (Snd h))" for z
    proof -
      obtain v y where ve: "Elem v raw_W" and wv: "raw_rel (Snd h) v"
        and ym: "Elem y (paper_D (G n) v)" and ze: "z = Opair (Opair (Snd h) v) y"
        using zm by (auto elim: pa_pairE)
      obtain x where xm: "Elem x (src_D (G n) v)" and ye: "y = paper_enc (G n) v x"
        using ym by (auto simp only: paper_D_member)
      let ?i = "Opair (Snd h) v"
      let ?h = "pa_compose ?i h"
      let ?g = "(paper_ZF_action_transport_assignment G paper_T ?i g)(n := Some y)"
      let ?b = "(book_ZF_move src_T G (Snd h) v b)(n := x)"
      have he: "Snd ?h = v" and ho: "Fst ?h = raw_root"
        by (simp_all only: pa_compose_def Fst Snd Lam.prems(3))
      have wr: "raw_rel raw_root (Snd h)"
        using pa_arrow_data(3)[OF Lam.prems(2)] by (simp only: Lam.prems(3))
      have ha: "Elem ?h pa_Ar"
        by (simp only: pa_compose_def Fst Snd Lam.prems(3) pa_arrow_pair
          raw_worlds(1) ve raw_rel_trans[OF wr wv] simp_thms)
      have moved: "book_env_typed (\<lambda>a. explode (src_D a v)) G (book_ZF_move src_T G (Snd h) v b)"
        by (rule pt_book_move_typed[OF we ve wv Lam.prems(4)])
      have bt: "book_env_typed (\<lambda>a. explode (src_D a v)) G ?b"
        by (rule book_env_update[OF moved]) (simp only: explode_Elem xm)
      have ga: "pt_agree G v ?g ?b"
        using pt_agree_update[OF pt_agree_move[OF we Lam.prems(4,5)], where n=n and x=x]
        by (simp only: ye)
      have adequate: "named_adequate ?g A"
        using Lam.prems(6) by (simp only: paper_ZF_action_transport_body_adequate_iff)
      have ih0: "pt_eval G A ?h ?g = Some (paper_enc a (Snd ?h) (J (Snd ?h) ?b (pt_term A)))"
        by (rule Lam.IH[OF an ha ho]) (simp_all only: he bt ga adequate)
      have ih: "pt_eval G A ?h ?g = Some (paper_enc a v (J v ?b (pt_term A)))"
        using ih0 by (simp only: he)
      have vw: "v \<in> explode raw_W" using ve by (simp only: explode_Elem)
      have xs: "x \<in> explode (src_D (G n) v)" using xm by (simp only: explode_Elem)
      have app: "app (J (Snd h) b (NLam n (pt_term A))) (Opair v x) = J v ?b (pt_term A)"
        by (rule J.abstraction_future_application[OF ww al Lam.prems(4) vw wv xs])
      have body_evaluated: "paper_ZF_action_abstraction_body pa_compose paper_T G n
        (pt_eval G A) h g z = Some (paper_enc a v (J v ?b (pt_term A)))"
        by (simp only: ze paper_ZF_action_abstraction_body_pair ih)
      have encoded_application: "app ?E z = paper_enc a v (J v ?b (pt_term A))"
        by (simp only: ze ye paper_enc_app[OF we ve wv xm] pt_term.simps app)
      show ?thesis by (simp only: body_evaluated encoded_application)
    qed
    show ?case
      by (simp only: paper_ZF_action_eval.simps,
        rule pt_abstract_matches[where A=pa_Ar and source=Fst and target=Snd
          and compose=pa_compose and D=paper_D and T=paper_T and G=G and n=n
          and B="pt_eval G A" and h=h and g=g and E="?E", OF graph body])
  qed
qed

theorem pt_totality_from_primitives:
  assumes vm: "\<And>l. Elem (V l) (src_D (paper_logical_type l) raw_root)"
    and logical: "\<And>w l. Elem w raw_W \<Longrightarrow> paper_R_type (paper_logical_type l) \<Longrightarrow>
      paper_enc (paper_logical_type l) w (src_T (paper_logical_type l) raw_root w (V l)) =
      paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
    and language: "paper_R_in_language S G A a"
    and arrow: "Elem h pa_Ar" and origin: "Fst h = raw_root"
    and env: "paper_ZF_action_env_typed paper_D G (Snd h) g"
    and adequate: "named_adequate g A"
  shows "\<exists>v. pt_eval G A h g = Some v \<and> v \<in> explode (paper_D a (Snd h))"
proof -
  obtain J where interp: "book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T
    (pt_signature S) (pt_I V) G J"
    using pt_interpreter_exists[OF vm, where S=S and G=G] by blast
  interpret J: book_ZF_modal_interpretation raw_W raw_rel raw_root src_D src_T
    "pt_signature S" "pt_I V" G J by (rule interp)
  let ?b = "pt_complete G (Snd h) g"
  have bt: "book_env_typed (\<lambda>a. explode (src_D a (Snd h))) G ?b"
    by (rule pt_complete_type[OF env])
  have agree: "pt_agree G (Snd h) g ?b" by (rule pt_complete_agrees[OF env])
  have ty: "paper_R_has_type G A a" and ns: "named_in_signature S A"
    using language by (auto simp only: paper_R_in_language_def)
  have evaluated: "pt_eval G A h g = Some (paper_enc a (Snd h) (J (Snd h) ?b (pt_term A)))"
    by (rule pt_eval_agrees[OF interp logical ty ns arrow origin bt agree adequate])
  have ww: "Snd h \<in> explode raw_W"
    using pa_arrow_data(2)[OF arrow] by (simp only: explode_Elem)
  have member: "Elem (J (Snd h) ?b (pt_term A)) (src_D a (Snd h))"
    using J.denote_type[OF ww pt_R_language[OF language] bt]
    by (simp only: explode_Elem)
  have encoded: "paper_enc a (Snd h) (J (Snd h) ?b (pt_term A)) \<in> explode (paper_D a (Snd h))"
    using paper_enc_type[OF member] by (simp only: explode_Elem)
  show ?thesis by (rule exI, rule conjI[OF evaluated encoded])
qed

theorem pt_action_model_from_primitives:
  assumes rich: "paper_R_rich G"
    and vm: "\<And>l. Elem (V l) (src_D (paper_logical_type l) raw_root)"
    and logical: "\<And>w l. Elem w raw_W \<Longrightarrow> paper_R_type (paper_logical_type l) \<Longrightarrow>
      paper_enc (paper_logical_type l) w (src_T (paper_logical_type l) raw_root w (V l)) =
      paper_ZF_logical_value pa_Ar Fst Snd pa_compose pa_id paper_D paper_T w l"
  shows "paper_ZF_action_model S G (explode raw_W) pa_Ar Fst Snd pa_compose pa_id raw_root
    paper_D paper_T paper_I"
  unfolding paper_ZF_action_model_def
  apply (rule conjI[OF rich])
  apply (rule conjI[OF paper_premodel])
  apply (intro allI impI)
  apply (rule pt_totality_from_primitives[OF vm logical])
  by (assumption | simp only: explode_Elem)+

text \<open>The displayed implication does not assume action-model
  totality, a supplied paper evaluator, or validity of source formulas.
  It reduces the final certificate to membership and exact recoding of
  the concrete six primitive objects. The interpreter used inside the
  proof is obtained from the independently proved generic book theorem;
  the literal partial paper evaluation is then checked by induction,
  including strict definedness at every outgoing abstraction pair.\<close>

end
