theory Goodman_Exact_Denotation_Translation
  imports Goodman_Exact_Goodman_Soundness
    "Goodman_Integration_Proof.Goodman_H_Certificate_Interface"
    "Bacon_Book_Environment_Development.Bacon_Book_Minimal_Existential_Truth"
begin

section \<open>Chart assignments and exact evaluation\<close>

lemma gi_exact_chart_assignment_typed:
  assumes chart: "map G ns = \<Gamma>"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_env_typed \<Gamma> (\<lambda>i. g (ns ! i))"
proof (unfold pp_e_env_typed_def, intro allI impI)
  fix i \<sigma>
  assume index_type: "lookup \<Gamma> i = Some \<sigma>"
  have name_type: "G (ns ! i) = \<sigma>"
    by (rule gi_chart_variable[OF chart index_type])
  show "Elem (g (ns ! i)) (pp_e_domain \<sigma>)"
    using gi_exact_assignment_lookup[OF typed, where n="ns ! i"]
    by (simp only: name_type)
qed

lemma gi_exact_chart_update_lookup:
  assumes fresh: "n \<notin> set ns"
    and index_type: "lookup (\<sigma> # map G ns) i = Some \<tau>"
  shows "(g(n := x)) ((n # ns) ! i) = extend_env x (\<lambda>j. g (ns ! j)) i"
proof (cases i)
  case 0
  show ?thesis by (simp only: 0 nth_Cons_0 fun_upd_same extend_env.simps)
next
  case (Suc j)
  have bound: "j < length ns"
    using index_type by (auto simp: Suc lookup_def split: if_splits)
  have member: "ns ! j \<in> set ns" by (rule nth_mem[OF bound])
  have different: "ns ! j \<noteq> n" using member fresh by blast
  show ?thesis by (simp only: Suc nth_Cons_Suc extend_env.simps fun_upd_other[OF different])
qed

context pp_e_constants
begin

lemma gi_exact_eval_agrees_on_context:
  assumes term_type: "\<Gamma> \<turnstile> M : \<tau>"
    and left_type: "pp_e_env_typed \<Gamma> \<rho>"
    and right_type: "pp_e_env_typed \<Gamma> \<eta>"
    and agreement: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> \<rho> n = \<eta> n"
  shows "pp_e_eval C \<rho> M = pp_e_eval C \<eta> M"
proof -
  have pointwise: "pp_e_eqv \<sigma> [] (\<rho> n) (\<eta> n)"
    if index_type: "lookup \<Gamma> n = Some \<sigma>" for n \<sigma>
  proof -
    have member: "Elem (\<rho> n) (pp_e_domain \<sigma>)"
      by (rule pp_e_env_typed_lookup[OF left_type index_type])
    have same: "\<rho> n = \<eta> n" by (rule agreement[OF index_type])
    show ?thesis using pp_e_eqv_reflexive[OF member, where w="[]"]
      by (simp only: same)
  qed
  have related: "pp_e_env_eqv [] \<Gamma> \<rho> \<eta>"
    using left_type right_type pointwise unfolding pp_e_env_eqv_def by blast
  have values_related: "pp_e_eqv \<tau> [] (pp_e_eval C \<rho> M) (pp_e_eval C \<eta> M)"
    by (rule pp_e_eval_respects[OF term_type related])
  have lm: "Elem (pp_e_eval C \<rho> M) (pp_e_domain \<tau>)"
    using pp_e_eval_type[OF term_type left_type] by (simp only: pp_e_dom_def)
  have rm: "Elem (pp_e_eval C \<eta> M) (pp_e_domain \<tau>)"
    using pp_e_eval_type[OF term_type right_type] by (simp only: pp_e_dom_def)
  show ?thesis using values_related
    by (simp only: pp_e_eqv_iff_action_eq[OF lm rm] rev.simps
        pp_b_action_one_all[OF lm] pp_b_action_one_all[OF rm])
qed

lemma gi_exact_chart_body_eval:
  assumes rich: "sg_rich G" and body_type: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and typed: "book_env_typed gi_exact_domain G g"
    and member: "x \<in> gi_exact_domain \<sigma>"
  shows "pp_e_eval C (\<lambda>i. (g(named_chart_fresh G ns \<sigma> := x))
      ((named_chart_fresh G ns \<sigma> # ns) ! i)) A =
    pp_e_eval C (extend_env x (\<lambda>i. g (ns ! i))) A"
proof -
  let ?n = "named_chart_fresh G ns \<sigma>"
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have fresh: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have named_member: "x \<in> gi_exact_domain (G ?n)" using member by (simp only: nt)
  have update_type: "book_env_typed gi_exact_domain G (g(?n := x))"
    by (rule book_env_update[OF typed named_member])
  have extended_chart: "map G (?n # ns) = \<sigma> # \<Gamma>" by (simp only: list.map nt chart)
  have left_type: "pp_e_env_typed (\<sigma> # \<Gamma>) (\<lambda>i. (g(?n := x)) ((?n # ns) ! i))"
    by (rule gi_exact_chart_assignment_typed[OF extended_chart update_type])
  have exact_member: "Elem x (pp_e_domain \<sigma>)" using member by (simp only: gi_exact_domain_member)
  have right_type: "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x (\<lambda>i. g (ns ! i)))"
    by (rule pp_e_env_typed_extend[OF gi_exact_chart_assignment_typed[OF chart typed] exact_member])
  show ?thesis
  proof (rule gi_exact_eval_agrees_on_context[OF body_type left_type right_type])
    fix i \<mu>
    assume index_type: "lookup (\<sigma> # \<Gamma>) i = Some \<mu>"
    have adjusted: "lookup (\<sigma> # map G ns) i = Some \<mu>" using index_type by (simp only: chart)
    show "(g(?n := x)) ((?n # ns) ! i) = extend_env x (\<lambda>i. g (ns ! i)) i"
      by (rule gi_exact_chart_update_lookup[OF fresh adjusted])
  qed
qed

section \<open>Typed translation and proposition-value extensionality\<close>

lemma gi_exact_translation_language:
  assumes rich: "sg_rich G" and term_type: "\<Gamma> \<turnstile> M : \<tau>" and chart: "map G ns = \<Gamma>"
  shows "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G
    (gi_to_book G ns (\<lambda>c \<sigma>. c) M) \<tau>"
  by (rule gi_to_book_language[OF rich term_type chart gi_constants_universal])

lemma gi_exact_translated_member:
  assumes rich: "sg_rich G" and term_type: "\<Gamma> \<turnstile> M : \<tau>"
    and chart: "map G ns = \<Gamma>" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M) \<in> gi_exact_domain \<tau>"
  by (rule gi_exact_named_denote_type[OF gi_exact_translation_language[OF rich term_type chart] typed])

lemma gi_exact_translation_prop_ext:
  assumes rich: "sg_rich G" and term_type: "\<Gamma> \<turnstile> M : Prop"
    and chart: "map G ns = \<Gamma>" and typed: "book_env_typed gi_exact_domain G g"
    and worlds: "\<And>w. pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M)) w =
      pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) M) w"
  shows "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M) =
    pp_e_eval C (\<lambda>i. g (ns ! i)) M"
proof -
  have lm: "Elem (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M)) (pp_e_domain Prop)"
    using gi_exact_translated_member[OF rich term_type chart typed] by (simp only: gi_exact_domain_member)
  have rm: "Elem (pp_e_eval C (\<lambda>i. g (ns ! i)) M) (pp_e_domain Prop)"
    using pp_e_eval_type[OF term_type gi_exact_chart_assignment_typed[OF chart typed]]
    by (simp only: pp_e_dom_def)
  show ?thesis by (rule pp_e_prop_ext[OF lm rm worlds])
qed

lemma gi_exact_named_not_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and term_language: "book_theory_formula \<Sigma> G A"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_not G A)) w =
    (\<not> pp_e_holds (gi_exact_named_denote C G g A) w)"
  using book_full_minimal_model.book_not_truth[
    OF gi_exact_book_minimal_model[OF rich] rich typed term_language]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_and_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and left_language: "book_theory_formula \<Sigma> G A" and right_language: "book_theory_formula \<Sigma> G B"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_and G A B)) w =
    (pp_e_holds (gi_exact_named_denote C G g A) w \<and> pp_e_holds (gi_exact_named_denote C G g B) w)"
  using book_full_minimal_model.book_and_truth[
    OF gi_exact_book_minimal_model[OF rich] rich typed left_language right_language]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_or_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and left_language: "book_theory_formula \<Sigma> G A" and right_language: "book_theory_formula \<Sigma> G B"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_or G A B)) w =
    (pp_e_holds (gi_exact_named_denote C G g A) w \<or> pp_e_holds (gi_exact_named_denote C G g B) w)"
  using book_full_minimal_model.book_or_truth[
    OF gi_exact_book_minimal_model[OF rich] rich typed left_language right_language]
  by (simp only: gi_exact_valuation_def)

lemma gi_exact_named_exists_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and body_language: "book_theory_formula \<Sigma> G A"
  shows "pp_e_holds (gi_exact_named_denote C G g (book_exists G n A)) w =
    (\<exists>x\<in>gi_exact_domain (G n). pp_e_holds (gi_exact_named_denote C G (g(n := x)) A) w)"
  using book_full_minimal_model.book_exists_truth[
    OF gi_exact_book_minimal_model[OF rich] rich typed body_language]
  by (simp only: gi_exact_valuation_def)

section \<open>All-type denotation preservation\<close>

text \<open>
  The induction compares values, not merely truth at a selected world.
  In the proposition cases equality follows from truth agreement at every
  word. In the abstraction case it follows from extensionality of actual
  set-theoretic function graphs in Bacon's restricted arrow carrier.
  A binder changes the chart and the named assignment together; the
  preceding context-agreement theorem handles unused de Bruijn indices.
\<close>

theorem gi_exact_denotation_translation:
  assumes rich: "sg_rich G" and term_type: "\<Gamma> \<turnstile> M : \<tau>"
    and chart: "map G ns = \<Gamma>" and chart_distinct: "distinct ns"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M) =
    pp_e_eval C (\<lambda>i. g (ns ! i)) M"
  using term_type chart chart_distinct typed
proof (induction arbitrary: ns g rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case by (simp only: gi_to_book.simps gi_exact_named_denote_var pp_e_eval.simps)
next
  case (Const \<Gamma> c \<tau>)
  show ?case by (simp only: gi_to_book.simps gi_exact_named_denote_const pp_e_eval.simps)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have left: "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) M) = pp_e_eval C (\<lambda>i. g (ns ! i)) M"
    by (rule App.IH(1)[OF App.prems])
  have right: "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) N) = pp_e_eval C (\<lambda>i. g (ns ! i)) N"
    by (rule App.IH(2)[OF App.prems])
  show ?case by (simp only: gi_to_book.simps gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=\<tau>]
      gi_exact_app_value pp_e_eval.simps left right)
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?body = "gi_to_book G (?n # ns) (\<lambda>c \<sigma>. c) A"
  let ?F = "gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Lam \<sigma> A))"
  let ?H = "pp_e_eval C (\<lambda>i. g (ns ! i)) (Lam \<sigma> A)"
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have new_chart: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Lam.prems(1)])
  have new_distinct: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Lam.prems(2)])
  have body_language: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G ?body \<tau>"
    by (rule gi_exact_translation_language[OF rich Lam.hyps new_chart])
  have lam_type: "\<Gamma> \<turnstile> Lam \<sigma> A : Arr \<sigma> \<tau>" by (rule has_type.Lam[OF Lam.hyps])
  have f_member: "Elem ?F (pp_e_domain (Arr \<sigma> \<tau>))"
    using gi_exact_translated_member[OF rich lam_type Lam.prems(1,3)] by (simp only: gi_exact_domain_member)
  have h_member: "Elem ?H (pp_e_domain (Arr \<sigma> \<tau>))"
    using pp_e_eval_type[OF lam_type gi_exact_chart_assignment_typed[OF Lam.prems(1,3)]]
    by (simp only: pp_e_dom_def)
  show ?case
  proof (rule pp_b_function_ext[OF pp_b_arrow_member_function[OF f_member]
      pp_b_arrow_member_function[OF h_member]])
    fix x
    assume exact_x: "Elem x (pp_e_domain \<sigma>)"
    have xm: "x \<in> gi_exact_domain \<sigma>" using exact_x by (simp only: gi_exact_domain_member)
    have named_member: "x \<in> gi_exact_domain (G ?n)" using xm by (simp only: nt)
    have updated: "book_env_typed gi_exact_domain G (g(?n := x))"
      by (rule book_env_update[OF Lam.prems(3) named_member])
    have native_app: "?F \<acute> x = gi_exact_named_denote C G (g(?n := x)) ?body"
      using gi_exact_named_lambda_application[OF rich body_language Lam.prems(3) named_member]
      by (simp only: gi_to_book.simps Let_def gi_exact_app_value nt)
    have induction_value: "gi_exact_named_denote C G (g(?n := x)) ?body =
        pp_e_eval C (\<lambda>i. (g(?n := x)) ((?n # ns) ! i)) A"
      by (rule Lam.IH[OF new_chart new_distinct updated])
    have chart_value: "pp_e_eval C (\<lambda>i. (g(?n := x)) ((?n # ns) ! i)) A =
        pp_e_eval C (extend_env x (\<lambda>i. g (ns ! i))) A"
      by (rule gi_exact_chart_body_eval[OF rich Lam.hyps Lam.prems(1,3) xm])
    have old_app: "?H \<acute> x = pp_e_eval C (extend_env x (\<lambda>i. g (ns ! i))) A"
      by (simp add: Lambda_app exact_x)
    show "?F \<acute> x = ?H \<acute> x" by (simp only: native_app induction_value chart_value old_app)
  qed
next
  case (Eq \<Gamma> A \<sigma> B)
  have al: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) A) \<sigma>"
    by (rule gi_exact_translation_language[OF rich Eq.hyps(1) Eq.prems(1)])
  have bl: "book_in_language book_minimal_logical_type UNIV (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) B) \<sigma>"
    by (rule gi_exact_translation_language[OF rich Eq.hyps(2) Eq.prems(1)])
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Eq[OF Eq.hyps] Eq.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Eq \<sigma> A B))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Eq \<sigma> A B)) w"
      by (simp only: gi_to_book.simps gi_exact_named_leibniz_holds[OF rich Eq.prems(3) al bl]
          Eq.IH(1)[OF Eq.prems] Eq.IH(2)[OF Eq.prems] pp_e_eval_Eq_holds)
  qed
next
  case (Neg \<Gamma> A)
  have al: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) A)"
    by (rule gi_exact_translation_language[OF rich Neg.hyps Neg.prems(1)])
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Neg[OF Neg.hyps] Neg.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Neg A))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Neg A)) w"
      by (simp only: gi_to_book.simps gi_exact_named_not_holds[OF rich Neg.prems(3) al]
          Neg.IH[OF Neg.prems] pp_e_eval_Neg_holds)
  qed
next
  case (Conj \<Gamma> A B)
  have al: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) A)"
    by (rule gi_exact_translation_language[OF rich Conj.hyps(1) Conj.prems(1)])
  have bl: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) B)"
    by (rule gi_exact_translation_language[OF rich Conj.hyps(2) Conj.prems(1)])
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Conj[OF Conj.hyps] Conj.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Conj A B))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Conj A B)) w"
      by (simp only: gi_to_book.simps gi_exact_named_and_holds[OF rich Conj.prems(3) al bl]
          Conj.IH(1)[OF Conj.prems] Conj.IH(2)[OF Conj.prems] pp_e_eval_Conj_holds)
  qed
next
  case (Disj \<Gamma> A B)
  have al: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) A)"
    by (rule gi_exact_translation_language[OF rich Disj.hyps(1) Disj.prems(1)])
  have bl: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) B)"
    by (rule gi_exact_translation_language[OF rich Disj.hyps(2) Disj.prems(1)])
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Disj[OF Disj.hyps] Disj.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Disj A B))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Disj A B)) w"
      by (simp only: gi_to_book.simps gi_exact_named_or_holds[OF rich Disj.prems(3) al bl]
          Disj.IH(1)[OF Disj.prems] Disj.IH(2)[OF Disj.prems] pp_e_eval_Disj_holds)
  qed
next
  case (Imp \<Gamma> A B)
  have al: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) A)"
    by (rule gi_exact_translation_language[OF rich Imp.hyps(1) Imp.prems(1)])
  have bl: "book_theory_formula (\<lambda>_. UNIV) G (gi_to_book G ns (\<lambda>c \<sigma>. c) B)"
    by (rule gi_exact_translation_language[OF rich Imp.hyps(2) Imp.prems(1)])
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Imp[OF Imp.hyps] Imp.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Imp A B))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Imp A B)) w"
      by (simp only: gi_to_book.simps gi_exact_named_imp_holds[OF rich Imp.prems(3) al bl]
          Imp.IH(1)[OF Imp.prems] Imp.IH(2)[OF Imp.prems] pp_e_eval_Imp_holds)
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?body = "gi_to_book G (?n # ns) (\<lambda>c \<sigma>. c) A"
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have new_chart: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Forall.prems(1)])
  have new_distinct: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Forall.prems(2)])
  have body_language: "book_theory_formula (\<lambda>_. UNIV) G ?body"
    by (rule gi_exact_translation_language[OF rich Forall.hyps new_chart])
  have body_value: "gi_exact_named_denote C G (g(?n := x)) ?body =
      pp_e_eval C (extend_env x (\<lambda>i. g (ns ! i))) A"
    if member: "x \<in> gi_exact_domain \<sigma>" for x
  proof -
    have named_member: "x \<in> gi_exact_domain (G ?n)" using member by (simp only: nt)
    have updated: "book_env_typed gi_exact_domain G (g(?n := x))"
      by (rule book_env_update[OF Forall.prems(3) named_member])
    have induction_value: "gi_exact_named_denote C G (g(?n := x)) ?body =
        pp_e_eval C (\<lambda>i. (g(?n := x)) ((?n # ns) ! i)) A"
      by (rule Forall.IH[OF new_chart new_distinct updated])
    show ?thesis by (rule trans[OF induction_value
      gi_exact_chart_body_eval[OF rich Forall.hyps Forall.prems(1,3) member]])
  qed
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Forall[OF Forall.hyps] Forall.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Forall \<sigma> A))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Forall \<sigma> A)) w"
      by (simp only: gi_to_book.simps Let_def gi_exact_named_all_holds[OF rich Forall.prems(3) body_language]
          nt pp_e_eval_Forall_holds; simp add: body_value gi_exact_domain_def)
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?body = "gi_to_book G (?n # ns) (\<lambda>c \<sigma>. c) A"
  have nt: "G ?n = \<sigma>" by (rule named_chart_fresh_type[OF rich])
  have new_chart: "map G (?n # ns) = \<sigma> # \<Gamma>" by (rule gi_chart_extension[OF rich Exists.prems(1)])
  have new_distinct: "distinct (?n # ns)" by (rule gi_binder_chart_distinct[OF rich Exists.prems(2)])
  have body_language: "book_theory_formula (\<lambda>_. UNIV) G ?body"
    by (rule gi_exact_translation_language[OF rich Exists.hyps new_chart])
  have body_value: "gi_exact_named_denote C G (g(?n := x)) ?body =
      pp_e_eval C (extend_env x (\<lambda>i. g (ns ! i))) A"
    if member: "x \<in> gi_exact_domain \<sigma>" for x
  proof -
    have named_member: "x \<in> gi_exact_domain (G ?n)" using member by (simp only: nt)
    have updated: "book_env_typed gi_exact_domain G (g(?n := x))"
      by (rule book_env_update[OF Exists.prems(3) named_member])
    have induction_value: "gi_exact_named_denote C G (g(?n := x)) ?body =
        pp_e_eval C (\<lambda>i. (g(?n := x)) ((?n # ns) ! i)) A"
      by (rule Exists.IH[OF new_chart new_distinct updated])
    show ?thesis by (rule trans[OF induction_value
      gi_exact_chart_body_eval[OF rich Exists.hyps Exists.prems(1,3) member]])
  qed
  show ?case
  proof (rule gi_exact_translation_prop_ext[OF rich has_type.Exists[OF Exists.hyps] Exists.prems(1,3)])
    fix w
    show "pp_e_holds (gi_exact_named_denote C G g (gi_to_book G ns (\<lambda>c \<sigma>. c) (Exists \<sigma> A))) w =
        pp_e_holds (pp_e_eval C (\<lambda>i. g (ns ! i)) (Exists \<sigma> A)) w"
      by (simp only: gi_to_book.simps Let_def gi_exact_named_exists_holds[OF rich Exists.prems(3) body_language]
          nt pp_e_eval_Exists_holds; simp add: body_value gi_exact_domain_def)
  qed
qed

end

end
