theory Bacon_Book_ZF_Modal_Truth_Clauses
  imports
    Bacon_Book_ZF_Modal_Naturality
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Theory_Consistency
begin

section \<open>Truth of the primitive and defined connectives at an arbitrary world\<close>

text \<open>
  The logical constants are interpreted at a world w as the counterparts
  of the root operations of Definition 18.1, which are their future
  restrictions (Definitions 17.9–17.13). The implication operation is
  the repository's documented future-restricted form of the printed
  W-complement clause; see the model and operation files and
  docs/MODAL_NONTRIVIALITY.md. The derived membership clauses at the
  evaluation world itself agree with Proposition 18.2. Applying them at the pair (w,·) therefore recovers the
  root clauses at w itself. The defined Boolean operators, Leibniz
  identity and the box are literal closed abstractions of the minimal
  language; their truth is computed through the abstraction clause.
  Bottom is ∀p.p, so in the broad structural class it may be true at
  a world; the clauses below keep that case visible instead of
  assuming a false proposition.
\<close>

lemma book_ZF_restrict_app:
  assumes member: "Elem p (book_ZF_pairs W R A v)"
  shows "app (book_ZF_restrict W R A v F) p = app F p"
  unfolding book_ZF_restrict_def by (rule Lambda_app[OF member])

context book_ZF_modal_interpretation
begin

lemma book_ZF_truth_at_transfer:
  assumes equal: "J w g A = J w h B"
  shows "book_ZF_truth_at J w g A \<longleftrightarrow> book_ZF_truth_at J w h B"
  unfolding book_ZF_truth_at_def by (simp only: equal)

lemma current_pair:
  assumes ww: "w \<in> explode W" and am: "a \<in> explode (D \<sigma> w)"
  shows "Elem (Opair w a) (book_ZF_pairs W R (D \<sigma>) w)"
  using ww am reflexive[OF ww] by (simp only: book_ZF_pairs_member explode_Elem)

lemma root_pair:
  assumes ww: "w \<in> explode W" and am: "a \<in> explode (D \<sigma> w)"
  shows "Elem (Opair w a) (book_ZF_pairs W R (D \<sigma>) root)"
  using ww am root_below[OF ww] by (simp only: book_ZF_pairs_member explode_Elem)

lemma logical_value:
  assumes ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (NLogical SImp) = book_ZF_restrict W R (D Prop) w (book_ZF_if_future W R D i root)"
    and "J w g (NLogical (SBAll \<sigma>)) = book_ZF_restrict W R (D (Arr \<sigma> Prop)) w (book_ZF_all W R D root \<sigma>)"
  by (simp_all only: denote_logical[OF ww typed] book_ZF_logical_root.simps book_minimal_logical_type.simps
    function_restriction[OF root_world ww root_below[OF ww] implication_member]
    function_restriction[OF root_world ww root_below[OF ww] universal_member])

subsection \<open>Implication\<close>

theorem imp_value:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (book_imp A B) = book_ZF_collect W R w (\<lambda>u. \<not> Elem u (J w g A) \<or> Elem u (J w g B))"
proof -
  have am: "J w g A \<in> explode (D Prop w)" and bm: "J w g B \<in> explode (D Prop w)"
    by (rule denote_type[OF ww al typed], rule denote_type[OF ww bl typed])
  have head: "book_in_language book_minimal_logical_type UNIV signature G (NApp (NLogical SImp) A) (Arr Prop Prop)"
    by (rule book_language_App[OF book_imp_operator_language al])
  have outer: "J w g (book_imp A B) = app (app (J w g (NLogical SImp)) (Opair w (J w g A))) (Opair w (J w g B))"
    unfolding book_imp_def
    by (simp only: denote_application[OF ww head bl typed] denote_application[OF ww book_imp_operator_language al typed])
  have first: "app (J w g (NLogical SImp)) (Opair w (J w g A)) = app (book_ZF_if_future W R D i root) (Opair w (J w g A))"
    by (simp only: logical_value(1)[OF ww typed] book_ZF_restrict_app[OF current_pair[OF ww am]])
  have val_eq: "app (app (book_ZF_if_future W R D i root) (Opair w (J w g A))) (Opair w (J w g B)) =
    book_ZF_collect W R w (\<lambda>u. \<not> Elem u (i Prop w w (J w g A)) \<or> Elem u (J w g B))"
    by (rule book_ZF_if_future_value, rule root_pair[OF ww am], rule current_pair[OF ww bm])
  show ?thesis by (simp only: outer first val_eq transport_identity[OF ww am])
qed

theorem truth_imp:
  assumes al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_imp A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<longrightarrow> book_ZF_truth_at J w g B)"
  unfolding book_ZF_truth_at_def
  by (simp only: imp_value[OF al bl ww typed] book_ZF_collect_member iffD1[OF explode_Elem ww] reflexive[OF ww]
    simp_thms; blast)

subsection \<open>Universal quantification\<close>

theorem all_value:
  assumes al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (book_all G n A) = book_ZF_collect W R w
    (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (J v ((book_ZF_move i G w v g)(n := a)) A))"
proof -
  have lam: "book_in_language book_minimal_logical_type UNIV signature G (NLam n A) (Arr (G n) Prop)"
    by (rule book_language_Lam[OF al])
  have lm: "J w g (NLam n A) \<in> explode (D (Arr (G n) Prop) w)" by (rule denote_type[OF ww lam typed])
  have outer: "J w g (book_all G n A) = app (J w g (NLogical (SBAll (G n)))) (Opair w (J w g (NLam n A)))"
    unfolding book_all_def by (rule denote_application[OF ww book_all_operator_language lam typed])
  have val_eq: "app (J w g (NLogical (SBAll (G n)))) (Opair w (J w g (NLam n A))) =
    book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (app (J w g (NLam n A)) (Opair v a)))"
  proof -
    have alls: "app (book_ZF_all W R D root (G n)) (Opair w (J w g (NLam n A))) =
      book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (app (J w g (NLam n A)) (Opair v a)))"
      by (rule book_ZF_all_value, rule root_pair[OF ww lm])
    show ?thesis by (simp only: logical_value(2)[OF ww typed] book_ZF_restrict_app[OF current_pair[OF ww lm]] alls)
  qed
  have future: "app (J w g (NLam n A)) (Opair v a) = J v ((book_ZF_move i G w v g)(n := a)) A"
    if vw: "v \<in> explode W" and access: "R w v" and am: "a \<in> explode (D (G n) v)" for v a
    by (rule abstraction_future_application[OF ww al typed vw access am])
  have same: "book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (app (J w g (NLam n A)) (Opair v a))) =
    book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (J v ((book_ZF_move i G w v g)(n := a)) A))"
  proof (rule iffD2[OF Ext], intro allI)
    fix v
    have inner: "(\<forall>a\<in>explode (D (G n) v). Elem v (app (J w g (NLam n A)) (Opair v a))) =
      (\<forall>a\<in>explode (D (G n) v). Elem v (J v ((book_ZF_move i G w v g)(n := a)) A))"
      if vw: "v \<in> explode W" and wv: "R w v"
      by (rule ball_cong[OF refl]; simp only: future[OF vw wv])
    show "Elem v (book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (app (J w g (NLam n A)) (Opair v a)))) =
      Elem v (book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D (G n) v). Elem v (J v ((book_ZF_move i G w v g)(n := a)) A)))"
      by (simp only: book_ZF_collect_member; cases "Elem v W \<and> R w v"; auto simp only: inner explode_Elem)
  qed
  show ?thesis by (simp only: outer val_eq same)
qed

theorem truth_all:
  assumes al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_all G n A) \<longleftrightarrow>
    (\<forall>a\<in>explode (D (G n) w). book_ZF_truth_at J w (g(n := a)) A)"
  unfolding book_ZF_truth_at_def
  by (simp only: all_value[OF al ww typed] book_ZF_collect_member iffD1[OF explode_Elem ww] reflexive[OF ww]
    move_identity[OF ww typed] simp_thms)

subsection \<open>Abstractions applied to arguments at the current world\<close>

theorem unary_abstraction_value:
  assumes body: "book_in_language book_minimal_logical_type UNIV signature G Body \<tau>"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A (G p)"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (NApp (NLam p Body) A) = J w (g(p := J w g A)) Body"
proof -
  have am: "J w g A \<in> explode (D (G p) w)" by (rule denote_type[OF ww al typed])
  show ?thesis
    by (simp only: denote_application[OF ww book_language_Lam[OF body] al typed]
      abstraction_future_application[OF ww body typed ww reflexive[OF ww] am] move_identity[OF ww typed])
qed

theorem binary_abstraction_value:
  assumes body: "book_in_language book_minimal_logical_type UNIV signature G Body \<tau>"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A (G p)"
    and bl: "book_in_language book_minimal_logical_type UNIV signature G B (G q)"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (NApp (NApp (NLam p (NLam q Body)) A) B) = J w ((g(p := J w g A))(q := J w g B)) Body"
proof -
  have am: "J w g A \<in> explode (D (G p) w)" by (rule denote_type[OF ww al typed])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(p := J w g A))" by (rule book_env_update[OF typed am])
  have inner: "book_in_language book_minimal_logical_type UNIV signature G (NLam q Body) (Arr (G q) \<tau>)"
    by (rule book_language_Lam[OF body])
  have head: "J w g (NApp (NLam p (NLam q Body)) A) = J w (g(p := J w g A)) (NLam q Body)"
    by (rule unary_abstraction_value[OF inner al ww typed])
  have bm: "J w g B \<in> explode (D (G q) w)" by (rule denote_type[OF ww bl typed])
  have applied: "J w g (NApp (NApp (NLam p (NLam q Body)) A) B) =
    app (J w g (NApp (NLam p (NLam q Body)) A)) (Opair w (J w g B))"
    by (rule denote_application[OF ww book_language_App[OF book_language_Lam[OF inner] al] bl typed])
  show ?thesis
    by (simp only: applied head abstraction_future_application[OF ww body updated ww reflexive[OF ww] bm]
      move_identity[OF ww updated])
qed

subsection \<open>Bottom, negation and the Boolean operators\<close>

theorem truth_bottom:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_bottom G) \<longleftrightarrow> (\<forall>p\<in>explode (D Prop w). Elem w p)"
proof -
  let ?n = "book_prop_name G"
  have vl: "book_theory_formula signature G (NVar ?n)" by (rule book_boolean_variables_language(1)[OF rich])
  have each: "book_ZF_truth_at J w (g(?n := a)) (NVar ?n) \<longleftrightarrow> Elem w a"
    if am: "a \<in> explode (D Prop w)" for a
  proof -
    have at: "a \<in> explode (D (G ?n) w)" using am by (simp only: book_prop_name_type[OF rich])
    show ?thesis unfolding book_ZF_truth_at_def
      by (simp only: denote_variable[OF ww book_env_update[OF typed at]] fun_upd_same)
  qed
  show ?thesis
    by (simp only: book_bottom_as_all[OF rich] truth_all[OF vl ww typed] book_prop_name_type[OF rich];
      rule ball_cong[OF refl]; rule each; assumption)
qed

theorem bottom_true_everything:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and absurd: "book_ZF_truth_at J w g (book_bottom G)"
    and pl: "book_theory_formula signature G P" and typed_h: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
  shows "book_ZF_truth_at J w h P"
  unfolding book_ZF_truth_at_def
  using absurd[unfolded truth_bottom[OF rich ww typed]] denote_type[OF ww pl typed_h] by blast

theorem bottom_independent:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W"
    and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g" and typed_h: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G h"
  shows "book_ZF_truth_at J w g (book_bottom G) \<longleftrightarrow> book_ZF_truth_at J w h (book_bottom G)"
  by (simp only: truth_bottom[OF rich ww typed] truth_bottom[OF rich ww typed_h])

theorem truth_not:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_not G A) \<longleftrightarrow>
    (book_ZF_truth_at J w g A \<longrightarrow> book_ZF_truth_at J w g (book_bottom G))"
proof -
  let ?n = "book_prop_name G"
  have vl: "book_theory_formula signature G (NVar ?n)" by (rule book_boolean_variables_language(1)[OF rich])
  have bl: "book_theory_formula signature G (book_bottom G)" by (rule book_bottom_language[OF rich])
  have body: "book_theory_formula signature G (book_imp (NVar ?n) (book_bottom G))" by (rule book_imp_language[OF vl bl])
  have at: "book_in_language book_minimal_logical_type UNIV signature G A (G ?n)"
    using al by (simp only: book_prop_name_type[OF rich])
  have am: "J w g A \<in> explode (D Prop w)" by (rule denote_type[OF ww al typed])
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (g(?n := J w g A))"
    by (rule book_env_update[OF typed]; simp only: book_prop_name_type[OF rich]; rule am)
  have val_eq: "J w g (book_not G A) = J w (g(?n := J w g A)) (book_imp (NVar ?n) (book_bottom G))"
    unfolding book_not_def book_not_const_def by (rule unary_abstraction_value[OF body at ww typed])
  have variable: "book_ZF_truth_at J w (g(?n := J w g A)) (NVar ?n) \<longleftrightarrow> book_ZF_truth_at J w g A"
    unfolding book_ZF_truth_at_def by (simp only: denote_variable[OF ww updated] fun_upd_same)
  show ?thesis
    by (simp only: book_ZF_truth_at_transfer[OF val_eq] truth_imp[OF vl bl ww updated] variable
      bottom_independent[OF rich ww updated typed])
qed

theorem truth_not_classical:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and nontrivial: "\<not> book_ZF_truth_at J w g (book_bottom G)"
  shows "book_ZF_truth_at J w g (book_not G A) \<longleftrightarrow> \<not> book_ZF_truth_at J w g A"
  unfolding truth_not[OF rich al ww typed] using nontrivial by blast

theorem truth_boolean_binary:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
    and nontrivial: "\<not> book_ZF_truth_at J w g (book_bottom G)"
  shows "book_ZF_truth_at J w g (book_or G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<or> book_ZF_truth_at J w g B)"
    and "book_ZF_truth_at J w g (book_and G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<and> book_ZF_truth_at J w g B)"
    and "book_ZF_truth_at J w g (book_iff G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<longleftrightarrow> book_ZF_truth_at J w g B)"
proof -
  let ?p = "book_prop_name G" and ?q = "book_second_prop_name G"
  have pv: "book_theory_formula signature G (NVar ?p)" and qv: "book_theory_formula signature G (NVar ?q)"
    by (rule book_boolean_variables_language[OF rich])+
  have at: "book_in_language book_minimal_logical_type UNIV signature G A (G ?p)"
    and bt: "book_in_language book_minimal_logical_type UNIV signature G B (G ?q)"
    using al bl by (simp_all only: book_prop_name_type[OF rich] book_second_prop_name_type[OF rich])
  have am: "J w g A \<in> explode (D Prop w)" and bm: "J w g B \<in> explode (D Prop w)"
    by (rule denote_type[OF ww al typed], rule denote_type[OF ww bl typed])
  let ?h = "(g(?p := J w g A))(?q := J w g B)"
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?h"
    by (rule book_env_update[OF book_env_update[OF typed]];
      simp only: book_prop_name_type[OF rich] book_second_prop_name_type[OF rich]; (rule am | rule bm))
  have distinct: "?p \<noteq> ?q" by (rule book_boolean_names_distinct[OF rich])
  have tp: "book_ZF_truth_at J w ?h (NVar ?p) \<longleftrightarrow> book_ZF_truth_at J w g A"
    and tq: "book_ZF_truth_at J w ?h (NVar ?q) \<longleftrightarrow> book_ZF_truth_at J w g B"
    unfolding book_ZF_truth_at_def
    by (simp_all only: denote_variable[OF ww updated] fun_upd_apply distinct distinct[symmetric] simp_thms if_True if_False)
  have nb: "\<not> book_ZF_truth_at J w ?h (book_bottom G)"
    using nontrivial by (simp only: bottom_independent[OF rich ww updated typed] simp_thms)
  have npl: "book_theory_formula signature G (book_not G (NVar ?p))"
    and nql: "book_theory_formula signature G (book_not G (NVar ?q))"
    by (rule book_not_language[OF rich pv], rule book_not_language[OF rich qv])
  show "book_ZF_truth_at J w g (book_or G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<or> book_ZF_truth_at J w g B)"
    unfolding book_or_def book_or_const_def
    by (simp only: book_ZF_truth_at_transfer[OF binary_abstraction_value[OF book_imp_language[OF npl qv] at bt ww typed]]
      truth_imp[OF npl qv ww updated] truth_not_classical[OF rich pv ww updated nb] tp tq; blast)
  show "book_ZF_truth_at J w g (book_and G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<and> book_ZF_truth_at J w g B)"
    unfolding book_and_def book_and_const_def
    by (simp only: book_ZF_truth_at_transfer[OF binary_abstraction_value[OF book_not_language[OF rich book_imp_language[OF pv nql]] at bt ww typed]]
      truth_not_classical[OF rich book_imp_language[OF pv nql] ww updated nb] truth_imp[OF pv nql ww updated]
      truth_not_classical[OF rich qv ww updated nb] tp tq; blast)
  have il: "book_theory_formula signature G (book_imp (NVar ?p) (NVar ?q))"
    and jl: "book_theory_formula signature G (book_imp (NVar ?q) (NVar ?p))"
    by (rule book_imp_language[OF pv qv], rule book_imp_language[OF qv pv])
  have conj: "book_ZF_truth_at J w ?h (book_and G (book_imp (NVar ?p) (NVar ?q)) (book_imp (NVar ?q) (NVar ?p))) \<longleftrightarrow>
    ((book_ZF_truth_at J w g A \<longrightarrow> book_ZF_truth_at J w g B) \<and> (book_ZF_truth_at J w g B \<longrightarrow> book_ZF_truth_at J w g A))"
  proof -
    let ?k = "(?h(?p := J w ?h (book_imp (NVar ?p) (NVar ?q))))(?q := J w ?h (book_imp (NVar ?q) (NVar ?p)))"
    have im: "J w ?h (book_imp (NVar ?p) (NVar ?q)) \<in> explode (D Prop w)"
      and jm: "J w ?h (book_imp (NVar ?q) (NVar ?p)) \<in> explode (D Prop w)"
      by (rule denote_type[OF ww il updated], rule denote_type[OF ww jl updated])
    have it: "book_in_language book_minimal_logical_type UNIV signature G (book_imp (NVar ?p) (NVar ?q)) (G ?p)"
      and jt: "book_in_language book_minimal_logical_type UNIV signature G (book_imp (NVar ?q) (NVar ?p)) (G ?q)"
      using il jl by (simp_all only: book_prop_name_type[OF rich] book_second_prop_name_type[OF rich])
    have kt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?k"
      by (rule book_env_update[OF book_env_update[OF updated]];
        simp only: book_prop_name_type[OF rich] book_second_prop_name_type[OF rich]; (rule im | rule jm))
    have nk: "\<not> book_ZF_truth_at J w ?k (book_bottom G)"
      using nontrivial by (simp only: bottom_independent[OF rich ww kt typed] simp_thms)
    have kp: "book_ZF_truth_at J w ?k (NVar ?p) \<longleftrightarrow> book_ZF_truth_at J w ?h (book_imp (NVar ?p) (NVar ?q))"
      and kq: "book_ZF_truth_at J w ?k (NVar ?q) \<longleftrightarrow> book_ZF_truth_at J w ?h (book_imp (NVar ?q) (NVar ?p))"
      unfolding book_ZF_truth_at_def
      by (simp_all only: denote_variable[OF ww kt] fun_upd_apply distinct distinct[symmetric] simp_thms if_True if_False)
    show ?thesis
      unfolding book_and_def book_and_const_def
      by (simp only: book_ZF_truth_at_transfer[OF binary_abstraction_value[OF book_not_language[OF rich book_imp_language[OF pv nql]] it jt ww updated]]
        truth_not_classical[OF rich book_imp_language[OF pv nql] ww kt nk] truth_imp[OF pv nql ww kt]
        truth_not_classical[OF rich qv ww kt nk] kp kq truth_imp[OF pv qv ww updated] truth_imp[OF qv pv ww updated] tp tq; blast)
  qed
  show "book_ZF_truth_at J w g (book_iff G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<longleftrightarrow> book_ZF_truth_at J w g B)"
    unfolding book_iff_def book_iff_const_def
    by (simp only: book_ZF_truth_at_transfer[OF binary_abstraction_value[OF book_and_language[OF rich il jl] at bt ww typed]] conj; blast)
qed

end

end
