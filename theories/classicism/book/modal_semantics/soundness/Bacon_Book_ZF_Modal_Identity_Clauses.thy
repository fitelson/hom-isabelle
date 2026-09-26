theory Bacon_Book_ZF_Modal_Identity_Clauses
  imports Bacon_Book_ZF_Modal_Truth_Clauses
begin

section \<open>Unconditional Boolean clauses, predicate quantification, top, Leibniz identity and the box\<close>

text \<open>
  The Boolean clauses hold without a false-proposition premise: if
  bottom is true at w, every formula is true at w and both sides of
  each biconditional hold. The quantifier clause for an arbitrary
  predicate term is what the UI constructor needs. Leibniz identity
  A =σ B is the closed term λxy.∀z.(zx ↔ zy); its truth at w is
  identity of the two values, with no false-proposition premise,
  using the model's own equality operation (identity_member) as the
  separating predicate (if bottom is true at w the separator forces
  every domain at w to be a singleton, so the clause still holds). The box is the literal λp.(p =ₜ ⊤) of
  book_box_const; its truth is truth of the operand at every future
  world under the moved assignment. None of this uses a proof
  judgment or the soundness being established.
\<close>

context book_ZF_modal_interpretation
begin

subsection \<open>Boolean clauses without a nontriviality premise\<close>

theorem truth_or:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_or G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<or> book_ZF_truth_at J w g B)"
proof (cases "book_ZF_truth_at J w g (book_bottom G)")
  case True
  have both: "book_ZF_truth_at J w g (book_or G A B)" "book_ZF_truth_at J w g A"
    by (rule bottom_true_everything[OF rich ww typed True _ typed]; (rule book_or_language[OF rich al bl] | rule al))+
  show ?thesis using both by blast
next
  case False
  show ?thesis by (rule truth_boolean_binary(1)[OF rich al bl ww typed False])
qed

theorem truth_and:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_and G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<and> book_ZF_truth_at J w g B)"
proof (cases "book_ZF_truth_at J w g (book_bottom G)")
  case True
  have all: "book_ZF_truth_at J w g (book_and G A B)" "book_ZF_truth_at J w g A" "book_ZF_truth_at J w g B"
    by (rule bottom_true_everything[OF rich ww typed True _ typed];
      (rule book_and_language[OF rich al bl] | rule al | rule bl))+
  show ?thesis using all by blast
next
  case False
  show ?thesis by (rule truth_boolean_binary(2)[OF rich al bl ww typed False])
qed

theorem truth_iff:
  assumes rich: "sg_rich G" and al: "book_theory_formula signature G A" and bl: "book_theory_formula signature G B"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_iff G A B) \<longleftrightarrow> (book_ZF_truth_at J w g A \<longleftrightarrow> book_ZF_truth_at J w g B)"
proof (cases "book_ZF_truth_at J w g (book_bottom G)")
  case True
  have all: "book_ZF_truth_at J w g (book_iff G A B)" "book_ZF_truth_at J w g A" "book_ZF_truth_at J w g B"
    by (rule bottom_true_everything[OF rich ww typed True _ typed];
      (rule book_iff_language[OF rich al bl] | rule al | rule bl))+
  show ?thesis using all by blast
next
  case False
  show ?thesis by (rule truth_boolean_binary(3)[OF rich al bl ww typed False])
qed

subsection \<open>Universal quantification over an arbitrary predicate term\<close>

theorem truth_all_predicate:
  assumes fl: "book_in_language book_minimal_logical_type UNIV signature G F (Arr \<sigma> Prop)"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (NApp (NLogical (SBAll \<sigma>)) F) \<longleftrightarrow>
    (\<forall>a\<in>explode (D \<sigma> w). Elem w (app (J w g F) (Opair w a)))"
proof -
  have fm: "J w g F \<in> explode (D (Arr \<sigma> Prop) w)" by (rule denote_type[OF ww fl typed])
  have outer: "J w g (NApp (NLogical (SBAll \<sigma>)) F) = app (J w g (NLogical (SBAll \<sigma>))) (Opair w (J w g F))"
    by (rule denote_application[OF ww book_all_operator_language fl typed])
  have alls: "app (book_ZF_all W R D root \<sigma>) (Opair w (J w g F)) =
    book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D \<sigma> v). Elem v (app (J w g F) (Opair v a)))"
    by (rule book_ZF_all_value, rule root_pair[OF ww fm])
  show ?thesis unfolding book_ZF_truth_at_def
    by (simp only: outer logical_value(2)[OF ww typed] book_ZF_restrict_app[OF current_pair[OF ww fm]] alls
      book_ZF_collect_member iffD1[OF explode_Elem ww] reflexive[OF ww] simp_thms)
qed

subsection \<open>Top\<close>

theorem top_value:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g (book_top G) = book_ZF_future W R w"
proof -
  let ?n = "book_prop_name G"
  have bl: "book_theory_formula signature G (book_bottom G)" by (rule book_bottom_language[OF rich])
  have vl: "book_theory_formula signature G (NVar ?n)" by (rule book_boolean_variables_language(1)[OF rich])
  have body: "book_theory_formula signature G (book_imp (NVar ?n) (book_bottom G))" by (rule book_imp_language[OF vl bl])
  have bt: "book_in_language book_minimal_logical_type UNIV signature G (book_bottom G) (G ?n)"
    using bl by (simp only: book_prop_name_type[OF rich])
  have bm: "J w g (book_bottom G) \<in> explode (D Prop w)" by (rule denote_type[OF ww bl typed])
  let ?h = "g(?n := J w g (book_bottom G))"
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?h"
    by (rule book_env_update[OF typed]; simp only: book_prop_name_type[OF rich]; rule bm)
  have unary: "J w g (book_top G) = J w ?h (book_imp (NVar ?n) (book_bottom G))"
    unfolding book_top_def book_not_def book_not_const_def by (rule unary_abstraction_value[OF body bt ww typed])
  have var: "J w ?h (NVar ?n) = J w g (book_bottom G)" by (simp only: denote_variable[OF ww updated] fun_upd_same)
  have same_bottom: "J w ?h (book_bottom G) = J w g (book_bottom G)"
    by (rule denote_coincidence[OF bl ww updated typed]; simp only: book_bottom_closed; simp)
  have imp: "J w ?h (book_imp (NVar ?n) (book_bottom G)) =
    book_ZF_collect W R w (\<lambda>u. \<not> Elem u (J w g (book_bottom G)) \<or> Elem u (J w g (book_bottom G)))"
    by (simp only: imp_value[OF vl bl ww updated] var same_bottom)
  have trivial: "book_ZF_collect W R w (\<lambda>u. \<not> Elem u (J w g (book_bottom G)) \<or> Elem u (J w g (book_bottom G))) =
    book_ZF_future W R w"
    by (rule iffD2[OF Ext]; intro allI; simp only: book_ZF_collect_member book_ZF_future_member simp_thms)
  show ?thesis by (simp only: unary imp trivial)
qed

theorem truth_top:
  assumes rich: "sg_rich G" and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_top G)"
  unfolding book_ZF_truth_at_def
  by (simp only: top_value[OF rich ww typed] book_ZF_future_member iffD1[OF explode_Elem ww] reflexive[OF ww] simp_thms)

subsection \<open>Leibniz identity as identity of values\<close>

lemma equality_predicate:
  assumes ww: "w \<in> explode W" and am: "a \<in> explode (D \<sigma> w)"
  shows "app (book_ZF_eq W R D i root \<sigma>) (Opair w a) \<in> explode (D (Arr \<sigma> Prop) w)"
    and "\<And>b. b \<in> explode (D \<sigma> w) \<Longrightarrow>
      Elem w (app (app (book_ZF_eq W R D i root \<sigma>) (Opair w a)) (Opair w b)) \<longleftrightarrow> a = b"
proof -
  show "app (book_ZF_eq W R D i root \<sigma>) (Opair w a) \<in> explode (D (Arr \<sigma> Prop) w)"
    by (rule function_type[OF root_world ww root_below[OF ww] identity_member am])
next
  fix b assume bm: "b \<in> explode (D \<sigma> w)"
  have val_eq: "app (app (book_ZF_eq W R D i root \<sigma>) (Opair w a)) (Opair w b) =
    book_ZF_collect W R w (\<lambda>u. i \<sigma> w u a = i \<sigma> w u b)"
    by (rule book_ZF_eq_value, rule root_pair[OF ww am], rule current_pair[OF ww bm])
  show "Elem w (app (app (book_ZF_eq W R D i root \<sigma>) (Opair w a)) (Opair w b)) \<longleftrightarrow> a = b"
    by (simp only: val_eq book_ZF_collect_member iffD1[OF explode_Elem ww] reflexive[OF ww]
      transport_identity[OF ww am] transport_identity[OF ww bm] simp_thms)
qed

lemmas equality_predicate_available = equality_predicate(1)
lemmas equality_predicate_separates = equality_predicate(2)

theorem truth_leibniz:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV signature G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV signature G B \<sigma>"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_leibniz G \<sigma> A B) \<longleftrightarrow> J w g A = J w g B"
proof -
  let ?x = "book_leibniz_x G \<sigma>" and ?y = "book_leibniz_y G \<sigma>" and ?z = "book_leibniz_z G \<sigma>"
  have xt: "G ?x = \<sigma>" and yt: "G ?y = \<sigma>" and zt: "G ?z = Arr \<sigma> Prop" by (rule book_leibniz_name_types[OF rich])+
  have xy: "?x \<noteq> ?y" and xz: "?x \<noteq> ?z" and yz: "?y \<noteq> ?z" by (rule book_leibniz_names_distinct[OF rich])+
  have at: "book_in_language book_minimal_logical_type UNIV signature G A (G ?x)"
    and bt: "book_in_language book_minimal_logical_type UNIV signature G B (G ?y)"
    using al bl by (simp_all only: xt yt)
  have am: "J w g A \<in> explode (D \<sigma> w)" and bm: "J w g B \<in> explode (D \<sigma> w)"
    by (rule denote_type[OF ww al typed], rule denote_type[OF ww bl typed])
  let ?h = "(g(?x := J w g A))(?y := J w g B)"
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?h"
    by (rule book_env_update[OF book_env_update[OF typed]]; simp only: xt yt; (rule am | rule bm))
  have zx: "book_theory_formula signature G (NApp (NVar ?z) (NVar ?x))"
    and zy: "book_theory_formula signature G (NApp (NVar ?z) (NVar ?y))"
    by (rule book_language_App[OF book_leibniz_variables_language(3)[OF rich] book_leibniz_variables_language(1)[OF rich]],
      rule book_language_App[OF book_leibniz_variables_language(3)[OF rich] book_leibniz_variables_language(2)[OF rich]])
  have body: "book_theory_formula signature G (book_leibniz_body G \<sigma>)" by (rule book_leibniz_body_language[OF rich])
  have val_eq: "J w g (book_leibniz G \<sigma> A B) = J w ?h (book_leibniz_body G \<sigma>)"
    unfolding book_leibniz_def book_leibniz_const_def by (rule binary_abstraction_value[OF body at bt ww typed])
  have each: "book_ZF_truth_at J w (?h(?z := Z)) (book_leibniz_matrix G \<sigma>) \<longleftrightarrow>
    (Elem w (app Z (Opair w (J w g A))) \<longleftrightarrow> Elem w (app Z (Opair w (J w g B))))"
    if zm: "Z \<in> explode (D (G ?z) w)" for Z
  proof -
    have kt: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G (?h(?z := Z))" by (rule book_env_update[OF updated zm])
    have vz: "J w (?h(?z := Z)) (NVar ?z) = Z"
      and vx: "J w (?h(?z := Z)) (NVar ?x) = J w g A"
      and vy: "J w (?h(?z := Z)) (NVar ?y) = J w g B"
      by (simp_all only: denote_variable[OF ww kt] fun_upd_apply xy xz yz xz[symmetric] yz[symmetric] xy[symmetric]
        simp_thms if_True if_False)
    have appx: "J w (?h(?z := Z)) (NApp (NVar ?z) (NVar ?x)) = app Z (Opair w (J w g A))"
      and appy: "J w (?h(?z := Z)) (NApp (NVar ?z) (NVar ?y)) = app Z (Opair w (J w g B))"
      by (simp_all only: denote_application[OF ww book_leibniz_variables_language(3)[OF rich]
        book_leibniz_variables_language(1)[OF rich] kt] denote_application[OF ww book_leibniz_variables_language(3)[OF rich]
        book_leibniz_variables_language(2)[OF rich] kt] vz vx vy)
    show ?thesis unfolding book_leibniz_matrix_def
      by (simp only: truth_iff[OF rich zx zy ww kt]; simp only: book_ZF_truth_at_def appx appy)
  qed
  have quantified: "book_ZF_truth_at J w g (book_leibniz G \<sigma> A B) \<longleftrightarrow>
    (\<forall>Z\<in>explode (D (Arr \<sigma> Prop) w). Elem w (app Z (Opair w (J w g A))) \<longleftrightarrow> Elem w (app Z (Opair w (J w g B))))"
    unfolding book_ZF_truth_at_transfer[OF val_eq] book_leibniz_body_def
    by (simp only: truth_all[OF book_leibniz_matrix_language[OF rich] ww updated] zt; rule ball_cong[OF refl];
      rule each; simp only: zt)
  show ?thesis
  proof (simp only: quantified, rule iffI)
    assume agree: "\<forall>Z\<in>explode (D (Arr \<sigma> Prop) w). Elem w (app Z (Opair w (J w g A))) \<longleftrightarrow> Elem w (app Z (Opair w (J w g B)))"
    let ?E = "app (book_ZF_eq W R D i root \<sigma>) (Opair w (J w g A))"
    have em: "?E \<in> explode (D (Arr \<sigma> Prop) w)" by (rule equality_predicate(1)[OF ww am])
    have left: "Elem w (app ?E (Opair w (J w g A)))" by (simp only: equality_predicate(2)[OF ww am am])
    have right: "Elem w (app ?E (Opair w (J w g B)))" using agree em left by blast
    show "J w g A = J w g B" using right by (simp only: equality_predicate(2)[OF ww am bm])
  next
    assume "J w g A = J w g B"
    then show "\<forall>Z\<in>explode (D (Arr \<sigma> Prop) w). Elem w (app Z (Opair w (J w g A))) \<longleftrightarrow> Elem w (app Z (Opair w (J w g B)))"
      by simp
  qed
qed

subsection \<open>The box\<close>

theorem proposition_as_future:
  assumes pl: "book_theory_formula signature G P"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "J w g P = book_ZF_future W R w \<longleftrightarrow>
    (\<forall>v\<in>explode W. R w v \<longrightarrow> book_ZF_truth_at J v (book_ZF_move i G w v g) P)"
proof
  assume equal: "J w g P = book_ZF_future W R w"
  show "\<forall>v\<in>explode W. R w v \<longrightarrow> book_ZF_truth_at J v (book_ZF_move i G w v g) P"
  proof (intro ballI impI)
    fix v assume vw: "v \<in> explode W" and wv: "R w v"
    have member: "Elem v (J w g P)" using vw wv by (simp only: equal book_ZF_future_member explode_Elem)
    show "book_ZF_truth_at J v (book_ZF_move i G w v g) P"
      using member by (simp only: truth_at_future[OF pl ww vw wv typed])
  qed
next
  assume everywhere: "\<forall>v\<in>explode W. R w v \<longrightarrow> book_ZF_truth_at J v (book_ZF_move i G w v g) P"
  show "J w g P = book_ZF_future W R w"
  proof (rule iffD2[OF Ext], intro allI)
    fix v
    show "Elem v (J w g P) = Elem v (book_ZF_future W R w)"
    proof (cases "v \<in> explode W \<and> R w v")
      case True
      then have vw: "v \<in> explode W" and wv: "R w v" by blast+
      have truth: "book_ZF_truth_at J v (book_ZF_move i G w v g) P" using everywhere vw wv by blast
      show ?thesis using vw wv truth
        by (simp only: truth_at_future[OF pl ww vw wv typed, symmetric] book_ZF_future_member explode_Elem simp_thms)
    next
      case False
      have outside: "\<not> Elem v (J w g P)" using proposition_future[OF pl ww typed] False by blast
      have not_future: "\<not> Elem v (book_ZF_future W R w)"
        using False by (simp only: book_ZF_future_member explode_Elem simp_thms)
      show ?thesis using outside not_future by blast
    qed
  qed
qed

theorem truth_box:
  assumes rich: "sg_rich G" and pl: "book_theory_formula signature G P"
    and ww: "w \<in> explode W" and typed: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  shows "book_ZF_truth_at J w g (book_box G P) \<longleftrightarrow>
    (\<forall>v\<in>explode W. R w v \<longrightarrow> book_ZF_truth_at J v (book_ZF_move i G w v g) P)"
proof -
  let ?n = "book_prop_name G"
  have vl: "book_theory_formula signature G (NVar ?n)" by (rule book_boolean_variables_language(1)[OF rich])
  have tl: "book_theory_formula signature G (book_top G)" by (rule book_top_language[OF rich])
  have body: "book_theory_formula signature G (book_leibniz G Prop (NVar ?n) (book_top G))"
    by (rule book_leibniz_language[OF rich vl tl])
  have pt: "book_in_language book_minimal_logical_type UNIV signature G P (G ?n)"
    using pl by (simp only: book_prop_name_type[OF rich])
  have pm: "J w g P \<in> explode (D Prop w)" by (rule denote_type[OF ww pl typed])
  let ?h = "g(?n := J w g P)"
  have updated: "book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G ?h"
    by (rule book_env_update[OF typed]; simp only: book_prop_name_type[OF rich]; rule pm)
  have val_eq: "J w g (book_box G P) = J w ?h (book_leibniz G Prop (NVar ?n) (book_top G))"
    unfolding book_box_def book_box_const_def by (rule unary_abstraction_value[OF body pt ww typed])
  have var: "J w ?h (NVar ?n) = J w g P" by (simp only: denote_variable[OF ww updated] fun_upd_same)
  show ?thesis
    by (simp only: book_ZF_truth_at_transfer[OF val_eq] truth_leibniz[OF rich vl tl ww updated] var
      top_value[OF rich ww updated] proposition_as_future[OF pl ww typed])
qed

end

end
