theory Bacon_Book_Canonical_Combinator_Syntax
  imports Bacon_Book_Term_Actual_Identity
begin

section \<open>Closed k and s terms for the canonical model\<close>

definition book_canonical_K_x where "book_canonical_K_x G \<sigma> = named_chart_fresh G [] \<sigma>"
definition book_canonical_K_y where "book_canonical_K_y G \<sigma> \<tau> = named_chart_fresh G [book_canonical_K_x G \<sigma>] \<tau>"
definition book_canonical_K where
  "book_canonical_K G \<sigma> \<tau> = NLam (book_canonical_K_x G \<sigma>)
    (NLam (book_canonical_K_y G \<sigma> \<tau>) (NVar (book_canonical_K_x G \<sigma>)))"

lemma book_canonical_K_name_types:
  "sg_rich G \<Longrightarrow> G (book_canonical_K_x G \<sigma>) = \<sigma>"
  "sg_rich G \<Longrightarrow> G (book_canonical_K_y G \<sigma> \<tau>) = \<tau>"
  unfolding book_canonical_K_x_def book_canonical_K_y_def by (rule named_chart_fresh_type; assumption)+

lemma book_canonical_K_names_distinct:
  assumes rich: "sg_rich G"
  shows "book_canonical_K_x G \<sigma> \<noteq> book_canonical_K_y G \<sigma> \<tau>"
proof -
  have "book_canonical_K_y G \<sigma> \<tau> \<notin> set [book_canonical_K_x G \<sigma>]"
    unfolding book_canonical_K_y_def by (rule named_chart_fresh_notin[OF rich])
  then show ?thesis by auto
qed

lemma book_canonical_K_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_canonical_K G \<sigma> \<tau>) (Arr \<sigma> (Arr \<tau> \<sigma>))"
proof -
  have variable: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_canonical_K_x G \<sigma>)) \<sigma>"
    by (simp only: book_language_var_iff book_canonical_K_name_types[OF rich])
  show ?thesis using book_language_Lam[where n="book_canonical_K_x G \<sigma>",
    OF book_language_Lam[where n="book_canonical_K_y G \<sigma> \<tau>", OF variable]]
    by (simp only: book_canonical_K_def book_canonical_K_name_types[OF rich])
qed

lemma book_canonical_K_closed: "named_fv (book_canonical_K G \<sigma> \<tau>) = {}"
  by (auto simp: book_canonical_K_def)

theorem book_canonical_K_closed_terms:
  "sg_rich G \<Longrightarrow> book_canonical_K G \<sigma> \<tau> \<in> book_closed_terms \<Sigma> G (Arr \<sigma> (Arr \<tau> \<sigma>))"
  by (rule book_closed_termsI[OF book_canonical_K_language book_canonical_K_closed]; assumption)

definition book_canonical_S_f where "book_canonical_S_f G \<sigma> \<tau> \<rho> = named_chart_fresh G [] (Arr \<sigma> (Arr \<tau> \<rho>))"
definition book_canonical_S_g where
  "book_canonical_S_g G \<sigma> \<tau> \<rho> = named_chart_fresh G [book_canonical_S_f G \<sigma> \<tau> \<rho>] (Arr \<sigma> \<tau>)"
definition book_canonical_S_x where
  "book_canonical_S_x G \<sigma> \<tau> \<rho> = named_chart_fresh G
    [book_canonical_S_f G \<sigma> \<tau> \<rho>, book_canonical_S_g G \<sigma> \<tau> \<rho>] \<sigma>"
definition book_canonical_S_body where
  "book_canonical_S_body G \<sigma> \<tau> \<rho> =
    NApp (NApp (NVar (book_canonical_S_f G \<sigma> \<tau> \<rho>)) (NVar (book_canonical_S_x G \<sigma> \<tau> \<rho>)))
      (NApp (NVar (book_canonical_S_g G \<sigma> \<tau> \<rho>)) (NVar (book_canonical_S_x G \<sigma> \<tau> \<rho>)))"
definition book_canonical_S where
  "book_canonical_S G \<sigma> \<tau> \<rho> = NLam (book_canonical_S_f G \<sigma> \<tau> \<rho>)
    (NLam (book_canonical_S_g G \<sigma> \<tau> \<rho>) (NLam (book_canonical_S_x G \<sigma> \<tau> \<rho>) (book_canonical_S_body G \<sigma> \<tau> \<rho>)))"

lemma book_canonical_S_name_types:
  "sg_rich G \<Longrightarrow> G (book_canonical_S_f G \<sigma> \<tau> \<rho>) = Arr \<sigma> (Arr \<tau> \<rho>)"
  "sg_rich G \<Longrightarrow> G (book_canonical_S_g G \<sigma> \<tau> \<rho>) = Arr \<sigma> \<tau>"
  "sg_rich G \<Longrightarrow> G (book_canonical_S_x G \<sigma> \<tau> \<rho>) = \<sigma>"
  unfolding book_canonical_S_f_def book_canonical_S_g_def book_canonical_S_x_def
  by (rule named_chart_fresh_type; assumption)+

lemma book_canonical_S_names_distinct:
  assumes rich: "sg_rich G"
  shows "book_canonical_S_f G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_g G \<sigma> \<tau> \<rho>"
    and "book_canonical_S_f G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_x G \<sigma> \<tau> \<rho>"
    and "book_canonical_S_g G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_x G \<sigma> \<tau> \<rho>"
proof -
  have gn: "book_canonical_S_g G \<sigma> \<tau> \<rho> \<notin> set [book_canonical_S_f G \<sigma> \<tau> \<rho>]"
    unfolding book_canonical_S_g_def by (rule named_chart_fresh_notin[OF rich])
  have xn: "book_canonical_S_x G \<sigma> \<tau> \<rho> \<notin>
    set [book_canonical_S_f G \<sigma> \<tau> \<rho>, book_canonical_S_g G \<sigma> \<tau> \<rho>]"
    unfolding book_canonical_S_x_def by (rule named_chart_fresh_notin[OF rich])
  show "book_canonical_S_f G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_g G \<sigma> \<tau> \<rho>"
    and "book_canonical_S_f G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_x G \<sigma> \<tau> \<rho>"
    and "book_canonical_S_g G \<sigma> \<tau> \<rho> \<noteq> book_canonical_S_x G \<sigma> \<tau> \<rho>"
    using gn xn by auto
qed

lemma book_canonical_S_body_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_canonical_S_body G \<sigma> \<tau> \<rho>) \<rho>"
proof -
  have fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_canonical_S_f G \<sigma> \<tau> \<rho>)) (Arr \<sigma> (Arr \<tau> \<rho>))"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  have gl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_canonical_S_g G \<sigma> \<tau> \<rho>)) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  have xl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (book_canonical_S_x G \<sigma> \<tau> \<rho>)) \<sigma>"
    by (simp only: book_language_var_iff book_canonical_S_name_types[OF rich])
  show ?thesis unfolding book_canonical_S_body_def
    by (rule book_language_App[OF book_language_App[OF fl xl] book_language_App[OF gl xl]])
qed

lemma book_canonical_S_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (book_canonical_S G \<sigma> \<tau> \<rho>)
    (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>)))"
  using book_language_Lam[where n="book_canonical_S_f G \<sigma> \<tau> \<rho>",
    OF book_language_Lam[where n="book_canonical_S_g G \<sigma> \<tau> \<rho>",
      OF book_language_Lam[where n="book_canonical_S_x G \<sigma> \<tau> \<rho>", OF book_canonical_S_body_language[OF rich]]]]
  by (simp only: book_canonical_S_def book_canonical_S_name_types[OF rich])

lemma book_canonical_S_closed: "named_fv (book_canonical_S G \<sigma> \<tau> \<rho>) = {}"
  by (auto simp: book_canonical_S_def book_canonical_S_body_def)

theorem book_canonical_S_closed_terms:
  "sg_rich G \<Longrightarrow> book_canonical_S G \<sigma> \<tau> \<rho> \<in> book_closed_terms \<Sigma> G
    (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>)))"
  by (rule book_closed_termsI[OF book_canonical_S_language book_canonical_S_closed]; assumption)

text \<open>
  These are the ordinary closed terms λx.λy.x and λf.λg.λx.fx(gx),
  with distinctly chosen names of the required full types. They are
  the canonical witnesses used in Proposition 18.5. This syntax
  does not assume membership of either combinator in a modal domain;
  that follows by applying the actual closed-term representation.
\<close>

end
