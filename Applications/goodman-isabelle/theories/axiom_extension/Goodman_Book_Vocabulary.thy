theory Goodman_Book_Vocabulary
  imports Goodman_Book_Axiom_Extension "HOL-Library.Countable_Set"
begin

section \<open>Pure and Fun in the book's minimal language\<close>

text \<open>
  The only nonlogical names are Pure and Fun, each declared at σ→t.
  They are ordinary object-language constants. No HOL purity predicate,
  full function space, or interpretation of the constants is assumed.
  Logical operations and Leibniz identity are the book's own terms.
\<close>

datatype goodman_constant = PureName | FunName
type_synonym gb_term = "goodman_constant book_named_term"

definition gb_signature :: "goodman_constant ssignature" where
  "gb_signature \<tau> = (if \<exists>\<sigma>. \<tau> = Arr \<sigma> Prop then {PureName, FunName} else {})"

definition gb_Pure :: "otype \<Rightarrow> gb_term" where
  "gb_Pure \<sigma> = NConst PureName (Arr \<sigma> Prop)"
definition gb_Fun :: "otype \<Rightarrow> gb_term" where
  "gb_Fun \<sigma> = NConst FunName (Arr \<sigma> Prop)"
definition gb_pure :: "otype \<Rightarrow> gb_term \<Rightarrow> gb_term" where
  "gb_pure \<sigma> A = NApp (gb_Pure \<sigma>) A"
definition gb_fun :: "otype \<Rightarrow> gb_term \<Rightarrow> gb_term" where
  "gb_fun \<sigma> A = NApp (gb_Fun \<sigma>) A"

abbreviation gb_unary where "gb_unary \<equiv> Arr Prop Prop"

lemma gb_signature_countable: "countable (gb_signature \<sigma>)"
  by (simp add: gb_signature_def)

lemma gb_Pure_language:
  "book_in_language book_minimal_logical_type UNIV gb_signature G (gb_Pure \<sigma>) (Arr \<sigma> Prop)"
  by (simp add: gb_Pure_def book_language_const_iff gb_signature_def)
lemma gb_Fun_language:
  "book_in_language book_minimal_logical_type UNIV gb_signature G (gb_Fun \<sigma>) (Arr \<sigma> Prop)"
  by (simp add: gb_Fun_def book_language_const_iff gb_signature_def)
lemma gb_pure_language:
  "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma> \<Longrightarrow>
    book_theory_formula gb_signature G (gb_pure \<sigma> A)"
  unfolding gb_pure_def by (rule book_language_App[OF gb_Pure_language]; assumption)
lemma gb_fun_language:
  "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma> \<Longrightarrow>
    book_theory_formula gb_signature G (gb_fun \<sigma> A)"
  unfolding gb_fun_def by (rule book_language_App[OF gb_Fun_language]; assumption)

lemma gb_Pure_closed[simp]: "named_fv (gb_Pure \<sigma>) = {}"
  by (simp add: gb_Pure_def)
lemma gb_Fun_closed[simp]: "named_fv (gb_Fun \<sigma>) = {}"
  by (simp add: gb_Fun_def)
lemma gb_pure_fv[simp]: "named_fv (gb_pure \<sigma> A) = named_fv A"
  by (simp add: gb_pure_def)
lemma gb_fun_fv[simp]: "named_fv (gb_fun \<sigma> A) = named_fv A"
  by (simp add: gb_fun_def)

section \<open>Distinct typed binders\<close>

definition gb_x where "gb_x G \<sigma> = named_chart_fresh G [] \<sigma>"
definition gb_y where "gb_y G \<sigma> \<tau> = named_chart_fresh G [gb_x G \<sigma>] \<tau>"
definition gb_z where "gb_z G \<sigma> \<tau> \<upsilon> = named_chart_fresh G [gb_x G \<sigma>, gb_y G \<sigma> \<tau>] \<upsilon>"

lemma gb_names_type:
  assumes rich: "sg_rich G"
  shows "G (gb_x G \<sigma>) = \<sigma>"
    and "G (gb_y G \<sigma> \<tau>) = \<tau>"
    and "G (gb_z G \<sigma> \<tau> \<upsilon>) = \<upsilon>"
  unfolding gb_x_def gb_y_def gb_z_def by (rule named_chart_fresh_type[OF rich])+

lemma gb_names_distinct:
  assumes rich: "sg_rich G"
  shows "distinct [gb_x G \<sigma>, gb_y G \<sigma> \<tau>, gb_z G \<sigma> \<tau> \<upsilon>]"
  using named_chart_fresh_notin[OF rich, where ns="[gb_x G \<sigma>]" and \<sigma>=\<tau>]
    named_chart_fresh_notin[OF rich, where ns="[gb_x G \<sigma>, gb_y G \<sigma> \<tau>]" and \<sigma>=\<upsilon>]
  unfolding gb_y_def[symmetric] gb_z_def[symmetric] by auto

lemma gb_x_language:
  "sg_rich G \<Longrightarrow> book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (gb_x G \<sigma>)) \<sigma>"
  by (simp only: book_language_var_iff; rule gb_names_type(1)[symmetric]; assumption)
lemma gb_y_language:
  "sg_rich G \<Longrightarrow> book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (gb_y G \<sigma> \<tau>)) \<tau>"
  by (simp only: book_language_var_iff; rule gb_names_type(2)[symmetric]; assumption)
lemma gb_z_language:
  "sg_rich G \<Longrightarrow> book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar (gb_z G \<sigma> \<tau> \<upsilon>)) \<upsilon>"
  by (simp only: book_language_var_iff; rule gb_names_type(3)[symmetric]; assumption)

section \<open>Purity, application, and unique fundamentality\<close>

definition gb_purity_of_pure where "gb_purity_of_pure \<sigma> = gb_pure (Arr \<sigma> Prop) (gb_Pure \<sigma>)"
definition gb_purity_of_fun where "gb_purity_of_fun \<sigma> = gb_pure (Arr \<sigma> Prop) (gb_Fun \<sigma>)"
definition gb_target_PP where "gb_target_PP = gb_purity_of_pure gb_unary"

definition gb_application_closure where
  "gb_application_closure G \<sigma> \<tau> =
    book_all G (gb_x G (Arr \<sigma> \<tau>)) (book_all G (gb_y G (Arr \<sigma> \<tau>) \<sigma>)
      (book_imp (book_and G
        (gb_pure (Arr \<sigma> \<tau>) (NVar (gb_x G (Arr \<sigma> \<tau>))))
        (gb_pure \<sigma> (NVar (gb_y G (Arr \<sigma> \<tau>) \<sigma>))))
        (gb_pure \<tau> (NApp (NVar (gb_x G (Arr \<sigma> \<tau>))) (NVar (gb_y G (Arr \<sigma> \<tau>) \<sigma>))))))"

definition gb_persistence where
  "gb_persistence G \<sigma> = book_all G (gb_x G \<sigma>)
    (book_imp (gb_pure \<sigma> (NVar (gb_x G \<sigma>)))
      (book_box G (gb_pure \<sigma> (NVar (gb_x G \<sigma>)))))"

definition gb_unique_fundamental where
  "gb_unique_fundamental G \<sigma> =
    book_exists G (gb_x G \<sigma>) (book_and G
      (gb_fun \<sigma> (NVar (gb_x G \<sigma>)))
      (book_all G (gb_y G \<sigma> \<sigma>) (book_imp
        (gb_fun \<sigma> (NVar (gb_y G \<sigma> \<sigma>)))
        (book_leibniz G \<sigma> (NVar (gb_y G \<sigma> \<sigma>)) (NVar (gb_x G \<sigma>))))))"

definition gb_no_fundamentals where
  "gb_no_fundamentals G \<sigma> = book_all G (gb_x G \<sigma>) (book_not G (gb_fun \<sigma> (NVar (gb_x G \<sigma>))))"

lemma gb_purity_of_pure_language: "book_theory_formula gb_signature G (gb_purity_of_pure \<sigma>)"
  unfolding gb_purity_of_pure_def by (rule gb_pure_language, rule gb_Pure_language)
lemma gb_purity_of_fun_language: "book_theory_formula gb_signature G (gb_purity_of_fun \<sigma>)"
  unfolding gb_purity_of_fun_def by (rule gb_pure_language, rule gb_Fun_language)
lemma gb_target_PP_language: "book_theory_formula gb_signature G gb_target_PP"
  unfolding gb_target_PP_def by (rule gb_purity_of_pure_language)

lemma gb_application_closure_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_application_closure G \<sigma> \<tau>)"
proof -
  have app: "book_in_language book_minimal_logical_type UNIV gb_signature G
    (NApp (NVar (gb_x G (Arr \<sigma> \<tau>))) (NVar (gb_y G (Arr \<sigma> \<tau>) \<sigma>))) \<tau>"
    by (rule book_language_App[OF gb_x_language[OF rich, where \<sigma>="Arr \<sigma> \<tau>"]
      gb_y_language[OF rich, where \<sigma>="Arr \<sigma> \<tau>" and \<tau>=\<sigma>]])
  show ?thesis unfolding gb_application_closure_def
    by (intro book_all_language book_imp_language book_and_language[OF rich] gb_pure_language
      app gb_x_language[OF rich] gb_y_language[OF rich])
qed

lemma gb_persistence_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_persistence G \<sigma>)"
  unfolding gb_persistence_def
  by (intro book_all_language book_imp_language book_box_language[OF rich] gb_pure_language gb_x_language[OF rich])

lemma gb_unique_fundamental_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_unique_fundamental G \<sigma>)"
  unfolding gb_unique_fundamental_def
  by (intro book_exists_language[OF rich] book_and_language[OF rich] book_all_language book_imp_language
    book_leibniz_language[OF rich] gb_fun_language gb_x_language[OF rich] gb_y_language[OF rich])

lemma gb_no_fundamentals_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula gb_signature G (gb_no_fundamentals G \<sigma>)"
  unfolding gb_no_fundamentals_def
  by (intro book_all_language book_not_language[OF rich] gb_fun_language gb_x_language[OF rich])

lemma gb_basic_axioms_closed:
  "named_fv (gb_purity_of_pure \<sigma>) = {}"
  "named_fv (gb_purity_of_fun \<sigma>) = {}"
  "named_fv gb_target_PP = {}"
  "named_fv (gb_application_closure G \<sigma> \<tau>) = {}"
  "named_fv (gb_persistence G \<sigma>) = {}"
  "named_fv (gb_unique_fundamental G \<sigma>) = {}"
  "named_fv (gb_no_fundamentals G \<sigma>) = {}"
  unfolding gb_purity_of_pure_def gb_purity_of_fun_def gb_target_PP_def
    gb_application_closure_def gb_persistence_def gb_unique_fundamental_def gb_no_fundamentals_def
  by (auto simp: book_all_fv book_exists_fv book_imp_fv book_and_fv book_box_fv book_not_fv book_leibniz_fv)

end
