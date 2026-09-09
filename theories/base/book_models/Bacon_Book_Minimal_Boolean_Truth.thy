theory Bacon_Book_Minimal_Boolean_Truth
  imports Bacon_Book_Minimal_Boolean_Syntax Bacon_Book_Minimal_Truth
begin

section \<open>Truth of the literal two-binder Boolean operators\<close>

text \<open>
  The operators of Table 4.1, p.93, have disjunction, conjunction, and
  biconditional truth conditions; ⊤ is true. Each binary application is
  evaluated by two actual λ-application equations, after which its body
  is interpreted under the two typed value updates.

  Representation. The values of A and B are both taken under the original
  assignment. The second binder name differs from the first, so its update
  does not erase the first value. No raw substitution of A/B into the body,
  Functionality, primitive/defined identity, or source H judgment is used.
\<close>

context book_full_minimal_model
begin

lemma book_boolean_first_update_typed:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
  shows "book_env_typed domain stock (g(book_prop_name stock := denote g A))"
proof -
  have member: "denote g A \<in> domain Prop" by (rule denote_type[OF UNIV_I A typed])
  have named: "denote g A \<in> domain (stock (book_prop_name stock))"
    by (simp only: book_prop_name_type[OF rich]; rule member)
  show ?thesis by (rule book_env_update[OF typed named])
qed

lemma book_boolean_updates_typed:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "book_env_typed domain stock
    ((g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B))"
proof -
  have first: "book_env_typed domain stock (g(book_prop_name stock := denote g A))"
    by (rule book_boolean_first_update_typed[OF rich typed A])
  have member: "denote g B \<in> domain Prop" by (rule denote_type[OF UNIV_I B typed])
  have named: "denote g B \<in> domain (stock (book_second_prop_name stock))"
    by (simp only: book_second_prop_name_type[OF rich]; rule member)
  show ?thesis by (rule book_env_update[OF first named])
qed

lemma book_boolean_variable_values:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "denote ((g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B))
      (NVar (book_prop_name stock)) = denote g A"
    and "denote ((g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B))
      (NVar (book_second_prop_name stock)) = denote g B"
proof -
  let ?h = "(g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B)"
  have ht: "book_env_typed domain stock ?h" by (rule book_boolean_updates_typed[OF rich typed A B])
  show "denote ?h (NVar (book_prop_name stock)) = denote g A"
    using denote_var[where n="book_prop_name stock", OF UNIV_I ht]
    by (simp add: book_boolean_names_distinct[OF rich])
  show "denote ?h (NVar (book_second_prop_name stock)) = denote g B"
    using denote_var[where n="book_second_prop_name stock", OF UNIV_I ht] by simp
qed

lemma book_double_lambda_denote:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and body: "book_in_language book_minimal_logical_type UNIV signature stock M Prop"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "denote g (NApp (NApp (NLam (book_prop_name stock) (NLam (book_second_prop_name stock) M)) A) B) =
    denote ((g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B)) M"
proof -
  let ?p = "book_prop_name stock"
  let ?q = "book_second_prop_name stock"
  let ?F = "NLam ?p (NLam ?q M)"
  let ?a = "denote g A"
  let ?b = "denote g B"
  have ptype: "stock ?p = Prop" by (rule book_prop_name_type[OF rich])
  have qtype: "stock ?q = Prop" by (rule book_second_prop_name_type[OF rich])
  have inner_language: "book_in_language book_minimal_logical_type UNIV signature stock (NLam ?q M) (Arr Prop Prop)"
    using book_language_Lam[where n="?q", OF body] by (simp only: qtype)
  have fl: "book_in_language book_minimal_logical_type UNIV signature stock ?F (Arr Prop (Arr Prop Prop))"
    by (rule book_boolean_abstraction_language[OF rich body])
  have fal: "book_in_language book_minimal_logical_type UNIV signature stock (NApp ?F A) (Arr Prop Prop)"
    by (rule book_language_App[OF fl A])
  have first_app: "denote g (NApp ?F A) = app Prop (Arr Prop Prop) (denote g ?F) ?a"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fl A typed])
  have second_app: "denote g (NApp (NApp ?F A) B) = app Prop Prop (denote g (NApp ?F A)) ?b"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fal B typed])
  have am: "?a \<in> domain (stock ?p)"
    by (simp only: ptype; rule denote_type[OF UNIV_I A typed])
  have bm: "?b \<in> domain (stock ?q)"
    by (simp only: qtype; rule denote_type[OF UNIV_I B typed])
  have ht: "book_env_typed domain stock (g(?p := ?a))" by (rule book_env_update[OF typed am])
  have first_beta: "app Prop (Arr Prop Prop) (denote g ?F) ?a = denote (g(?p := ?a)) (NLam ?q M)"
    using book_full_lambda_application[OF inner_language typed am] by (simp only: ptype)
  have second_beta: "app Prop Prop (denote (g(?p := ?a)) (NLam ?q M)) ?b = denote ((g(?p := ?a))(?q := ?b)) M"
    using book_full_lambda_application[OF body ht bm] by (simp only: qtype)
  show ?thesis by (simp only: second_app first_app first_beta second_beta)
qed

theorem book_or_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "V (denote g (book_or stock A B)) = (V (denote g A) \<or> V (denote g B))"
proof -
  let ?p = "NVar (book_prop_name stock)"
  let ?q = "NVar (book_second_prop_name stock)"
  let ?h = "(g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B)"
  have pl: "book_in_language book_minimal_logical_type UNIV signature stock ?p Prop"
    by (rule book_boolean_variables_language(1)[OF rich])
  have ql: "book_in_language book_minimal_logical_type UNIV signature stock ?q Prop"
    by (rule book_boolean_variables_language(2)[OF rich])
  have ht: "book_env_typed domain stock ?h" by (rule book_boolean_updates_typed[OF rich typed A B])
  have evaluated: "denote g (book_or stock A B) = denote ?h (book_imp (book_not stock ?p) ?q)"
    using book_double_lambda_denote[OF rich typed book_or_body_language[OF rich] A B]
    by (simp only: book_or_def book_or_const_def)
  have body_truth: "V (denote ?h (book_imp (book_not stock ?p) ?q)) = (V (denote g A) \<or> V (denote g B))"
    by (simp only: book_imp_truth[OF ht book_not_language[OF rich pl] ql]
      book_not_truth[OF rich ht pl] book_boolean_variable_values[OF rich typed A B]; blast)
  show ?thesis by (simp only: evaluated; rule body_truth)
qed

theorem book_and_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "V (denote g (book_and stock A B)) = (V (denote g A) \<and> V (denote g B))"
proof -
  let ?p = "NVar (book_prop_name stock)"
  let ?q = "NVar (book_second_prop_name stock)"
  let ?h = "(g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B)"
  have pl: "book_in_language book_minimal_logical_type UNIV signature stock ?p Prop"
    by (rule book_boolean_variables_language(1)[OF rich])
  have ql: "book_in_language book_minimal_logical_type UNIV signature stock ?q Prop"
    by (rule book_boolean_variables_language(2)[OF rich])
  have ht: "book_env_typed domain stock ?h" by (rule book_boolean_updates_typed[OF rich typed A B])
  have implication_language: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp ?p (book_not stock ?q)) Prop"
    by (rule book_imp_language[OF pl book_not_language[OF rich ql]])
  have evaluated: "denote g (book_and stock A B) = denote ?h (book_not stock (book_imp ?p (book_not stock ?q)))"
    using book_double_lambda_denote[OF rich typed book_and_body_language[OF rich] A B]
    by (simp only: book_and_def book_and_const_def)
  have body_truth: "V (denote ?h (book_not stock (book_imp ?p (book_not stock ?q)))) =
    (V (denote g A) \<and> V (denote g B))"
    by (simp only: book_not_truth[OF rich ht implication_language]
      book_imp_truth[OF ht pl book_not_language[OF rich ql]] book_not_truth[OF rich ht ql]
      book_boolean_variable_values[OF rich typed A B]; blast)
  show ?thesis by (simp only: evaluated; rule body_truth)
qed

theorem book_iff_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and A: "book_in_language book_minimal_logical_type UNIV signature stock A Prop"
    and B: "book_in_language book_minimal_logical_type UNIV signature stock B Prop"
  shows "V (denote g (book_iff stock A B)) = (V (denote g A) = V (denote g B))"
proof -
  let ?p = "NVar (book_prop_name stock)"
  let ?q = "NVar (book_second_prop_name stock)"
  let ?h = "(g(book_prop_name stock := denote g A))(book_second_prop_name stock := denote g B)"
  have pl: "book_in_language book_minimal_logical_type UNIV signature stock ?p Prop"
    by (rule book_boolean_variables_language(1)[OF rich])
  have ql: "book_in_language book_minimal_logical_type UNIV signature stock ?q Prop"
    by (rule book_boolean_variables_language(2)[OF rich])
  have ht: "book_env_typed domain stock ?h" by (rule book_boolean_updates_typed[OF rich typed A B])
  have pq: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp ?p ?q) Prop"
    by (rule book_imp_language[OF pl ql])
  have qp: "book_in_language book_minimal_logical_type UNIV signature stock (book_imp ?q ?p) Prop"
    by (rule book_imp_language[OF ql pl])
  have evaluated: "denote g (book_iff stock A B) = denote ?h (book_and stock (book_imp ?p ?q) (book_imp ?q ?p))"
    using book_double_lambda_denote[OF rich typed book_iff_body_language[OF rich] A B]
    by (simp only: book_iff_def book_iff_const_def)
  have body_truth: "V (denote ?h (book_and stock (book_imp ?p ?q) (book_imp ?q ?p))) =
    (V (denote g A) = V (denote g B))"
    by (simp only: book_and_truth[OF rich ht pq qp] book_imp_truth[OF ht pl ql] book_imp_truth[OF ht ql pl]
      book_boolean_variable_values[OF rich typed A B]; blast)
  show ?thesis by (simp only: evaluated; rule body_truth)
qed

theorem book_top_true:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "V (denote g (book_top stock))"
  by (simp only: book_top_def book_not_truth[OF rich typed book_bottom_language[OF rich]];
    rule book_bottom_false[OF rich typed])

end

end
