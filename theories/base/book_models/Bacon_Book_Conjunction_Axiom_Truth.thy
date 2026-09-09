theory Bacon_Book_Conjunction_Axiom_Truth
  imports Bacon_Book_Minimal_Validity
begin

section \<open>The three conjunction axioms determine all-domain truth\<close>

text \<open>
  Suppose a closed operator K:t→t→t has value k, and its three
  conjunction schemas hold globally at two distinct proposition variables.
  For arbitrary a,b∈Dₜ, assign those variables a and b. The introduction
  schema gives v(a)∧v(b)→v(kab); the two elimination schemas give the
  converse. This proves the source truth clause on EVERY domain pair,
  without assuming closed denotability of those arguments.

  Source: conjunction axioms in §5.2, p.104, and Definition 15.1, p.314.
  K is an arbitrary witnessed closed operator; the theorem does not identify
  it with a λ-defined conjunction or construct a richer model by itself.
\<close>

context book_full_minimal_model
begin

theorem book_conjunction_axioms_truth:
  assumes closed_value: "book_closed_value (Arr Prop (Arr Prop Prop)) K k"
    and xtype: "stock x = Prop" and ytype: "stock y = Prop" and distinct: "x \<noteq> y"
    and introduction: "book_formula_valid domain stock denote V
      (book_imp (NVar x) (book_imp (NVar y) (NApp (NApp K (NVar x)) (NVar y))))"
    and left_axiom: "book_formula_valid domain stock denote V
      (book_imp (NApp (NApp K (NVar x)) (NVar y)) (NVar x))"
    and right_axiom: "book_formula_valid domain stock denote V
      (book_imp (NApp (NApp K (NVar x)) (NVar y)) (NVar y))"
    and a_member: "a \<in> domain Prop" and b_member: "b \<in> domain Prop"
  shows "V (app Prop Prop (app Prop (Arr Prop Prop) k a) b) \<longleftrightarrow> (V a \<and> V b)"
proof -
  let ?X = "NVar x"
  let ?Y = "NVar y"
  let ?C = "NApp (NApp K ?X) ?Y"
  have kl: "book_in_language book_minimal_logical_type UNIV signature stock K (Arr Prop (Arr Prop Prop))"
    using closed_value unfolding book_closed_value_def by blast
  have xl: "book_in_language book_minimal_logical_type UNIV signature stock ?X Prop"
    by (simp add: book_language_var_iff xtype)
  have yl: "book_in_language book_minimal_logical_type UNIV signature stock ?Y Prop"
    by (simp add: book_language_var_iff ytype)
  have partial: "book_in_language book_minimal_logical_type UNIV signature stock (NApp K ?X) (Arr Prop Prop)"
    by (rule book_language_App[OF kl xl])
  have cl: "book_in_language book_minimal_logical_type UNIV signature stock ?C Prop"
    by (rule book_language_App[OF partial yl])
  obtain g0 where typed0: "book_env_typed domain stock g0"
    using book_minimal_assignment_exists by blast
  have a_type: "a \<in> domain (stock x)" using a_member by (simp only: xtype)
  have b_type: "b \<in> domain (stock y)" using b_member by (simp only: ytype)
  have typed1: "book_env_typed domain stock (g0(x := a))" by (rule book_env_update[OF typed0 a_type])
  let ?g = "(g0(x := a))(y := b)"
  have typed: "book_env_typed domain stock ?g" by (rule book_env_update[OF typed1 b_type])
  have xv: "denote ?g ?X = a" using denote_var[OF UNIV_I typed, where n=x] distinct by simp
  have yv: "denote ?g ?Y = b" using denote_var[OF UNIV_I typed, where n=y] by simp
  have kv: "denote ?g K = k" by (rule book_closed_value_at[OF closed_value typed])
  have first_app: "denote ?g (NApp K ?X) = app Prop (Arr Prop Prop) k a"
    using denote_app[OF UNIV_I UNIV_I UNIV_I kl xl typed] by (simp only: kv xv)
  have cv: "denote ?g ?C = app Prop Prop (app Prop (Arr Prop Prop) k a) b"
    using denote_app[OF UNIV_I UNIV_I UNIV_I partial yl typed] by (simp only: first_app yv)
  have outer: "V (denote ?g (book_imp ?X (book_imp ?Y ?C)))"
    by (rule book_formula_validE[OF introduction typed])
  have left: "V (denote ?g (book_imp ?C ?X))" by (rule book_formula_validE[OF left_axiom typed])
  have right: "V (denote ?g (book_imp ?C ?Y))" by (rule book_formula_validE[OF right_axiom typed])
  have intro_truth: "V a \<longrightarrow> V b \<longrightarrow> V (denote ?g ?C)"
    using outer book_imp_truth[OF typed xl book_imp_language[OF yl cl]]
      book_imp_truth[OF typed yl cl] by (simp only: xv yv; blast)
  have left_truth: "V (denote ?g ?C) \<longrightarrow> V a"
    using left book_imp_truth[OF typed cl xl] by (simp only: xv; blast)
  have right_truth: "V (denote ?g ?C) \<longrightarrow> V b"
    using right book_imp_truth[OF typed cl yl] by (simp only: yv; blast)
  show ?thesis using intro_truth left_truth right_truth by (simp only: cv; blast)
qed

end

end
