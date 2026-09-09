theory Bacon_Book_Disjunction_Axiom_Truth
  imports Bacon_Book_Conjunction_Decoded_Model Bacon_Book_Minimal_Validity
begin

section \<open>The source disjunction schemas force truth on the whole domain\<close>

text \<open>
  Let K:t→t→t be a witnessed closed operator in a native conjunction
  model. Suppose its three disjunction schemas hold globally at distinct
  proposition variables x,y,z. Then v(kab) ↔ v(a)∨v(b) for EVERY
  a,b∈Dₜ. Source: §5.2, p.104, and Definition 15.1, p.314.

  Assign x=a, y=b, and z=f, where f is a false proposition supplied
  by the model. The introduction schemas yield both truth implications
  into kab. If a and b are false, the elimination schema with consequent
  f forces kab to be false. No closed name for a, b or f is required.

  This is an all-domain semantic calculation conditional on the displayed
  model and global schemas. It is not yet a construction of a model with
  primitive ∨. It uses neither Functionality nor an identity of K with
  a λ-defined disjunction.
\<close>

context book_conjunction_model
begin

theorem book_disjunction_axioms_truth:
  assumes closed_value: "book_closed_value (Arr Prop (Arr Prop Prop)) K k"
    and xtype: "stock x = Prop" and ytype: "stock y = Prop" and ztype: "stock z = Prop"
    and xy: "x \<noteq> y" and xz: "x \<noteq> z" and yz: "y \<noteq> z"
    and elimination: "book_formula_valid domain stock denote V
      (book_conj_imp (book_conj_imp (NVar x) (NVar z))
        (book_conj_imp (book_conj_imp (NVar y) (NVar z))
          (book_conj_imp (NApp (NApp K (NVar x)) (NVar y)) (NVar z))))"
    and left_axiom: "book_formula_valid domain stock denote V
      (book_conj_imp (NVar x) (NApp (NApp K (NVar x)) (NVar y)))"
    and right_axiom: "book_formula_valid domain stock denote V
      (book_conj_imp (NVar y) (NApp (NApp K (NVar x)) (NVar y)))"
    and am: "a \<in> domain Prop" and bm: "b \<in> domain Prop"
  shows "V (app Prop Prop (app Prop (Arr Prop Prop) k a) b) \<longleftrightarrow> (V a \<or> V b)"
proof -
  let ?X = "NVar x"
  let ?Y = "NVar y"
  let ?Z = "NVar z"
  let ?C = "NApp (NApp K ?X) ?Y"
  have kl: "book_in_language book_conj_logical_type UNIV signature stock K (Arr Prop (Arr Prop Prop))"
    using closed_value unfolding book_closed_value_def by blast
  have xl: "book_conj_formula signature stock ?X" by (simp add: book_language_var_iff xtype)
  have yl: "book_conj_formula signature stock ?Y" by (simp add: book_language_var_iff ytype)
  have zl: "book_conj_formula signature stock ?Z" by (simp add: book_language_var_iff ztype)
  have partial: "book_in_language book_conj_logical_type UNIV signature stock (NApp K ?X) (Arr Prop Prop)"
    by (rule book_language_App[OF kl xl])
  have cl: "book_conj_formula signature stock ?C" by (rule book_language_App[OF partial yl])
  have xzl: "book_conj_formula signature stock (book_conj_imp ?X ?Z)"
    by (rule book_conj_imp_language[OF xl zl])
  have yzl: "book_conj_formula signature stock (book_conj_imp ?Y ?Z)"
    by (rule book_conj_imp_language[OF yl zl])
  have czl: "book_conj_formula signature stock (book_conj_imp ?C ?Z)"
    by (rule book_conj_imp_language[OF cl zl])
  have tail_language: "book_conj_formula signature stock
    (book_conj_imp (book_conj_imp ?Y ?Z) (book_conj_imp ?C ?Z))"
    by (rule book_conj_imp_language[OF yzl czl])
  obtain f where fm: "f \<in> domain Prop" and false_f: "\<not> V f"
    using false_proposition by blast
  obtain g0 where typed0: "book_env_typed domain stock g0"
    using book_conjunction_assignment_exists by blast
  have a_type: "a \<in> domain (stock x)" using am by (simp only: xtype)
  have b_type: "b \<in> domain (stock y)" using bm by (simp only: ytype)
  have f_type: "f \<in> domain (stock z)" using fm by (simp only: ztype)
  have typed1: "book_env_typed domain stock (g0(x := a))" by (rule book_env_update[OF typed0 a_type])
  have typed2: "book_env_typed domain stock ((g0(x := a))(y := b))" by (rule book_env_update[OF typed1 b_type])
  let ?g = "((g0(x := a))(y := b))(z := f)"
  have typed: "book_env_typed domain stock ?g" by (rule book_env_update[OF typed2 f_type])
  have xv: "denote ?g ?X = a" using denote_var[OF UNIV_I typed, where n=x] xy xz by simp
  have yv: "denote ?g ?Y = b" using denote_var[OF UNIV_I typed, where n=y] yz by simp
  have zv: "denote ?g ?Z = f" using denote_var[OF UNIV_I typed, where n=z] by simp
  have kv: "denote ?g K = k" by (rule book_closed_value_at[OF closed_value typed])
  have first_app: "denote ?g (NApp K ?X) = app Prop (Arr Prop Prop) k a"
    using denote_app[OF UNIV_I UNIV_I UNIV_I kl xl typed] by (simp only: kv xv)
  have cv: "denote ?g ?C = app Prop Prop (app Prop (Arr Prop Prop) k a) b"
    using denote_app[OF UNIV_I UNIV_I UNIV_I partial yl typed] by (simp only: first_app yv)
  have left: "V (denote ?g (book_conj_imp ?X ?C))" by (rule book_formula_validE[OF left_axiom typed])
  have right: "V (denote ?g (book_conj_imp ?Y ?C))" by (rule book_formula_validE[OF right_axiom typed])
  have elim_truth: "V (denote ?g
    (book_conj_imp (book_conj_imp ?X ?Z)
      (book_conj_imp (book_conj_imp ?Y ?Z) (book_conj_imp ?C ?Z))))"
    by (rule book_formula_validE[OF elimination typed])
  have left_truth: "V a \<longrightarrow> V (denote ?g ?C)"
    using left book_conj_imp_truth[OF typed xl cl] by (simp only: xv; blast)
  have right_truth: "V b \<longrightarrow> V (denote ?g ?C)"
    using right book_conj_imp_truth[OF typed yl cl] by (simp only: yv; blast)
  have eliminate: "(V a \<longrightarrow> V f) \<longrightarrow> (V b \<longrightarrow> V f) \<longrightarrow>
    (V (denote ?g ?C) \<longrightarrow> V f)"
    using elim_truth
    by (simp only: book_conj_imp_truth[OF typed xzl tail_language]
      book_conj_imp_truth[OF typed yzl czl] book_conj_imp_truth[OF typed xl zl]
      book_conj_imp_truth[OF typed yl zl] book_conj_imp_truth[OF typed cl zl] xv yv zv)
  show ?thesis using left_truth right_truth eliminate false_f by (simp only: cv; blast)
qed

end

end
