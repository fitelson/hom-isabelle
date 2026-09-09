theory Bacon_Book_ZF_K_Value
  imports Bacon_Book_ZF_Implication_Future_Set
    Bacon_Book_Modal_Representation.Bacon_Book_Canonical_Combinator_Syntax
begin

context book_full_C_canonical_frame
begin

definition full_ZF_K_value where
  "full_ZF_K_value w \<sigma> \<tau> = full_ZF_closed_value w (Arr \<sigma> (Arr \<tau> \<sigma>)) (book_canonical_K G \<sigma> \<tau>)"

theorem full_ZF_K_value_type:
  "full_ZF_K_value w \<sigma> \<tau> \<in> explode (full_ZF_D (Arr \<sigma> (Arr \<tau> \<sigma>)) w)"
  unfolding full_ZF_K_value_def by (rule full_ZF_closed_value_type[OF book_canonical_K_closed_terms[OF rich]])

theorem full_ZF_K_value_natural:
  "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
    full_ZF_i (Arr \<sigma> (Arr \<tau> \<sigma>)) w v (full_ZF_K_value w \<sigma> \<tau>) = full_ZF_K_value v \<sigma> \<tau>"
  unfolding full_ZF_K_value_def
  by (rule full_ZF_closed_value_natural[OF _ _ _ book_canonical_K_closed_terms[OF rich]]; assumption)

theorem full_ZF_K_future_value:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and access: "le w v"
    and am: "a \<in> explode (full_ZF_D \<sigma> w)" and bm: "b \<in> explode (full_ZF_D \<tau> v)"
  shows "app (app (full_ZF_K_value actual \<sigma> \<tau>) (Opair (book_ZF_world_code w) a))
    (Opair (book_ZF_world_code v) b) = full_ZF_i \<sigma> w v a"
proof -
  let ?x = "book_canonical_K_x G \<sigma>"
  let ?y = "book_canonical_K_y G \<sigma> \<tau>"
  have xt: "G ?x = \<sigma>" and yt: "G ?y = \<tau>" by (rule book_canonical_K_name_types[OF rich])+
  have distinct: "?x \<noteq> ?y" by (rule book_canonical_K_names_distinct[OF rich])
  have root: "actual \<in> worlds" by (rule book_full_C_root_is_world)
  have reach: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  obtain g where gt: "book_env_typed (\<lambda>\<rho>. explode (full_ZF_D \<rho> actual)) G g"
    using book_total_assignment_exists[where D="\<lambda>\<rho>. explode (full_ZF_D \<rho> actual)" and G=G,
      OF full_ZF_domains_nonempty[OF root]] by blast
  let ?h = "(full_ZF_assignment_move actual w g)(?x := a)"
  let ?k = "(full_ZF_assignment_move w v ?h)(?y := b)"
  have ax: "a \<in> explode (full_ZF_D (G ?x) w)" by (simp only: xt; rule am)
  have by_type: "b \<in> explode (full_ZF_D (G ?y) v)" by (simp only: yt; rule bm)
  have ht: "book_env_typed (\<lambda>\<rho>. explode (full_ZF_D \<rho> w)) G ?h"
    by (rule book_env_update[OF full_ZF_assignment_move_typed[OF root ww reach gt] ax])
  have kt: "book_env_typed (\<lambda>\<rho>. explode (full_ZF_D \<rho> v)) G ?k"
    by (rule book_env_update[OF full_ZF_assignment_move_typed[OF ww vw access ht] by_type])
  have xl: "book_in_language book_minimal_logical_type UNIV (fst actual) G (NVar ?x) \<sigma>"
    by (simp only: book_language_var_iff xt)
  have body: "book_in_language book_minimal_logical_type UNIV (fst actual) G (NLam ?y (NVar ?x)) (Arr \<tau> \<sigma>)"
    using book_language_Lam[where n="?y", OF xl] by (simp only: yt)
  have kdenote: "full_ZF_denote actual g (NLam ?x (NLam ?y (NVar ?x))) = full_ZF_K_value actual \<sigma> \<tau>"
    using full_ZF_denote_closed_value[OF book_canonical_K_closed_terms[OF rich], of actual g]
    by (simp only: book_canonical_K_def full_ZF_K_value_def)
  have first: "app (full_ZF_K_value actual \<sigma> \<tau>) (Opair (book_ZF_world_code w) a) =
    full_ZF_denote w ?h (NLam ?y (NVar ?x))"
    using full_ZF_denote_lambda_future[OF root ww reach body gt ax] by (simp only: kdenote)
  have xw: "book_in_language book_minimal_logical_type UNIV (fst w) G (NVar ?x) \<sigma>"
    by (simp only: book_language_var_iff xt)
  have second: "app (full_ZF_denote w ?h (NLam ?y (NVar ?x))) (Opair (book_ZF_world_code v) b) =
    full_ZF_denote v ?k (NVar ?x)"
    by (rule full_ZF_denote_lambda_future[OF ww vw access xw ht by_type])
  have result: "full_ZF_denote v ?k (NVar ?x) = full_ZF_i \<sigma> w v a"
    by (subst full_ZF_denote_var[OF vw kt]; simp add: full_ZF_assignment_move_def distinct xt)
  show ?thesis by (simp only: first second result)
qed

end

text \<open>
  Definition 18.1(3.1): the actual canonical image of λx.λy.x
  belongs to Dσ→τ→σ and satisfies k(w,a)(v,b)=iᵂᵛa.
  Both future applications use the proved abstraction equation;
  distinct binders preserve the first supplied value through the
  second update. No generic exponential K-membership premise is used.
\<close>

end
