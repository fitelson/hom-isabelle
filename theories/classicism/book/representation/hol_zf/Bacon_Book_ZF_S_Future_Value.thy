theory Bacon_Book_ZF_S_Future_Value
  imports Bacon_Book_ZF_S_Body
begin

context book_full_C_canonical_frame
begin

theorem full_ZF_S_future_value:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds"
    and wv: "le w v" and vu: "le v u"
    and fm: "f \<in> explode (full_ZF_D (Arr \<sigma> (Arr \<tau> \<rho>)) w)"
    and gm: "g \<in> explode (full_ZF_D (Arr \<sigma> \<tau>) v)"
    and am: "a \<in> explode (full_ZF_D \<sigma> u)"
  shows "app (app (app (full_ZF_S_value actual \<sigma> \<tau> \<rho>) (Opair (book_ZF_world_code w) f))
      (Opair (book_ZF_world_code v) g)) (Opair (book_ZF_world_code u) a) =
    app (app f (Opair (book_ZF_world_code u) a))
      (Opair (book_ZF_world_code u) (app g (Opair (book_ZF_world_code u) a)))"
proof -
  let ?nf = "book_canonical_S_f G \<sigma> \<tau> \<rho>"
  let ?ng = "book_canonical_S_g G \<sigma> \<tau> \<rho>"
  let ?nx = "book_canonical_S_x G \<sigma> \<tau> \<rho>"
  let ?body = "book_canonical_S_body G \<sigma> \<tau> \<rho>"
  let ?inner = "NLam ?nx ?body"
  let ?middle = "NLam ?ng ?inner"
  have nft: "G ?nf = Arr \<sigma> (Arr \<tau> \<rho>)" and ngt: "G ?ng = Arr \<sigma> \<tau>" and nxt: "G ?nx = \<sigma>"
    by (rule book_canonical_S_name_types[OF rich])+
  have fg: "?nf \<noteq> ?ng" and fx: "?nf \<noteq> ?nx" and gx: "?ng \<noteq> ?nx"
    by (rule book_canonical_S_names_distinct[OF rich])+
  have root: "actual \<in> worlds" by (rule book_full_C_root_is_world)
  have reach: "le actual w" by (rule book_full_C_rooted_world_data(2)[OF ww])
  have wu: "le w u" by (rule book_full_C_rooted_trans[OF ww wv vu])
  obtain r where rt: "book_env_typed (\<lambda>\<delta>. explode (full_ZF_D \<delta> actual)) G r"
    using book_total_assignment_exists[where D="\<lambda>\<delta>. explode (full_ZF_D \<delta> actual)" and G=G,
      OF full_ZF_domains_nonempty[OF root]] by blast
  let ?h1 = "(full_ZF_assignment_move actual w r)(?nf := f)"
  let ?h2 = "(full_ZF_assignment_move w v ?h1)(?ng := g)"
  let ?h3 = "(full_ZF_assignment_move v u ?h2)(?nx := a)"
  have fn: "f \<in> explode (full_ZF_D (G ?nf) w)" by (simp only: nft; rule fm)
  have gn: "g \<in> explode (full_ZF_D (G ?ng) v)" by (simp only: ngt; rule gm)
  have an: "a \<in> explode (full_ZF_D (G ?nx) u)" by (simp only: nxt; rule am)
  have h1t: "book_env_typed (\<lambda>\<delta>. explode (full_ZF_D \<delta> w)) G ?h1"
    by (rule book_env_update[OF full_ZF_assignment_move_typed[OF root ww reach rt] fn])
  have h2t: "book_env_typed (\<lambda>\<delta>. explode (full_ZF_D \<delta> v)) G ?h2"
    by (rule book_env_update[OF full_ZF_assignment_move_typed[OF ww vw wv h1t] gn])
  have h3t: "book_env_typed (\<lambda>\<delta>. explode (full_ZF_D \<delta> u)) G ?h3"
    by (rule book_env_update[OF full_ZF_assignment_move_typed[OF vw uw vu h2t] an])
  have inner_language: "book_in_language book_minimal_logical_type UNIV \<Omega> G ?inner (Arr \<sigma> \<rho>)" for \<Omega>
    using book_language_Lam[where n="?nx", OF book_canonical_S_body_language[OF rich]] by (simp only: nxt)
  have middle_language: "book_in_language book_minimal_logical_type UNIV \<Omega> G ?middle (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))" for \<Omega>
    using book_language_Lam[where n="?ng", OF inner_language] by (simp only: ngt)
  have sdenote: "full_ZF_denote actual r (NLam ?nf ?middle) = full_ZF_S_value actual \<sigma> \<tau> \<rho>"
    using full_ZF_denote_closed_value[where w=actual and g=r and A="book_canonical_S G \<sigma> \<tau> \<rho>",
      OF book_canonical_S_closed_terms[OF rich]]
    by (simp only: book_canonical_S_def full_ZF_S_value_def)
  have first: "app (full_ZF_S_value actual \<sigma> \<tau> \<rho>) (Opair (book_ZF_world_code w) f) = full_ZF_denote w ?h1 ?middle"
    using full_ZF_denote_lambda_future[OF root ww reach middle_language rt fn] by (simp only: sdenote)
  have second: "app (full_ZF_denote w ?h1 ?middle) (Opair (book_ZF_world_code v) g) = full_ZF_denote v ?h2 ?inner"
    by (rule full_ZF_denote_lambda_future[OF ww vw wv inner_language h1t gn])
  have third: "app (full_ZF_denote v ?h2 ?inner) (Opair (book_ZF_world_code u) a) = full_ZF_denote u ?h3 ?body"
    by (rule full_ZF_denote_lambda_future[OF vw uw vu book_canonical_S_body_language[OF rich] h2t an])
  have f_lookup: "?h3 ?nf = full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) v u
    (full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) w v f)"
    by (simp add: full_ZF_assignment_move_def fg fx nft)
  have g_lookup: "?h3 ?ng = full_ZF_i (Arr \<sigma> \<tau>) v u g"
    by (simp add: full_ZF_assignment_move_def gx ngt)
  have x_lookup: "?h3 ?nx = a" by simp
  have f_chain: "full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) v u (full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) w v f) =
    full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) w u f"
    by (rule full_ZF_i_composition[OF ww vw uw wv vu fm, symmetric])
  have f_eval: "app (full_ZF_i (Arr \<sigma> (Arr \<tau> \<rho>)) w u f) (Opair (book_ZF_world_code u) a) =
    app f (Opair (book_ZF_world_code u) a)"
    using full_ZF_future_application[OF ww uw wu fm am] by (simp only: full_ZF_app_def; blast)
  have g_eval: "app (full_ZF_i (Arr \<sigma> \<tau>) v u g) (Opair (book_ZF_world_code u) a) =
    app g (Opair (book_ZF_world_code u) a)"
    using full_ZF_future_application[OF vw uw vu gm am] by (simp only: full_ZF_app_def; blast)
  have result: "full_ZF_denote u ?h3 ?body =
    app (app f (Opair (book_ZF_world_code u) a)) (Opair (book_ZF_world_code u) (app g (Opair (book_ZF_world_code u) a)))"
    by (subst full_ZF_S_body_evaluation[OF uw h3t]; simp only: f_lookup g_lookup x_lookup f_chain f_eval g_eval)
  show ?thesis by (simp only: first second third result)
qed

end

text \<open>
  Definition 18.1(3.2), on the actual typed argument domains:
  s(w,f)(v,g)(u,a)=f(u,a)(u,g(u,a)).
  The three abstraction steps transport and update assignments at
  the successive worlds. Distinct names preserve the earlier inputs;
  counterpart composition and actual graph restriction then recover
  the displayed f and g applications. Membership of s is supplied
  by its actual closed-term image, not by ambient exponential fullness.
\<close>

end
