theory Bacon_Book_Head_Test
  imports Bacon_Book_Full_Environment
    Bacon_Source_Vocabulary_Development.Bacon_Source_Rich_Stock
begin

section \<open>A represented predicate testing the head of an application\<close>

text \<open>
  Given a ∈ Dσ and P ∈ Dτ→t, the term λn.v(nu), with
  u:σ, v:τ → t and n:σ → τ, represents the predicate
  f ↦ Appτt(P,Appστ(f,a)). Choose distinct names and assign a and P
  to u and v. The previously proved λ-application equation supplies
  the required behavior, not Functionality.

  Source role: a full-language testing ingredient for the congruence
  assertion of Bacon's Exercise 15.5, p.321, preceding Proposition 15.5,
  p.322. Definition 3.1, p.57, licenses these abstractions in the full
  grammar. Definition 9.1, p.190, does not give unrestricted abstraction
  closure to an arbitrary general λ-language.

  Status: this theorem is in book_full_environment with a given typed
  total assignment. It proves neither tester availability in every
  general 𝒥(Σ) nor any truth or Leibniz-equivalence principle.
\<close>

context book_full_environment
begin

lemma book_head_test_body_language:
  assumes u_type: "stock u = \<sigma>" and v_type: "stock v = Arr \<tau> Prop"
    and n_type: "stock n = Arr \<sigma> \<tau>"
  shows "book_in_language logical_type logical_signature signature stock
    (NApp (NVar v) (NApp (NVar n) (NVar u))) Prop"
proof -
  have ul: "book_in_language logical_type logical_signature signature stock (NVar u) \<sigma>"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=u] by (simp only: u_type)
  have vl: "book_in_language logical_type logical_signature signature stock (NVar v) (Arr \<tau> Prop)"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=v] by (simp only: v_type)
  have nl: "book_in_language logical_type logical_signature signature stock (NVar n) (Arr \<sigma> \<tau>)"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=n] by (simp only: n_type)
  show ?thesis by (rule book_language_App[OF vl book_language_App[OF nl ul]])
qed

lemma book_head_test_body_evaluation:
  assumes u_type: "stock u = \<sigma>" and v_type: "stock v = Arr \<tau> Prop"
    and n_type: "stock n = Arr \<sigma> \<tau>"
    and typed: "book_env_typed domain stock k"
  shows "denote k (NApp (NVar v) (NApp (NVar n) (NVar u))) =
    app \<tau> Prop (k v) (app \<sigma> \<tau> (k n) (k u))"
proof -
  have ul: "book_in_language logical_type logical_signature signature stock (NVar u) \<sigma>"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=u] by (simp only: u_type)
  have vl: "book_in_language logical_type logical_signature signature stock (NVar v) (Arr \<tau> Prop)"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=v] by (simp only: v_type)
  have nl: "book_in_language logical_type logical_signature signature stock (NVar n) (Arr \<sigma> \<tau>)"
    using book_language_Var[where L=logical_type and \<Lambda>=logical_signature
      and \<Sigma>=signature and G=stock and n=n] by (simp only: n_type)
  have inner_language: "book_in_language logical_type logical_signature signature stock
    (NApp (NVar n) (NVar u)) \<tau>"
    by (rule book_language_App[OF nl ul])
  have inner: "denote k (NApp (NVar n) (NVar u)) =
    app \<sigma> \<tau> (denote k (NVar n)) (denote k (NVar u))"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I nl ul typed])
  have outer: "denote k (NApp (NVar v) (NApp (NVar n) (NVar u))) =
    app \<tau> Prop (denote k (NVar v)) (denote k (NApp (NVar n) (NVar u)))"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I vl inner_language typed])
  have var_value: "denote k (NVar i) = k i" for i
    by (rule denote_var[OF UNIV_I typed])
  show ?thesis by (simp only: outer inner var_value)
qed

theorem book_head_test_exists:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and argument: "a \<in> domain \<sigma>" and predicate: "P \<in> domain (Arr \<tau> Prop)"
  shows "\<exists>h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop).
    \<forall>f \<in> domain (Arr \<sigma> \<tau>).
      app (Arr \<sigma> \<tau>) Prop h f = app \<tau> Prop P (app \<sigma> \<tau> f a)"
proof -
  obtain u where u_type: "stock u = \<sigma>"
    by (rule sg_rich_variable[where \<sigma>=\<sigma>, OF rich]; rule that; assumption)
  obtain v where v_type: "stock v = Arr \<tau> Prop" and v_fresh: "v \<notin> {u}"
    using sg_rich_fresh[where \<sigma>="Arr \<tau> Prop" and S="{u}", OF rich] by auto
  obtain n where n_type: "stock n = Arr \<sigma> \<tau>" and n_fresh: "n \<notin> {u,v}"
    using sg_rich_fresh[where \<sigma>="Arr \<sigma> \<tau>" and S="{u,v}", OF rich] by auto
  let ?k = "(g(u := a))(v := P)"
  let ?M = "NApp (NVar v) (NApp (NVar n) (NVar u)) :: ('c,'l) named_term"
  let ?h = "denote ?k (NLam n ?M)"
  have a_type: "a \<in> domain (stock u)" using argument by (simp only: u_type)
  have p_type: "P \<in> domain (stock v)" using predicate by (simp only: v_type)
  have first_update: "book_env_typed domain stock (g(u := a))"
    by (rule book_env_update[OF typed a_type])
  have kt: "book_env_typed domain stock ?k" by (rule book_env_update[OF first_update p_type])
  have body_language: "book_in_language logical_type logical_signature signature stock ?M Prop"
    by (rule book_head_test_body_language[OF u_type v_type n_type])
  have abstraction_language: "book_in_language logical_type logical_signature signature stock
    (NLam n ?M) (Arr (Arr \<sigma> \<tau>) Prop)"
    using book_language_Lam[OF body_language, where n=n] by (simp only: n_type)
  have h_type: "?h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop)"
    by (rule denote_type[OF UNIV_I abstraction_language kt])
  show ?thesis
  proof (rule bexI[where x="?h"])
    show "\<forall>f \<in> domain (Arr \<sigma> \<tau>).
      app (Arr \<sigma> \<tau>) Prop ?h f = app \<tau> Prop P (app \<sigma> \<tau> f a)"
    proof (rule ballI)
      fix f
      assume member: "f \<in> domain (Arr \<sigma> \<tau>)"
      have f_type: "f \<in> domain (stock n)" using member by (simp only: n_type)
      have updated: "book_env_typed domain stock (?k(n := f))"
        by (rule book_env_update[OF kt f_type])
      have beta: "app (Arr \<sigma> \<tau>) Prop ?h f = denote (?k(n := f)) ?M"
        using book_full_lambda_application[where n=n, OF body_language kt f_type]
        by (simp only: n_type)
      have evaluation: "denote (?k(n := f)) ?M =
        app \<tau> Prop ((?k(n := f)) v) (app \<sigma> \<tau> ((?k(n := f)) n) ((?k(n := f)) u))"
        by (rule book_head_test_body_evaluation[OF u_type v_type n_type updated])
      have at_u: "(?k(n := f)) u = a" using v_fresh n_fresh by auto
      have at_v: "(?k(n := f)) v = P" using n_fresh by auto
      have at_n: "(?k(n := f)) n = f" by simp
      show "app (Arr \<sigma> \<tau>) Prop ?h f = app \<tau> Prop P (app \<sigma> \<tau> f a)"
        by (simp only: beta evaluation at_u at_v at_n)
    qed
  next
    show "?h \<in> domain (Arr (Arr \<sigma> \<tau>) Prop)" by (rule h_type)
  qed
qed

end

end
