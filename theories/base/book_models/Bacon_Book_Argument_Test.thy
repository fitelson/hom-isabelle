theory Bacon_Book_Argument_Test
  imports Bacon_Book_Full_Environment Bacon_Source_Vocabulary_Development.Bacon_Source_Rich_Stock
begin

section \<open>Representing the predicate a ↦ P(fa) in a full environment\<close>

text \<open>
  Given f ∈ Dσ→τ and P ∈ Dτ→t, the term λn.v(u n), evaluated
  with u assigned f and v assigned P, denotes an h ∈ Dσ→t satisfying
  Appσt(h,a) = Appτt(P,Appστ(f,a)). Source role: the full-language
  instance of Bacon's environment model condition, Definition 14.13,
  p.302, used to construct the predicate tests of Exercise 15.5, p.321.

  Representation. The three names are distinct and have the displayed
  fixed types. Typed updates preserve the given total assignment. The
  full environment supplies the actual λ denotation; no Functionality,
  valuation, Leibniz equivalence, or assumed tester closure is used.
  This is conditional on the full-language specialization, not a claim
  that an arbitrary admitted λ-sublanguage contains the tester.
\<close>

context book_full_environment
begin

lemma book_argument_body_language:
  assumes ut: "stock u = Arr \<sigma> \<tau>" and vt: "stock v = Arr \<tau> Prop" and nt: "stock n = \<sigma>"
  shows "book_in_language logical_type logical_signature signature stock (NApp (NVar v) (NApp (NVar u) (NVar n))) Prop"
proof -
  have ul: "book_in_language logical_type logical_signature signature stock (NVar u) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff ut)
  have vl: "book_in_language logical_type logical_signature signature stock (NVar v) (Arr \<tau> Prop)"
    by (simp only: book_language_var_iff vt)
  have nl: "book_in_language logical_type logical_signature signature stock (NVar n) \<sigma>"
    by (simp only: book_language_var_iff nt)
  show ?thesis by (rule book_language_App[OF vl book_language_App[OF ul nl]])
qed

lemma book_argument_body_denote:
  assumes ut: "stock u = Arr \<sigma> \<tau>" and vt: "stock v = Arr \<tau> Prop" and nt: "stock n = \<sigma>"
    and typed: "book_env_typed domain stock g"
  shows "denote g (NApp (NVar v) (NApp (NVar u) (NVar n))) =
    app \<tau> Prop (g v) (app \<sigma> \<tau> (g u) (g n))"
proof -
  have ul: "book_in_language logical_type logical_signature signature stock (NVar u) (Arr \<sigma> \<tau>)"
    by (simp only: book_language_var_iff ut)
  have vl: "book_in_language logical_type logical_signature signature stock (NVar v) (Arr \<tau> Prop)"
    by (simp only: book_language_var_iff vt)
  have nl: "book_in_language logical_type logical_signature signature stock (NVar n) \<sigma>"
    by (simp only: book_language_var_iff nt)
  have inner_language: "book_in_language logical_type logical_signature signature stock (NApp (NVar u) (NVar n)) \<tau>"
    by (rule book_language_App[OF ul nl])
  have inner: "denote g (NApp (NVar u) (NVar n)) = app \<sigma> \<tau> (denote g (NVar u)) (denote g (NVar n))"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I ul nl typed])
  have outer: "denote g (NApp (NVar v) (NApp (NVar u) (NVar n))) =
    app \<tau> Prop (denote g (NVar v)) (denote g (NApp (NVar u) (NVar n)))"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I vl inner_language typed])
  have uvalue: "denote g (NVar u) = g u" by (rule denote_var[where n=u, OF UNIV_I typed])
  have vvalue: "denote g (NVar v) = g v" by (rule denote_var[where n=v, OF UNIV_I typed])
  have nvalue: "denote g (NVar n) = g n" by (rule denote_var[where n=n, OF UNIV_I typed])
  show ?thesis by (simp only: outer inner uvalue vvalue nvalue)
qed

lemma book_argument_test_from_names:
  assumes ut: "stock u = Arr \<sigma> \<tau>" and vt: "stock v = Arr \<tau> Prop" and nt: "stock n = \<sigma>"
    and uv: "u \<noteq> v" and un: "u \<noteq> n" and vn: "v \<noteq> n"
    and typed: "book_env_typed domain stock g"
    and function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and predicate_member: "P \<in> domain (Arr \<tau> Prop)"
  shows "\<exists>h \<in> domain (Arr \<sigma> Prop). \<forall>a \<in> domain \<sigma>.
    app \<sigma> Prop h a = app \<tau> Prop P (app \<sigma> \<tau> f a)"
proof -
  let ?body = "NApp (NVar v) (NApp (NVar u) (NVar n))"
  let ?g = "(g(u := f))(v := P)"
  let ?h = "denote ?g (NLam n ?body)"
  have f_at_name: "f \<in> domain (stock u)" by (simp only: ut; rule function_member)
  have P_at_name: "P \<in> domain (stock v)" by (simp only: vt; rule predicate_member)
  have updated: "book_env_typed domain stock ?g"
    by (rule book_env_update[OF book_env_update[OF typed f_at_name] P_at_name])
  have body_language: "book_in_language logical_type logical_signature signature stock ?body Prop"
    by (rule book_argument_body_language[OF ut vt nt])
  have lambda_language: "book_in_language logical_type logical_signature signature stock (NLam n ?body) (Arr (stock n) Prop)"
    by (rule book_language_Lam[OF body_language])
  have member: "?h \<in> domain (Arr \<sigma> Prop)"
    using denote_type[OF UNIV_I lambda_language updated] by (simp only: nt)
  have behaviour: "app \<sigma> Prop ?h a = app \<tau> Prop P (app \<sigma> \<tau> f a)" if am: "a \<in> domain \<sigma>" for a
  proof -
    have a_at_name: "a \<in> domain (stock n)" by (simp only: nt; rule am)
    have extended: "book_env_typed domain stock (?g(n := a))" by (rule book_env_update[OF updated a_at_name])
    have beta: "app \<sigma> Prop ?h a = denote (?g(n := a)) ?body"
      using book_full_lambda_application[OF body_language updated a_at_name] by (simp only: nt)
    have body_eval: "denote (?g(n := a)) ?body =
      app \<tau> Prop ((?g(n := a)) v) (app \<sigma> \<tau> ((?g(n := a)) u) ((?g(n := a)) n))"
      by (rule book_argument_body_denote[OF ut vt nt extended])
    have assigned: "denote (?g(n := a)) ?body = app \<tau> Prop P (app \<sigma> \<tau> f a)"
      using body_eval by (simp add: uv un vn)
    show ?thesis by (rule trans[OF beta assigned])
  qed
  have all_arguments: "\<forall>a \<in> domain \<sigma>. app \<sigma> Prop ?h a = app \<tau> Prop P (app \<sigma> \<tau> f a)"
    by (intro ballI, rule behaviour, assumption)
  show ?thesis by (rule bexI[where x="?h"]; fact)
qed

theorem book_argument_test_exists:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and function_member: "f \<in> domain (Arr \<sigma> \<tau>)" and predicate_member: "P \<in> domain (Arr \<tau> Prop)"
  shows "\<exists>h \<in> domain (Arr \<sigma> Prop). \<forall>a \<in> domain \<sigma>.
    app \<sigma> Prop h a = app \<tau> Prop P (app \<sigma> \<tau> f a)"
proof -
  obtain u where ut: "stock u = Arr \<sigma> \<tau>" by (rule sg_rich_variable[OF rich])
  have finite_u: "finite {u}" by simp
  obtain v where vt: "stock v = Arr \<tau> Prop" and vf: "v \<notin> {u}"
    using sg_rich_fresh[where \<sigma>="Arr \<tau> Prop", OF rich finite_u] by (elim exE conjE)
  have finite_uv: "finite {u,v}" by simp
  obtain n where nt: "stock n = \<sigma>" and nf: "n \<notin> {u,v}"
    using sg_rich_fresh[where \<sigma>=\<sigma>, OF rich finite_uv] by (elim exE conjE)
  have uv: "u \<noteq> v" and un: "u \<noteq> n" and vn: "v \<noteq> n" using vf nf by auto
  show ?thesis by (rule book_argument_test_from_names[OF ut vt nt uv un vn typed function_member predicate_member])
qed

end

end
