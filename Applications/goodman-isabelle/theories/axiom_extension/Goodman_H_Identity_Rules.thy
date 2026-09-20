theory Goodman_H_Identity_Rules
  imports Goodman_H_Certificate_Interface
begin

section \<open>Reflexivity and Leibniz's law use Leibniz equivalence, not HOL equality\<close>

theorem gi_book_H_Ref:
  fixes \<Sigma> :: "'c ssignature" and A :: "'c book_named_term"
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
  shows "book_H \<Sigma> G (book_leibniz G \<sigma> A A)"
proof (rule gi_H_validity_certificate[OF rich book_leibniz_language[OF rich al al]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
  assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
  have member: "J g A \<in> D \<sigma>" by (rule M.denote_type[OF UNIV_I al typed])
  show "V (J g (book_leibniz G \<sigma> A A))"
    by (simp only: M.book_leibniz_truth[OF rich typed al al]; rule book_leibniz_refl; rule member)
qed

theorem gi_book_H_LL:
  fixes \<Sigma> :: "'c ssignature" and A B F :: "'c book_named_term"
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
  shows "book_H \<Sigma> G (book_imp (book_leibniz G \<sigma> A B) (book_imp (NApp F A) (NApp F B)))"
proof -
  have el: "book_theory_formula \<Sigma> G (book_leibniz G \<sigma> A B)" by (rule book_leibniz_language[OF rich al bl])
  have fal: "book_theory_formula \<Sigma> G (NApp F A)" by (rule book_language_App[OF fl al])
  have fbl: "book_theory_formula \<Sigma> G (NApp F B)" by (rule book_language_App[OF fl bl])
  have tail: "book_theory_formula \<Sigma> G (book_imp (NApp F A) (NApp F B))" by (rule book_imp_language[OF fal fbl])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_imp_language[OF el tail]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have fm: "J g F \<in> D (Arr \<sigma> Prop)" by (rule M.denote_type[OF UNIV_I fl typed])
    have test: "book_leibniz_equiv D app V \<sigma> (J g A) (J g B) \<Longrightarrow>
      V (app \<sigma> Prop (J g F) (J g A)) = V (app \<sigma> Prop (J g F) (J g B))"
      by (rule book_leibniz_test; (assumption | rule fm))
    show "V (J g (book_imp (book_leibniz G \<sigma> A B) (book_imp (NApp F A) (NApp F B))))"
      by (simp only: M.book_imp_truth[OF typed el tail] M.book_imp_truth[OF typed fal fbl]
        M.book_leibniz_truth[OF rich typed al bl]
        M.denote_app[OF UNIV_I UNIV_I UNIV_I fl al typed]
        M.denote_app[OF UNIV_I UNIV_I UNIV_I fl bl typed];
        use test in blast)
  qed
qed

theorem gi_book_H_Exists_Ref:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (book_exists G n (book_leibniz G (G n) (NVar n) (NVar n)))"
proof -
  have vl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) (G n)"
    by (rule book_language_Var)
  have el: "book_theory_formula \<Sigma> G (book_leibniz G (G n) (NVar n) (NVar n))"
    by (rule book_leibniz_language[OF rich vl vl])
  show ?thesis
  proof (rule gi_H_validity_certificate[OF rich book_exists_language[OF rich el]])
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V c g
    assume model: "book_full_minimal_model D app \<Sigma> G J V c" and typed: "book_env_typed D G g"
    interpret M: book_full_minimal_model D app \<Sigma> G J V c by (rule model)
    have member: "g n \<in> D (G n)" using typed unfolding book_env_typed_def by blast
    have eq_true: "V (J g (book_leibniz G (G n) (NVar n) (NVar n)))"
      by (simp only: M.book_leibniz_truth[OF rich typed vl vl] M.denote_var[OF UNIV_I typed];
        rule book_leibniz_refl; rule member)
    have witness: "\<exists>a\<in>D (G n). V (J (g(n := a)) (book_leibniz G (G n) (NVar n) (NVar n)))"
    proof (rule bexI[where x="g n"])
      show "V (J (g(n := g n)) (book_leibniz G (G n) (NVar n) (NVar n)))"
        by (simp only: fun_upd_triv; rule eq_true)
      show "g n \<in> D (G n)" by (rule member)
    qed
    show "V (J g (book_exists G n (book_leibniz G (G n) (NVar n) (NVar n))))"
      by (simp only: M.book_exists_truth[OF rich typed el]; rule witness)
  qed
qed

section \<open>Transfer the three constructor schemas\<close>

theorem gi_H_Ref:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<sigma>"
    and chart: "map G ns = \<Gamma>" and constants: "gi_constants_admitted k \<Sigma> A"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Eq \<sigma> A A))"
  using gi_book_H_Ref[OF rich gi_to_book_language[OF rich typed chart constants]]
  by (simp only: gi_to_book.simps)

theorem gi_H_LL:
  assumes rich: "sg_rich G"
    and a: "\<Gamma> \<turnstile> A : \<sigma>" and b: "\<Gamma> \<turnstile> B : \<sigma>" and f: "\<Gamma> \<turnstile> F : Arr \<sigma> Prop"
    and chart: "map G ns = \<Gamma>"
    and ac: "gi_constants_admitted k \<Sigma> A" and bc: "gi_constants_admitted k \<Sigma> B"
    and fc: "gi_constants_admitted k \<Sigma> F"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))))"
  using gi_book_H_LL[OF rich gi_to_book_language[OF rich a chart ac]
    gi_to_book_language[OF rich b chart bc] gi_to_book_language[OF rich f chart fc]]
  by (simp only: gi_to_book.simps)

theorem gi_H_IndividualExistence:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G (gi_to_book G ns k (Exists Ind (Eq Ind (Var 0) (Var 0))))"
  using gi_book_H_Exists_Ref[OF rich, where n="named_chart_fresh G ns Ind" and \<Sigma>=\<Sigma>]
  by (simp only: gi_to_book.simps Let_def nth_Cons_0 named_chart_fresh_type[OF rich])

end
