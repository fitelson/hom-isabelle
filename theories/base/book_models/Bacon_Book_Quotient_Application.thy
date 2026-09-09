theory Bacon_Book_Quotient_Application
  imports Bacon_Book_Leibniz_Classes Bacon_Book_Leibniz_Application
begin

section \<open>Typed application on Leibniz classes\<close>

text \<open>
  Define App̄στ(X,Y) = [Appστ(rep X,rep Y)]τ on the quotient domains.
  Every legitimate class has a representative of its original type, so
  the result belongs to the required quotient domain. If application
  respects Leibniz equivalence, the definition satisfies
  App̄στ([f]σ→τ,[a]σ) = [Appστ(f,a)]τ, independently of representatives.

  This is the applicative-structure part of Bacon's Proposition 15.5,
  p.322. Full book environments with a rich stock and a typed assignment
  now supply the congruence premise by proof. A quotient interpretation,
  logical valuation clauses, and Leibnizian separation are still separate
  obligations; the typed structure alone is not called a logical model.
\<close>

definition book_leibniz_quotient_app where
  "book_leibniz_quotient_app D app V \<sigma> \<tau> F A =
    book_leibniz_class D app V \<tau> (app \<sigma> \<tau> (book_leibniz_rep F) (book_leibniz_rep A))"

context book_applicative_structure
begin

lemma book_leibniz_quotient_app_type:
  assumes head: "F \<in> book_leibniz_quotient_domain domain app V (Arr \<sigma> \<tau>)"
    and argument: "A \<in> book_leibniz_quotient_domain domain app V \<sigma>"
  shows "book_leibniz_quotient_app domain app V \<sigma> \<tau> F A \<in>
    book_leibniz_quotient_domain domain app V \<tau>"
proof -
  have ft: "book_leibniz_rep F \<in> domain (Arr \<sigma> \<tau>)"
    by (rule book_leibniz_rep_type[OF head])
  have at: "book_leibniz_rep A \<in> domain \<sigma>"
    by (rule book_leibniz_rep_type[OF argument])
  have result: "app \<sigma> \<tau> (book_leibniz_rep F) (book_leibniz_rep A) \<in> domain \<tau>"
    by (rule app_type[OF ft at])
  show ?thesis unfolding book_leibniz_quotient_app_def
    by (rule book_leibniz_quotient_domainI[where D=domain and \<sigma>=\<tau>, OF result])
qed

theorem book_leibniz_quotient_applicative_structure:
  "book_applicative_structure (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V)"
  by unfold_locales (rule book_leibniz_quotient_app_type; assumption)

lemma book_leibniz_quotient_projection_from_congruence:
  assumes head: "f \<in> domain (Arr \<sigma> \<tau>)" and argument: "a \<in> domain \<sigma>"
    and compatible: "\<And>f g a b.
      book_leibniz_equiv domain app V (Arr \<sigma> \<tau>) f g \<Longrightarrow>
      book_leibniz_equiv domain app V \<sigma> a b \<Longrightarrow>
      book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g b)"
  shows "book_leibniz_quotient_app domain app V \<sigma> \<tau>
    (book_leibniz_class domain app V (Arr \<sigma> \<tau>) f)
    (book_leibniz_class domain app V \<sigma> a) =
    book_leibniz_class domain app V \<tau> (app \<sigma> \<tau> f a)"
proof -
  have fr: "book_leibniz_equiv domain app V (Arr \<sigma> \<tau>)
    (book_leibniz_rep (book_leibniz_class domain app V (Arr \<sigma> \<tau>) f)) f"
    by (rule book_leibniz_rep_equiv[where D=domain and \<sigma>="Arr \<sigma> \<tau>", OF head])
  have ar: "book_leibniz_equiv domain app V \<sigma>
    (book_leibniz_rep (book_leibniz_class domain app V \<sigma> a)) a"
    by (rule book_leibniz_rep_equiv[where D=domain and \<sigma>=\<sigma>, OF argument])
  have results: "book_leibniz_equiv domain app V \<tau>
    (app \<sigma> \<tau> (book_leibniz_rep (book_leibniz_class domain app V (Arr \<sigma> \<tau>) f))
      (book_leibniz_rep (book_leibniz_class domain app V \<sigma> a))) (app \<sigma> \<tau> f a)"
    by (rule compatible[OF fr ar])
  show ?thesis unfolding book_leibniz_quotient_app_def by (rule book_leibniz_class_eq[OF results])
qed

end

context book_full_environment
begin

theorem book_leibniz_quotient_application_projection:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and head: "f \<in> domain (Arr \<sigma> \<tau>)" and argument: "a \<in> domain \<sigma>"
  shows "book_leibniz_quotient_app domain app V \<sigma> \<tau>
    (book_leibniz_class domain app V (Arr \<sigma> \<tau>) f)
    (book_leibniz_class domain app V \<sigma> a) =
    book_leibniz_class domain app V \<tau> (app \<sigma> \<tau> f a)"
proof (rule book_leibniz_quotient_projection_from_congruence[OF head argument])
  fix f g a b
  assume heads: "book_leibniz_equiv domain app V (Arr \<sigma> \<tau>) f g"
    and arguments: "book_leibniz_equiv domain app V \<sigma> a b"
  show "book_leibniz_equiv domain app V \<tau> (app \<sigma> \<tau> f a) (app \<sigma> \<tau> g b)"
    by (rule book_leibniz_application_cong[OF rich typed heads arguments])
qed

end

end
