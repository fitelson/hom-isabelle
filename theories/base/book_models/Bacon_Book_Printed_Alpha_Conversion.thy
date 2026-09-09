theory Bacon_Book_Printed_Alpha_Conversion
  imports Bacon_Book_Printed_Alpha_Alignment
begin

section \<open>α is derivable without an α constructor\<close>

text \<open>
  A≡αB gives printed βη conversion whenever A belongs to the declared
  language. Induction over the independent α generators uses the freshly
  replayed binder theorem. No exact-capture β conversion theorem supplies
  any conversion conclusion. This is the noncircular α prerequisite for
  the printed Chapter 5 calculus correspondence.
\<close>

theorem book_alpha_implies_printed_conversion:
  assumes alpha: "named_alpha G A B"
    and language: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  using alpha language
proof (induction arbitrary: \<tau> rule: named_alpha.induct)
  case Refl
  show ?case by (rule book_printed_conversion.Refl[OF Refl.prems])
next
  case (Fresh_Binder x y A)
  obtain \<rho> where ty: "\<tau> = Arr (G x) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_Lam_obtain[OF Fresh_Binder.prems]; rule that; assumption)
  show ?case unfolding ty by (rule book_printed_fresh_binder_conversion[OF body Fresh_Binder.hyps])
next
  case (App F H A B)
  obtain \<sigma> where fn: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF App.prems]; rule that; assumption)
  show ?case by (rule book_printed_conversion_App[OF App.IH(1)[OF fn] App.IH(2)[OF argument]])
next
  case (Lam A B n)
  obtain \<rho> where ty: "\<tau> = Arr (G n) \<rho>"
    and body: "book_in_language L \<Lambda> \<Sigma> G A \<rho>"
    by (rule book_language_Lam_obtain[OF Lam.prems]; rule that; assumption)
  show ?case unfolding ty by (rule book_printed_conversion_Lam[OF Lam.IH[OF body]])
next
  case (Sym A B)
  have left: "book_in_language L \<Lambda> \<Sigma> G A \<tau>"
    by (rule iffD2[OF book_alpha_language_iff[OF Sym.hyps] Sym.prems])
  show ?case by (rule book_printed_conversion.Sym[OF Sym.IH[OF left]])
next
  case (Trans A B C)
  have first: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
    by (rule Trans.IH(1)[OF Trans.prems])
  have middle: "book_in_language L \<Lambda> \<Sigma> G B \<tau>"
    by (rule conjunct2[OF book_printed_conversion_languages[OF first]])
  have second: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> B C"
    by (rule Trans.IH(2)[OF middle])
  show ?case by (rule book_printed_conversion.Trans[OF first second])
qed

end
