theory Goodman_Constructor_Translation
  imports Goodman_Book_Axiom_Packages
begin

section \<open>From the constructor syntax to the book's named terms\<close>

text \<open>
  The list ns names the de Bruijn slots, in order. At a binder we choose
  a new variable of the required type, outside that list. The map k
  translates typed nonlogical names. Membership of EVERY translated
  constant in the declared target signature is an explicit premise.
  This file proves language preservation, not preservation of H or CEV+
  derivations, βη conversion, denotation, or the closed-logical stock.
  In particular the older truth term is translated literally; it is not
  silently replaced by book_top.
\<close>

fun gi_constants_admitted where
  "gi_constants_admitted k \<Sigma> (Var n) = True"
| "gi_constants_admitted k \<Sigma> (Const c \<sigma>) = (k c \<sigma> \<in> \<Sigma> \<sigma>)"
| "gi_constants_admitted k \<Sigma> (App F A) = (gi_constants_admitted k \<Sigma> F \<and> gi_constants_admitted k \<Sigma> A)"
| "gi_constants_admitted k \<Sigma> (Lam \<sigma> A) = gi_constants_admitted k \<Sigma> A"
| "gi_constants_admitted k \<Sigma> (Eq \<sigma> A B) = (gi_constants_admitted k \<Sigma> A \<and> gi_constants_admitted k \<Sigma> B)"
| "gi_constants_admitted k \<Sigma> (Neg A) = gi_constants_admitted k \<Sigma> A"
| "gi_constants_admitted k \<Sigma> (Conj A B) = (gi_constants_admitted k \<Sigma> A \<and> gi_constants_admitted k \<Sigma> B)"
| "gi_constants_admitted k \<Sigma> (Disj A B) = (gi_constants_admitted k \<Sigma> A \<and> gi_constants_admitted k \<Sigma> B)"
| "gi_constants_admitted k \<Sigma> (Imp A B) = (gi_constants_admitted k \<Sigma> A \<and> gi_constants_admitted k \<Sigma> B)"
| "gi_constants_admitted k \<Sigma> (Forall \<sigma> A) = gi_constants_admitted k \<Sigma> A"
| "gi_constants_admitted k \<Sigma> (Exists \<sigma> A) = gi_constants_admitted k \<Sigma> A"

fun gi_to_book ::
  "sgcontext \<Rightarrow> nat list \<Rightarrow> (string \<Rightarrow> otype \<Rightarrow> 'c) \<Rightarrow> oterm \<Rightarrow> 'c book_named_term" where
  "gi_to_book G ns k (Var n) = NVar (ns ! n)"
| "gi_to_book G ns k (Const c \<sigma>) = NConst (k c \<sigma>) \<sigma>"
| "gi_to_book G ns k (App F A) = NApp (gi_to_book G ns k F) (gi_to_book G ns k A)"
| "gi_to_book G ns k (Lam \<sigma> A) =
    (let n = named_chart_fresh G ns \<sigma> in NLam n (gi_to_book G (n # ns) k A))"
| "gi_to_book G ns k (Eq \<sigma> A B) = book_leibniz G \<sigma> (gi_to_book G ns k A) (gi_to_book G ns k B)"
| "gi_to_book G ns k (Neg A) = book_not G (gi_to_book G ns k A)"
| "gi_to_book G ns k (Conj A B) = book_and G (gi_to_book G ns k A) (gi_to_book G ns k B)"
| "gi_to_book G ns k (Disj A B) = book_or G (gi_to_book G ns k A) (gi_to_book G ns k B)"
| "gi_to_book G ns k (Imp A B) = book_imp (gi_to_book G ns k A) (gi_to_book G ns k B)"
| "gi_to_book G ns k (Forall \<sigma> A) =
    (let n = named_chart_fresh G ns \<sigma> in book_all G n (gi_to_book G (n # ns) k A))"
| "gi_to_book G ns k (Exists \<sigma> A) =
    (let n = named_chart_fresh G ns \<sigma> in book_exists G n (gi_to_book G (n # ns) k A))"

lemma gi_chart_extension:
  "sg_rich G \<Longrightarrow> map G ns = \<Gamma> \<Longrightarrow>
    map G (named_chart_fresh G ns \<sigma> # ns) = \<sigma> # \<Gamma>"
  by (simp add: named_chart_fresh_type)

lemma gi_chart_variable:
  assumes chart: "map G ns = \<Gamma>" and typed: "lookup \<Gamma> i = Some \<sigma>"
  shows "G (ns ! i) = \<sigma>"
  using typed unfolding chart[symmetric] lookup_def
  by (auto split: if_splits)

theorem gi_to_book_language:
  assumes rich: "sg_rich G" and typed: "\<Gamma> \<turnstile> A : \<tau>"
    and chart: "map G ns = \<Gamma>" and constants: "gi_constants_admitted k \<Sigma> A"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (gi_to_book G ns k A) \<tau>"
  using typed chart constants
proof (induction arbitrary: ns rule: has_type.induct)
  case Var
  show ?case by (simp only: gi_to_book.simps book_language_var_iff;
    rule gi_chart_variable[OF Var.prems(1) Var.hyps, symmetric])
next
  case Const
  then show ?case by (simp add: book_language_const_iff)
next
  case App
  then show ?case by (auto intro: book_language_App)
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have body: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (gi_to_book G (?n # ns) k A) \<tau>"
    by (rule Lam.IH[OF gi_chart_extension[OF rich Lam.prems(1)]];
      use Lam.prems(2) in simp)
  have abstraction: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLam ?n (gi_to_book G (?n # ns) k A)) (Arr (G ?n) \<tau>)"
    by (rule book_language_Lam[OF body])
  show ?case using abstraction by (simp add: Let_def named_chart_fresh_type[OF rich])
next
  case Eq
  then show ?case by (auto intro: book_leibniz_language[OF rich])
next
  case Neg
  then show ?case by (auto intro: book_not_language[OF rich])
next
  case Conj
  then show ?case by (auto intro: book_and_language[OF rich])
next
  case Disj
  then show ?case by (auto intro: book_or_language[OF rich])
next
  case Imp
  then show ?case by (auto intro: book_imp_language)
next
  case (Forall \<sigma> \<Gamma> A)
  have body: "book_theory_formula \<Sigma> G (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k A)"
    by (rule Forall.IH[OF gi_chart_extension[OF rich Forall.prems(1)]];
      use Forall.prems(2) in simp)
  show ?case by (simp only: gi_to_book.simps Let_def; rule book_all_language[OF body])
next
  case (Exists \<sigma> \<Gamma> A)
  have body: "book_theory_formula \<Sigma> G (gi_to_book G (named_chart_fresh G ns \<sigma> # ns) k A)"
    by (rule Exists.IH[OF gi_chart_extension[OF rich Exists.prems(1)]];
      use Exists.prems(2) in simp)
  show ?case by (simp only: gi_to_book.simps Let_def; rule book_exists_language[OF rich body])
qed

lemma gi_binder_chart_distinct:
  "sg_rich G \<Longrightarrow> distinct ns \<Longrightarrow>
    distinct (named_chart_fresh G ns \<sigma> # ns)"
  by (simp add: named_chart_fresh_notin)

text \<open>
  The next regression is only the binder-free PP formula. It uses the
  exact raw shape of pp_target_PP in the old Bacon_PP_Question theory.
  The old theory is not imported, so this is not a theorem about that
  named constant and is not a T6 transport theorem.
\<close>

lemma gi_target_PP_shape:
  assumes names: "\<And>\<tau>. k ''Pure'' \<tau> = PureName"
  shows "gi_to_book G ns k
    (App (Const ''Pure'' (Arr (Arr gb_unary Prop) Prop))
      (Const ''Pure'' (Arr gb_unary Prop))) = gb_target_PP"
  by (simp add: names gb_target_PP_def gb_purity_of_pure_def gb_pure_def gb_Pure_def)

end
