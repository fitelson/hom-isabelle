theory Bacon_Book_Printed_Conversion_Contexts
  imports Bacon_Book_Printed_Conversion
begin

section \<open>Printed conversion is stable under typed term contexts\<close>

text \<open>
  From A≡βηB derive λn.A≡βηλn.B. Conversion in either position
  of a typed application also preserves conversion of the whole term.
  Every intermediate node receives a new language guard by the matching
  formation rule. The proof is an induction on book_printed_conversion
  itself: no α rule, source-reduction chain, or older conversion result
  supplies any step.
\<close>

lemma book_printed_conversion_context:
  fixes f :: "('c,'l) named_term \<Rightarrow> ('c,'l) named_term"
  assumes conversion: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
    and language_map: "\<And>X. book_in_language L \<Lambda> \<Sigma> G X \<tau> \<Longrightarrow>
      book_in_language L \<Lambda> \<Sigma> G (f X) \<rho>"
    and beta_context: "\<And>X Y. named_compatible_step book_printed_beta_contract X Y \<Longrightarrow>
      named_compatible_step book_printed_beta_contract (f X) (f Y)"
    and eta_context: "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
      named_compatible_step named_eta_contract (f X) (f Y)"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<rho> (f A) (f B)"
  using conversion language_map
proof (induction rule: book_printed_conversion.induct)
  case (Refl A \<tau>)
  show ?case by (rule book_printed_conversion.Refl[OF Refl.prems[OF Refl.hyps]])
next
  case (PrintedBeta A \<tau> B)
  have left: "book_in_language L \<Lambda> \<Sigma> G (f A) \<rho>" by (rule PrintedBeta.prems[OF PrintedBeta.hyps(1)])
  have right: "book_in_language L \<Lambda> \<Sigma> G (f B) \<rho>" by (rule PrintedBeta.prems[OF PrintedBeta.hyps(2)])
  have step: "named_compatible_step book_printed_beta_contract (f A) (f B)"
    by (rule beta_context[where X=A and Y=B, OF PrintedBeta.hyps(3)])
  show ?case by (rule book_printed_conversion.PrintedBeta[OF left right step])
next
  case (Eta A \<tau> B)
  have left: "book_in_language L \<Lambda> \<Sigma> G (f A) \<rho>" by (rule Eta.prems[OF Eta.hyps(1)])
  have right: "book_in_language L \<Lambda> \<Sigma> G (f B) \<rho>" by (rule Eta.prems[OF Eta.hyps(2)])
  have step: "named_compatible_step named_eta_contract (f A) (f B)"
    by (rule eta_context[where X=A and Y=B, OF Eta.hyps(3)])
  show ?case by (rule book_printed_conversion.Eta[OF left right step])
next
  case (Sym \<tau> A B)
  show ?case by (rule book_printed_conversion.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<tau> A B C)
  show ?case by (rule book_printed_conversion.Trans[
    OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma book_printed_conversion_Lam:
  assumes conversion: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> A B"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G (Arr (G n) \<tau>) (NLam n A) (NLam n B)"
proof (rule book_printed_conversion_context[where f="NLam n", OF conversion])
  show "\<And>X. book_in_language L \<Lambda> \<Sigma> G X \<tau> \<Longrightarrow>
    book_in_language L \<Lambda> \<Sigma> G (NLam n X) (Arr (G n) \<tau>)"
    by (rule book_language_Lam)
next
  show "\<And>X Y. named_compatible_step book_printed_beta_contract X Y \<Longrightarrow>
    named_compatible_step book_printed_beta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body)
qed

lemma book_printed_conversion_App_left:
  assumes conversion: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr \<sigma> \<tau>) F H"
    and argument: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> (NApp F A) (NApp H A)"
proof (rule book_printed_conversion_context[where f="\<lambda>X. NApp X A", OF conversion])
  show "\<And>X. book_in_language L \<Lambda> \<Sigma> G X (Arr \<sigma> \<tau>) \<Longrightarrow>
    book_in_language L \<Lambda> \<Sigma> G (NApp X A) \<tau>"
    by (rule book_language_App[OF _ argument])
next
  show "\<And>X Y. named_compatible_step book_printed_beta_contract X Y \<Longrightarrow>
    named_compatible_step book_printed_beta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left)
qed

lemma book_printed_conversion_App_right:
  assumes head: "book_in_language L \<Lambda> \<Sigma> G F (Arr \<sigma> \<tau>)"
    and conversion: "book_printed_conversion L \<Lambda> \<Sigma> G \<sigma> A B"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> (NApp F A) (NApp F B)"
proof (rule book_printed_conversion_context[where f="NApp F", OF conversion])
  show "\<And>X. book_in_language L \<Lambda> \<Sigma> G X \<sigma> \<Longrightarrow>
    book_in_language L \<Lambda> \<Sigma> G (NApp F X) \<tau>"
    by (rule book_language_App[OF head])
next
  show "\<And>X Y. named_compatible_step book_printed_beta_contract X Y \<Longrightarrow>
    named_compatible_step book_printed_beta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right)
qed

lemma book_printed_conversion_App:
  assumes head: "book_printed_conversion L \<Lambda> \<Sigma> G (Arr \<sigma> \<tau>) F H"
    and argument: "book_printed_conversion L \<Lambda> \<Sigma> G \<sigma> A B"
  shows "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> (NApp F A) (NApp H B)"
proof -
  have al: "book_in_language L \<Lambda> \<Sigma> G A \<sigma>"
    by (rule conjunct1[OF book_printed_conversion_languages[OF argument]])
  have hl: "book_in_language L \<Lambda> \<Sigma> G H (Arr \<sigma> \<tau>)"
    by (rule conjunct2[OF book_printed_conversion_languages[OF head]])
  have left: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> (NApp F A) (NApp H A)"
    by (rule book_printed_conversion_App_left[OF head al])
  have right: "book_printed_conversion L \<Lambda> \<Sigma> G \<tau> (NApp H A) (NApp H B)"
    by (rule book_printed_conversion_App_right[OF hl argument])
  show ?thesis by (rule book_printed_conversion.Trans[OF left right])
qed

end
