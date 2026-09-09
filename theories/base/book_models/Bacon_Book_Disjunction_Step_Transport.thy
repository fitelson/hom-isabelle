theory Bacon_Book_Disjunction_Step_Transport
  imports Bacon_Book_Disjunction_Binding_Transport Bacon_Book_Printed_Conversion
begin

section \<open>Printed β and η contractions are transported structurally\<close>

text \<open>
  β: (λx.M)N ↝ M[N/x], subject to the PRINTED free-for guard.
  Source: Bacon Definition 3.7, p.70, and the β/η definitions of
  pp.66–68; the cumulative primitive-∨ extension is §5.2, p.104.
  Printed β roots use literal substitution and printed free-for transport.
  η roots use free-variable preservation. The contextual induction then
  lifts these root maps through application and λ. These are raw
  contraction facts; no typing, proof-calculus or model premise is introduced.
  In particular, the raw decoder transports syntactic contractions even
  at wrong-type tags; this does not give a typed raw-conversion theorem.
\<close>

lemma book_disj_encode_printed_beta:
  assumes step: "book_printed_beta_contract A B"
  shows "book_printed_beta_contract (book_disj_encode A) (book_disj_encode B)"
  using step
proof (induction rule: book_printed_beta_contract.induct)
  case (beta N x M)
  have permitted: "book_printed_free_for (book_disj_encode N) x (book_disj_encode M)"
    by (simp only: book_disj_encode_printed_free_for; rule beta.hyps)
  show ?case by (simp only: book_disj_encode.simps book_disj_encode_subst;
    rule book_printed_beta_contract.beta[OF permitted])
qed

lemma book_disj_decode_printed_beta:
  assumes step: "book_printed_beta_contract A B"
  shows "book_printed_beta_contract (book_disj_decode A) (book_disj_decode B)"
  using step
proof (induction rule: book_printed_beta_contract.induct)
  case (beta N x M)
  have permitted: "book_printed_free_for (book_disj_decode N) x (book_disj_decode M)"
    by (simp only: book_disj_decode_printed_free_for; rule beta.hyps)
  show ?case by (simp only: book_disj_decode.simps book_disj_decode_subst;
    rule book_printed_beta_contract.beta[OF permitted])
qed

lemma book_disj_encode_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_disj_encode A) (book_disj_encode B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (book_disj_encode F)"
    by (simp only: book_disj_encode_fv; rule eta.hyps)
  show ?case by (simp only: book_disj_encode.simps; rule named_eta_contract.eta[OF fresh])
qed

lemma book_disj_decode_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_disj_decode A) (book_disj_decode B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (book_disj_decode F)"
    by (simp only: book_disj_decode_fv; rule eta.hyps)
  show ?case by (simp only: book_disj_decode.simps; rule named_eta_contract.eta[OF fresh])
qed

lemma book_disj_encode_compatible:
  fixes R :: "'c book_disj_term \<Rightarrow> 'c book_disj_term \<Rightarrow> bool"
    and Q :: "('c + unit) book_conj_term \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> bool"
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> Q (book_disj_encode X) (book_disj_encode Y)"
  shows "named_compatible_step Q (book_disj_encode A) (book_disj_encode B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case root
  show ?case by (rule named_compatible_step.root, rule roots, rule root.hyps)
next
  case App_left
  show ?case by (simp only: book_disj_encode.simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case by (simp only: book_disj_encode.simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case by (simp only: book_disj_encode.simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma book_disj_decode_compatible:
  fixes R :: "('c + unit) book_conj_term \<Rightarrow> ('c + unit) book_conj_term \<Rightarrow> bool"
    and Q :: "'c book_disj_term \<Rightarrow> 'c book_disj_term \<Rightarrow> bool"
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> Q (book_disj_decode X) (book_disj_decode Y)"
  shows "named_compatible_step Q (book_disj_decode A) (book_disj_decode B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case root
  show ?case by (rule named_compatible_step.root, rule roots, rule root.hyps)
next
  case App_left
  show ?case by (simp only: book_disj_decode.simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case by (simp only: book_disj_decode.simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case by (simp only: book_disj_decode.simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma book_disj_encode_printed_beta_step:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
  shows "named_compatible_step book_printed_beta_contract (book_disj_encode A) (book_disj_encode B)"
  by (rule book_disj_encode_compatible[OF step], rule book_disj_encode_printed_beta, assumption)

lemma book_disj_decode_printed_beta_step:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
  shows "named_compatible_step book_printed_beta_contract (book_disj_decode A) (book_disj_decode B)"
  by (rule book_disj_decode_compatible[OF step], rule book_disj_decode_printed_beta, assumption)

lemma book_disj_encode_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (book_disj_encode A) (book_disj_encode B)"
  by (rule book_disj_encode_compatible[OF step], rule book_disj_encode_eta, assumption)

lemma book_disj_decode_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (book_disj_decode A) (book_disj_decode B)"
  by (rule book_disj_decode_compatible[OF step], rule book_disj_decode_eta, assumption)

end
