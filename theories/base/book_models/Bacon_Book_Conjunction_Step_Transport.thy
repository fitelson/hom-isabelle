theory Bacon_Book_Conjunction_Step_Transport
  imports Bacon_Book_Conjunction_Binding_Transport Bacon_Book_Printed_Conversion
begin

section \<open>Printed β and η contractions are transported structurally\<close>

text \<open>
  Printed β roots use the exact substitution and free-for transport.
  η roots use free-variable preservation. The contextual induction then
  lifts these root maps through application and λ. These are raw
  contraction facts; no proof-calculus or model premise is introduced.
\<close>

lemma book_conj_encode_printed_beta:
  assumes step: "book_printed_beta_contract A B"
  shows "book_printed_beta_contract (book_conj_encode A) (book_conj_encode B)"
  using step
proof (induction rule: book_printed_beta_contract.induct)
  case (beta N x M)
  have permitted: "book_printed_free_for (book_conj_encode N) x (book_conj_encode M)"
    by (simp only: book_conj_encode_printed_free_for; rule beta.hyps)
  show ?case by (simp only: book_conj_encode.simps book_conj_encode_subst;
    rule book_printed_beta_contract.beta[OF permitted])
qed

lemma book_conj_decode_printed_beta:
  assumes step: "book_printed_beta_contract A B"
  shows "book_printed_beta_contract (book_conj_decode A) (book_conj_decode B)"
  using step
proof (induction rule: book_printed_beta_contract.induct)
  case (beta N x M)
  have permitted: "book_printed_free_for (book_conj_decode N) x (book_conj_decode M)"
    by (simp only: book_conj_decode_printed_free_for; rule beta.hyps)
  show ?case by (simp only: book_conj_decode.simps book_conj_decode_subst;
    rule book_printed_beta_contract.beta[OF permitted])
qed

lemma book_conj_encode_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_conj_encode A) (book_conj_encode B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (book_conj_encode F)"
    by (simp only: book_conj_encode_fv; rule eta.hyps)
  show ?case by (simp only: book_conj_encode.simps; rule named_eta_contract.eta[OF fresh])
qed

lemma book_conj_decode_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_conj_decode A) (book_conj_decode B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (book_conj_decode F)"
    by (simp only: book_conj_decode_fv; rule eta.hyps)
  show ?case by (simp only: book_conj_decode.simps; rule named_eta_contract.eta[OF fresh])
qed

lemma book_conj_encode_compatible:
  fixes R :: "'c book_conj_term \<Rightarrow> 'c book_conj_term \<Rightarrow> bool"
    and Q :: "('c + unit) book_named_term \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> bool"
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> Q (book_conj_encode X) (book_conj_encode Y)"
  shows "named_compatible_step Q (book_conj_encode A) (book_conj_encode B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case root
  show ?case by (rule named_compatible_step.root, rule roots, rule root.hyps)
next
  case App_left
  show ?case by (simp only: book_conj_encode.simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case by (simp only: book_conj_encode.simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case by (simp only: book_conj_encode.simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma book_conj_decode_compatible:
  fixes R :: "('c + unit) book_named_term \<Rightarrow> ('c + unit) book_named_term \<Rightarrow> bool"
    and Q :: "'c book_conj_term \<Rightarrow> 'c book_conj_term \<Rightarrow> bool"
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>X Y. R X Y \<Longrightarrow> Q (book_conj_decode X) (book_conj_decode Y)"
  shows "named_compatible_step Q (book_conj_decode A) (book_conj_decode B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case root
  show ?case by (rule named_compatible_step.root, rule roots, rule root.hyps)
next
  case App_left
  show ?case by (simp only: book_conj_decode.simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case by (simp only: book_conj_decode.simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case by (simp only: book_conj_decode.simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma book_conj_encode_printed_beta_step:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
  shows "named_compatible_step book_printed_beta_contract (book_conj_encode A) (book_conj_encode B)"
  by (rule book_conj_encode_compatible[OF step], rule book_conj_encode_printed_beta, assumption)

lemma book_conj_decode_printed_beta_step:
  assumes step: "named_compatible_step book_printed_beta_contract A B"
  shows "named_compatible_step book_printed_beta_contract (book_conj_decode A) (book_conj_decode B)"
  by (rule book_conj_decode_compatible[OF step], rule book_conj_decode_printed_beta, assumption)

lemma book_conj_encode_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (book_conj_encode A) (book_conj_encode B)"
  by (rule book_conj_encode_compatible[OF step], rule book_conj_encode_eta, assumption)

lemma book_conj_decode_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (book_conj_decode A) (book_conj_decode B)"
  by (rule book_conj_decode_compatible[OF step], rule book_conj_decode_eta, assumption)

end
