theory Bacon_Source_Relational_Conversion_Congruence
  imports Bacon_Source_Relational_Conversion Bacon_Source_Relational_Binder_Vectors
begin

section \<open>Context lifting for the independent typed R conversion\<close>

text \<open>
  The following proofs lift every intermediate term and every contextual
  β or η step, not merely the endpoints. Typing premises therefore keep
  the entire chain in R. No signature is imposed on raw intermediates.
  There is no appeal to F conversion, a proof judgment, or semantics.
  Source role: contextual βη conversion, §1.1 p.5 and Appendix A.2.
\<close>

lemma paper_R_raw_beta_eta_context:
  fixes C :: "'c paper_named_term \<Rightarrow> 'c paper_named_term"
  assumes conversion: "paper_R_raw_beta_eta G \<sigma> A B"
    and typing: "\<And>X. paper_R_has_type G X \<sigma> \<Longrightarrow> paper_R_has_type G (C X) \<tau>"
    and beta: "\<And>X Y. named_compatible_step named_beta_contract X Y \<Longrightarrow>
      named_compatible_step named_beta_contract (C X) (C Y)"
    and eta: "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
      named_compatible_step named_eta_contract (C X) (C Y)"
  shows "paper_R_raw_beta_eta G \<tau> (C A) (C B)"
  using conversion typing beta eta
proof (induction arbitrary: C \<tau> rule: paper_R_raw_beta_eta.induct)
  case Refl
  show ?case by (rule paper_R_raw_beta_eta.Refl[OF Refl.prems(1)[OF Refl.hyps]])
next
  case Beta
  show ?case by (rule paper_R_raw_beta_eta.Beta[
    OF Beta.prems(1)[OF Beta.hyps(1)] Beta.prems(1)[OF Beta.hyps(2)]
      Beta.prems(2)[OF Beta.hyps(3)]])
next
  case Eta
  show ?case by (rule paper_R_raw_beta_eta.Eta[
    OF Eta.prems(1)[OF Eta.hyps(1)] Eta.prems(1)[OF Eta.hyps(2)]
      Eta.prems(3)[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule paper_R_raw_beta_eta.Sym[OF Sym.IH[OF Sym.prems]])
next
  case Trans
  show ?case by (rule paper_R_raw_beta_eta.Trans[
    OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma paper_R_raw_beta_eta_App_left:
  fixes A :: "'c paper_named_term"
  assumes conversion: "paper_R_raw_beta_eta G (Arr \<sigma> \<tau>) F H"
    and argument: "paper_R_has_type G A \<sigma>"
  shows "paper_R_raw_beta_eta G \<tau> (NApp F A) (NApp H A)"
proof (rule paper_R_raw_beta_eta_context[where C="\<lambda>X. NApp X A", OF conversion])
  fix X :: "'c paper_named_term"
  assume head: "paper_R_has_type G X (Arr \<sigma> \<tau>)"
  show "paper_R_has_type G (NApp X A) \<tau>" by (rule paper_R_has_type.App[OF head argument])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_beta_contract X Y"
  show "named_compatible_step named_beta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left[OF step])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_eta_contract X Y"
  show "named_compatible_step named_eta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left[OF step])
qed

lemma paper_R_raw_beta_eta_App_right:
  fixes F :: "'c paper_named_term"
  assumes conversion: "paper_R_raw_beta_eta G \<sigma> A B"
    and head: "paper_R_has_type G F (Arr \<sigma> \<tau>)"
  shows "paper_R_raw_beta_eta G \<tau> (NApp F A) (NApp F B)"
proof (rule paper_R_raw_beta_eta_context[where C="\<lambda>X. NApp F X", OF conversion])
  fix X :: "'c paper_named_term"
  assume argument: "paper_R_has_type G X \<sigma>"
  show "paper_R_has_type G (NApp F X) \<tau>" by (rule paper_R_has_type.App[OF head argument])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_beta_contract X Y"
  show "named_compatible_step named_beta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right[OF step])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_eta_contract X Y"
  show "named_compatible_step named_eta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right[OF step])
qed

lemma paper_R_raw_beta_eta_App:
  assumes heads: "paper_R_raw_beta_eta G (Arr \<sigma> \<tau>) F H"
    and arguments: "paper_R_raw_beta_eta G \<sigma> A B"
  shows "paper_R_raw_beta_eta G \<tau> (NApp F A) (NApp H B)"
proof -
  have argument: "paper_R_has_type G A \<sigma>"
    using paper_R_raw_beta_eta_types[OF arguments] by blast
  have head: "paper_R_has_type G H (Arr \<sigma> \<tau>)"
    using paper_R_raw_beta_eta_types[OF heads] by blast
  show ?thesis by (rule paper_R_raw_beta_eta.Trans[
    OF paper_R_raw_beta_eta_App_left[OF heads argument]
      paper_R_raw_beta_eta_App_right[OF arguments head]])
qed

lemma paper_R_raw_beta_eta_Lam:
  fixes A :: "'c paper_named_term"
  assumes conversion: "paper_R_raw_beta_eta G \<tau> A B"
    and binder_type: "paper_R_type (G n)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_raw_beta_eta G (Arr (G n) \<tau>) (NLam n A) (NLam n B)"
proof (rule paper_R_raw_beta_eta_context[where C="NLam n", OF conversion])
  fix X :: "'c paper_named_term"
  assume body: "paper_R_has_type G X \<tau>"
  show "paper_R_has_type G (NLam n X) (Arr (G n) \<tau>)"
    by (rule paper_R_has_type.Lam[OF body binder_type result])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_beta_contract X Y"
  show "named_compatible_step named_beta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body[OF step])
next
  fix X Y :: "'c paper_named_term"
  assume step: "named_compatible_step named_eta_contract X Y"
  show "named_compatible_step named_eta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body[OF step])
qed

section \<open>Lambda prefixes in their literal outermost-first order\<close>

text \<open>
  Binder vectors may be empty and may repeat names. For an empty vector
  the conclusion is simply the supplied conversion. The nonindividual
  result guard is needed for nonempty R abstractions and is automatic
  for the propositional bodies used in Appendix A.2.
\<close>

theorem paper_R_raw_beta_eta_lam_vec:
  assumes conversion: "paper_R_raw_beta_eta G \<tau> A B"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_raw_beta_eta G (paper_type_vector (map G ns) \<tau>)
    (named_lam_vec ns A) (named_lam_vec ns B)"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: named_lam_vec.simps list.map paper_type_vector.simps; rule conversion)
next
  case (Cons n ns)
  have nt: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)"
    using Cons.prems by simp_all
  have inner: "paper_R_raw_beta_eta G (paper_type_vector (map G ns) \<tau>)
      (named_lam_vec ns A) (named_lam_vec ns B)"
    by (rule Cons.IH[OF tail])
  have tail_result: "paper_type_vector (map G ns) \<tau> \<noteq> Ind"
    by (rule paper_type_vector_nonindividual_result[OF result])
  show ?case
    by (simp only: named_lam_vec.simps list.map paper_type_vector.simps;
      rule paper_R_raw_beta_eta_Lam[OF inner nt tail_result])
qed

end
