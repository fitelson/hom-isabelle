theory Bacon_Source_Relational_Naming_Conversion
  imports Bacon_Source_Relational_Naming_Step_Denotation
    Bacon_Source_Relational_Assignment_Extension Bacon_Source_Relational_Signature_Conservativity
begin

section \<open>Raw R conversion invariance with only endpoint signature guards\<close>

text \<open>
  First restrict the raw R chain to the expanded signature using the
  independent R retraction theorem. Interpret its intermediate terms
  under the proved R-supported extension of g, then use locality to
  recover the values under the original endpoint-adequate assignment.

  Only R domains are required to be nonempty; non-R slots remain
  undefined. The global adequacy lemma is polymorphic in the constant
  carrier and therefore applies to the expanded names without any F
  model or total-F-assignment assumption. The resulting theorem retains
  Definition 3.1(ii.d)'s raw, internally signature-free conversion guard.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_naming_completed_denote:
  assumes language: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "paper_R_naming_denote (paper_R_complete_assignment domain stock g) A = paper_R_naming_denote g A"
proof -
  have ct: "named_env_typed domain stock (paper_R_complete_assignment domain stock g)"
    by (rule paper_R_complete_assignment_typed[OF domain_nonempty typed])
  have ca: "named_adequate (paper_R_complete_assignment domain stock g) A"
    by (rule paper_R_complete_assignment_language_adequate[OF language])
  show ?thesis
  proof (rule paper_R_naming_denote_locality[OF language ct typed ca adequate])
    fix n
    assume free: "n \<in> named_fv A"
    show "paper_R_complete_assignment domain stock g n = g n"
      by (rule paper_R_complete_assignment_agrees[OF adequate free])
  qed
qed

lemma paper_R_naming_signature_conversion_complete:
  assumes conversion: "paper_R_beta_eta_in_signature (paper_R_naming_signature signature domain) stock \<tau> A B"
    and typed: "named_env_typed domain stock g"
  shows "paper_R_naming_denote (paper_R_complete_assignment domain stock g) A =
    paper_R_naming_denote (paper_R_complete_assignment domain stock g) B"
proof -
  have ct: "named_env_typed domain stock (paper_R_complete_assignment domain stock g)"
    by (rule paper_R_complete_assignment_typed[OF domain_nonempty typed])
  show ?thesis using conversion
  proof (induction rule: paper_R_beta_eta_in_signature.induct)
    case Refl
    show ?case by (rule refl)
  next
    case Beta
    show ?case by (rule paper_R_naming_beta_step_denote[
      OF Beta.hyps(3) Beta.hyps(1) Beta.hyps(2) ct
        paper_R_complete_assignment_language_adequate[OF Beta.hyps(1)]
        paper_R_complete_assignment_language_adequate[OF Beta.hyps(2)]])
  next
    case Eta
    show ?case by (rule paper_R_naming_eta_step_denote[
      OF Eta.hyps(3) Eta.hyps(1) Eta.hyps(2) ct
        paper_R_complete_assignment_language_adequate[OF Eta.hyps(1)]
        paper_R_complete_assignment_language_adequate[OF Eta.hyps(2)]])
  next
    case Sym
    show ?case by (rule sym[OF Sym.IH])
  next
    case Trans
    show ?case by (rule trans[OF Trans.IH])
  qed
qed

theorem paper_R_naming_denote_conversion:
  assumes conversion: "paper_R_raw_beta_eta stock \<tau> A B"
    and left: "paper_R_in_language (paper_R_naming_signature signature domain) stock A \<tau>"
    and right: "paper_R_in_language (paper_R_naming_signature signature domain) stock B \<tau>"
    and typed: "named_env_typed domain stock g" and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_naming_denote g A = paper_R_naming_denote g B"
proof -
  have restricted: "paper_R_beta_eta_in_signature (paper_R_naming_signature signature domain) stock \<tau> A B"
    by (rule paper_R_raw_to_signature[OF stock_rich conversion left right])
  have equal: "paper_R_naming_denote (paper_R_complete_assignment domain stock g) A =
      paper_R_naming_denote (paper_R_complete_assignment domain stock g) B"
    by (rule paper_R_naming_signature_conversion_complete[OF restricted typed])
  show ?thesis using equal by (simp only:
    paper_R_naming_completed_denote[OF left typed aa] paper_R_naming_completed_denote[OF right typed ba])
qed

end

end
