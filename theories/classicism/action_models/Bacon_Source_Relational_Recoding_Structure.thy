theory Bacon_Source_Relational_Recoding_Structure
  imports Bacon_Source_Relational_Recoding_Denotation
begin

section \<open>Application, locality and raw βη under carrier recoding\<close>

text \<open>
  The heterogeneous application clause retains independently typed heads
  and arguments. Their denotations are recovered by the inverse on the
  actual domain union before invoking the original application clause.
  No disjointness, Functionality or total assignment is assumed.
  Source: Bacon–Dorr Definition 3.1, pp.43–44.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_recode_denote_equal_iff:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and bl: "paper_R_in_language signature stock B \<tau>"
    and gt: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and ht: "named_env_typed (paper_R_recode_domain f domain) stock h"
    and aa: "named_adequate g A" and ba: "named_adequate h B"
  shows "paper_R_recode_denote f g A = paper_R_recode_denote f h B \<longleftrightarrow>
    denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A =
    denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) h) B"
proof
  assume equality: "paper_R_recode_denote f g A = paper_R_recode_denote f h B"
  have decoded: "paper_R_recode_inverse domain f (paper_R_recode_denote f g A) =
      paper_R_recode_inverse domain f (paper_R_recode_denote f h B)"
    by (rule arg_cong[OF equality])
  show "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A =
      denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) h) B"
    using decoded by (simp only: paper_R_recode_denote_inverse[OF injective al gt aa]
      paper_R_recode_denote_inverse[OF injective bl ht ba])
next
  assume equality: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A =
      denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) h) B"
  show "paper_R_recode_denote f g A = paper_R_recode_denote f h B"
    unfolding paper_R_recode_denote_def by (rule arg_cong[where f=f, OF equality])
qed

theorem paper_R_recode_denote_application:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and hl: "paper_R_in_language signature stock H (Arr \<upsilon> \<rho>)"
    and bl: "paper_R_in_language signature stock B \<upsilon>"
    and gt: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and ht: "named_env_typed (paper_R_recode_domain f domain) stock h"
    and ga: "named_adequate g (NApp F A)" and ha: "named_adequate h (NApp H B)"
    and heads: "paper_R_recode_denote f g F = paper_R_recode_denote f h H"
    and arguments: "paper_R_recode_denote f g A = paper_R_recode_denote f h B"
  shows "paper_R_recode_denote f g (NApp F A) = paper_R_recode_denote f h (NApp H B)"
proof -
  let ?g = "paper_R_recode_assignment (paper_R_recode_inverse domain f) g"
  let ?h = "paper_R_recode_assignment (paper_R_recode_inverse domain f) h"
  have gf: "named_adequate g F" and gaa: "named_adequate g A"
    using ga unfolding named_adequate_def by auto
  have hh: "named_adequate h H" and hab: "named_adequate h B"
    using ha unfolding named_adequate_def by auto
  have head_eq: "denote ?g F = denote ?h H"
    by (rule iffD1[OF paper_R_recode_denote_equal_iff[OF injective fl hl gt ht gf hh] heads])
  have arg_eq: "denote ?g A = denote ?h B"
    by (rule iffD1[OF paper_R_recode_denote_equal_iff[OF injective al bl gt ht gaa hab] arguments])
  have application: "denote ?g (NApp F A) = denote ?h (NApp H B)"
    by (rule denote_application_cong[OF fl al hl bl
      paper_R_recode_inverse_assignment_typed[OF injective gt]
      paper_R_recode_inverse_assignment_typed[OF injective ht]
      iffD2[OF paper_R_recode_assignment_adequate_iff ga]
      iffD2[OF paper_R_recode_assignment_adequate_iff ha] head_eq arg_eq])
  show ?thesis unfolding paper_R_recode_denote_def by (rule arg_cong[where f=f, OF application])
qed

theorem paper_R_recode_denote_locality:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and language: "paper_R_in_language signature stock A \<sigma>"
    and gt: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and ht: "named_env_typed (paper_R_recode_domain f domain) stock h"
    and ga: "named_adequate g A" and ha: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "paper_R_recode_denote f g A = paper_R_recode_denote f h A"
proof -
  have decoded_agree: "paper_R_recode_assignment (paper_R_recode_inverse domain f) g n =
      paper_R_recode_assignment (paper_R_recode_inverse domain f) h n"
    if "n \<in> named_fv A" for n
    by (simp only: paper_R_recode_assignment_def agree[OF that])
  have equality: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A =
      denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) h) A"
    by (rule denote_locality[OF language
      paper_R_recode_inverse_assignment_typed[OF injective gt]
      paper_R_recode_inverse_assignment_typed[OF injective ht]
      iffD2[OF paper_R_recode_assignment_adequate_iff ga]
      iffD2[OF paper_R_recode_assignment_adequate_iff ha] decoded_agree])
  show ?thesis unfolding paper_R_recode_denote_def by (rule arg_cong[where f=f, OF equality])
qed

theorem paper_R_recode_denote_conversion:
  assumes injective: "inj_on f (\<Union>\<sigma>. domain \<sigma>)"
    and conversion: "paper_R_raw_beta_eta stock \<sigma> A B"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and bl: "paper_R_in_language signature stock B \<sigma>"
    and typed: "named_env_typed (paper_R_recode_domain f domain) stock g"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "paper_R_recode_denote f g A = paper_R_recode_denote f g B"
proof -
  have equality: "denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) A =
      denote (paper_R_recode_assignment (paper_R_recode_inverse domain f) g) B"
    by (rule denote_beta_eta[OF conversion al bl
      paper_R_recode_inverse_assignment_typed[OF injective typed]
      iffD2[OF paper_R_recode_assignment_adequate_iff aa]
      iffD2[OF paper_R_recode_assignment_adequate_iff ba]])
  show ?thesis unfolding paper_R_recode_denote_def by (rule arg_cong[where f=f, OF equality])
qed

end

end
