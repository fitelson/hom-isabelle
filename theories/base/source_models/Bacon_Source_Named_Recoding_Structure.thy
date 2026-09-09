theory Bacon_Source_Named_Recoding_Structure
  imports Bacon_Source_Named_Recoding_Assignments Bacon_Source_Named_BBK_Interface
begin

section \<open>Injectively recoding the values of an independent named model\<close>

text \<open>
  For an injection f, put D′σ = f ‘ Dσ and interpret a term by first
  pulling its partial assignment back through inv f, then applying f to
  its old denotation. Source role: change of carrier in the model clauses
  of Bacon–Dorr Definition 3.1, pp.43–44.

  No surjectivity onto the target carrier is assumed. Typing places every
  assigned target value in a coded domain, where the inverse is justified.
  Application retains the full heterogeneous clause, not merely a same-type
  version. The syntax and raw typed βη relation are unchanged.
\<close>

context paper_named_bbk_model
begin

definition named_recode_denote :: "('v \<Rightarrow> 'w) \<Rightarrow> 'w named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'w" where
  "named_recode_denote f g A = f (denote (named_map_assignment (inv f) g) A)"

definition named_recode_valuation :: "('v \<Rightarrow> 'w) \<Rightarrow> 'w \<Rightarrow> bool" where
  "named_recode_valuation f v = valuation (inv f v)"

lemma named_recode_truth:
  assumes injective: "inj f"
  shows "named_recode_valuation f (named_recode_denote f g A) =
    valuation (denote (named_map_assignment (inv f) g) A)"
  by (simp only: named_recode_valuation_def named_recode_denote_def inv_f_f[OF injective])

theorem named_recode_denote_type:
  assumes injective: "inj f"
    and language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and typed: "named_env_typed (named_image_domain f domain) stock g" and adequate: "named_adequate g A"
  shows "named_recode_denote f g A \<in> named_image_domain f domain \<sigma>"
proof -
  have qt: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have qa: "named_adequate (named_map_assignment (inv f) g) A"
    by (rule iffD2[OF named_map_assignment_adequate adequate])
  have member: "denote (named_map_assignment (inv f) g) A \<in> domain \<sigma>"
    by (rule denote_type[OF language qt qa])
  show ?thesis unfolding named_recode_denote_def named_image_domain_def by (rule imageI[OF member])
qed

theorem named_recode_denote_var:
  assumes injective: "inj f" and typed: "named_env_typed (named_image_domain f domain) stock g"
    and assigned: "g n = Some v"
  shows "named_recode_denote f g (NVar n) = v"
proof -
  have qt: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have qn: "named_map_assignment (inv f) g n = Some (inv f v)"
    by (simp add: named_map_assignment_def assigned)
  have value_eq: "denote (named_map_assignment (inv f) g) (NVar n) = inv f v"
    by (rule denote_var[OF qt qn])
  have member: "v \<in> named_image_domain f domain (stock n)" by (rule named_env_value[OF typed assigned])
  obtain a where coded: "v = f a" using member unfolding named_image_domain_def by blast
  show ?thesis by (simp only: named_recode_denote_def value_eq coded inv_f_f[OF injective])
qed

theorem named_recode_denote_application:
  assumes injective: "inj f"
    and fl: "named_in_language paper_logical_type signature stock F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type signature stock A \<sigma>"
    and hl: "named_in_language paper_logical_type signature stock H (Arr \<upsilon> \<omega>)"
    and bl: "named_in_language paper_logical_type signature stock B \<upsilon>"
    and gt: "named_env_typed (named_image_domain f domain) stock g"
    and ht: "named_env_typed (named_image_domain f domain) stock h"
    and ga: "named_adequate g (NApp F A)" and ha: "named_adequate h (NApp H B)"
    and heads: "named_recode_denote f g F = named_recode_denote f h H"
    and args: "named_recode_denote f g A = named_recode_denote f h B"
  shows "named_recode_denote f g (NApp F A) = named_recode_denote f h (NApp H B)"
proof -
  let ?g = "named_map_assignment (inv f) g"
  let ?h = "named_map_assignment (inv f) h"
  have head_values: "denote ?g F = denote ?h H"
    by (rule injD[OF injective], rule heads[unfolded named_recode_denote_def])
  have arg_values: "denote ?g A = denote ?h B"
    by (rule injD[OF injective], rule args[unfolded named_recode_denote_def])
  have gadeq: "named_adequate ?g (NApp F A)" by (rule iffD2[OF named_map_assignment_adequate ga])
  have hadeq: "named_adequate ?h (NApp H B)" by (rule iffD2[OF named_map_assignment_adequate ha])
  have application: "denote ?g (NApp F A) = denote ?h (NApp H B)"
    by (rule denote_application_cong[OF fl al hl bl named_map_assignment_inv_typed[OF injective gt]
      named_map_assignment_inv_typed[OF injective ht] gadeq hadeq head_values arg_values])
  show ?thesis unfolding named_recode_denote_def by (rule arg_cong[where f=f, OF application])
qed

theorem named_recode_denote_locality:
  assumes injective: "inj f"
    and language: "named_in_language paper_logical_type signature stock A \<sigma>"
    and gt: "named_env_typed (named_image_domain f domain) stock g"
    and ht: "named_env_typed (named_image_domain f domain) stock h"
    and ga: "named_adequate g A" and ha: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "named_recode_denote f g A = named_recode_denote f h A"
proof -
  have qagree: "named_map_assignment (inv f) g n = named_map_assignment (inv f) h n"
    if "n \<in> named_fv A" for n
    by (simp only: named_map_assignment_def agree[OF that])
  have equality: "denote (named_map_assignment (inv f) g) A = denote (named_map_assignment (inv f) h) A"
    by (rule denote_locality[OF language named_map_assignment_inv_typed[OF injective gt]
      named_map_assignment_inv_typed[OF injective ht] iffD2[OF named_map_assignment_adequate ga]
      iffD2[OF named_map_assignment_adequate ha] qagree])
  show ?thesis unfolding named_recode_denote_def by (rule arg_cong[where f=f, OF equality])
qed

theorem named_recode_denote_conversion:
  assumes injective: "inj f"
    and conversion: "named_raw_beta_eta paper_logical_type stock \<sigma> A B"
    and al: "named_in_language paper_logical_type signature stock A \<sigma>"
    and bl: "named_in_language paper_logical_type signature stock B \<sigma>"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and ga: "named_adequate g A" and gb: "named_adequate g B"
  shows "named_recode_denote f g A = named_recode_denote f g B"
proof -
  have equality: "denote (named_map_assignment (inv f) g) A = denote (named_map_assignment (inv f) g) B"
    by (rule denote_beta_eta[OF conversion al bl named_map_assignment_inv_typed[OF injective typed]
      iffD2[OF named_map_assignment_adequate ga] iffD2[OF named_map_assignment_adequate gb]])
  show ?thesis unfolding named_recode_denote_def by (rule arg_cong[where f=f, OF equality])
qed

end

end
