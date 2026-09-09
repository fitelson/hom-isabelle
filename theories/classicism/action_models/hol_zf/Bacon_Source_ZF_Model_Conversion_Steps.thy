theory Bacon_Source_ZF_Model_Conversion_Steps
  imports Bacon_Source_ZF_Model_Beta_Conversion Bacon_Source_ZF_Model_Eta_Conversion
    Bacon_Source_ZF_Model_Evaluation_Contexts
begin

section \<open>C.2 transports the proved β and η root equations\<close>

text \<open>
  A literal β or η contraction inside an App/Lam context preserves
  evaluation when both whole terms are in the same R-language and
  the partial assignment is adequate for both. Source: C.2 and C.4–C.6,
  pp.70–71. Root equations are proved semantic consequences, not fields
  of the action model. The context theorem retains guards at each
  recursively exposed root and under every binder.
\<close>

lemma paper_ZF_action_model_beta_root:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and step: "named_beta_contract A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g A"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  using step left adequate
proof (induction rule: named_beta_contract.induct)
  case (beta C x U)
  show ?case by (rule paper_ZF_action_model_beta[OF model beta.prems(1) beta.hyps arrow origin typed beta.prems(2)])
qed

lemma paper_ZF_action_model_eta_root:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and step: "named_eta_contract A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g" and adequate: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
  using step left right adequate
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  obtain \<tau> where shape: "\<rho> = Arr (G x) \<tau>"
    by (rule paper_ZF_context_Lam_languageE[OF eta.prems(1)]; rule that; assumption)
  have language: "paper_R_in_language \<Sigma> G F (Arr (G x) \<tau>)"
    using eta.prems(2) by (simp only: shape)
  show ?case by (rule paper_ZF_action_model_eta[OF model language eta.hyps arrow origin typed eta.prems(3)])
qed

theorem paper_ZF_action_model_beta_step:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and step: "named_compatible_step named_beta_contract A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof (rule paper_ZF_model_eval_compatible[OF model step _ left right arrow origin typed adequate_left adequate_right])
  fix U V \<tau> k u
  assume root_step: "named_beta_contract U V"
    and ul: "paper_R_in_language \<Sigma> G U \<tau>" and vl: "paper_R_in_language \<Sigma> G V \<tau>"
    and ka: "k \<in> explode Ar" and ko: "source k = root"
    and ut: "paper_ZF_action_env_typed D G (target k) u"
    and ua: "named_adequate u U" and va: "named_adequate u V"
  show "paper_ZF_action_eval Ar source target compose identity D T I G U k u =
    paper_ZF_action_eval Ar source target compose identity D T I G V k u"
    by (rule paper_ZF_action_model_beta_root[OF model root_step ul ka ko ut ua])
qed

theorem paper_ZF_action_model_eta_step:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and step: "named_compatible_step named_eta_contract A B"
    and left: "paper_R_in_language \<Sigma> G A \<rho>" and right: "paper_R_in_language \<Sigma> G B \<rho>"
    and arrow: "h \<in> explode Ar" and origin: "source h = root"
    and typed: "paper_ZF_action_env_typed D G (target h) g"
    and adequate_left: "named_adequate g A" and adequate_right: "named_adequate g B"
  shows "paper_ZF_action_eval Ar source target compose identity D T I G A h g =
    paper_ZF_action_eval Ar source target compose identity D T I G B h g"
proof (rule paper_ZF_model_eval_compatible[OF model step _ left right arrow origin typed adequate_left adequate_right])
  fix U V \<tau> k u
  assume root_step: "named_eta_contract U V"
    and ul: "paper_R_in_language \<Sigma> G U \<tau>" and vl: "paper_R_in_language \<Sigma> G V \<tau>"
    and ka: "k \<in> explode Ar" and ko: "source k = root"
    and ut: "paper_ZF_action_env_typed D G (target k) u"
    and ua: "named_adequate u U" and va: "named_adequate u V"
  show "paper_ZF_action_eval Ar source target compose identity D T I G U k u =
    paper_ZF_action_eval Ar source target compose identity D T I G V k u"
    by (rule paper_ZF_action_model_eta_root[OF model root_step ul vl ka ko ut va])
qed

end
