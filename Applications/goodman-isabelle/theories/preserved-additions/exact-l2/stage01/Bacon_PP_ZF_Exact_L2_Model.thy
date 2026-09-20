theory Bacon_PP_ZF_Exact_L2_Model
  imports
    
    "Goodman_Exact_Generic_Seed.Bacon_PP_ZF_Exact_Generic_Seed"
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_Heredity_Semantics"
    "Goodman_Legacy_01.Bacon_PP_T6_Encoding"
begin

section \<open>Goodman's L2 on Bacon's exact proposition action\<close>

text \<open>
  The semantic operators below act on Bacon's proposition M-set
  \<open>Pow (nat list)\<close>.  The stock contains exactly the operators denoted
  by closed logical terms in the exact HOL--ZF recursion.
\<close>

type_synonym pp_e_operator = "pp_sem_prop \<Rightarrow> pp_sem_prop"

definition pp_e_exact_operator_stock :: "pp_e_operator set" where
  "pp_e_exact_operator_stock =
    image pp_e_raw_operator pp_e_closed_unary_denotations"

lemma pp_e_exact_operator_stock_countable:
  "countable pp_e_exact_operator_stock"
  unfolding pp_e_exact_operator_stock_def
  using pp_e_closed_unary_denotations_countable by simp

lemma pp_e_exact_operator_stockI:
  assumes typed: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and logical: "pp_logical_vocabulary M"
  shows "pp_e_raw_operator (pp_e_closed_den M)
    \<in> pp_e_exact_operator_stock"
  unfolding pp_e_exact_operator_stock_def
    pp_e_closed_unary_denotations_def
  using typed logical by blast

lemma pp_e_exact_operator_stockE:
  assumes "F \<in> pp_e_exact_operator_stock"
  obtains M where
    "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    "pp_logical_vocabulary M"
    "F = pp_e_raw_operator (pp_e_closed_den M)"
  using assms
  unfolding pp_e_exact_operator_stock_def
    pp_e_closed_unary_denotations_def
  by blast

lemma pp_e_exact_operator_stock_equivariant:
  assumes "F \<in> pp_e_exact_operator_stock"
  shows "pp_equivariant_operator F"
proof -
  obtain X where X: "X \<in> pp_e_closed_unary_denotations"
    and F: "F = pp_e_raw_operator X"
    using assms unfolding pp_e_exact_operator_stock_def by blast
  show ?thesis
    unfolding F
    by (rule pp_e_closed_raw_operator_equivariant[OF X])
qed

lemma pp_e_raw_operator_identity:
  "pp_e_raw_operator (pp_e_closed_den pp_identity_operator) = id"
proof (rule ext)
  fix P
  have P_domain: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain by simp
  have beta:
      "pp_e_closed_den pp_identity_operator \<acute> pp_n_bacon_embed P =
        pp_n_bacon_embed P"
    using P_domain
    by (simp add: pp_e_closed_den_def pp_identity_operator_def Lambda_app)
  show "pp_e_raw_operator (pp_e_closed_den pp_identity_operator) P = id P"
    unfolding pp_e_raw_operator_def beta by simp
qed

lemma pp_e_exact_identity_in_stock:
  "id \<in> pp_e_exact_operator_stock"
proof -
  have "pp_e_raw_operator (pp_e_closed_den pp_identity_operator)
      \<in> pp_e_exact_operator_stock"
  proof (rule pp_e_exact_operator_stockI)
    show "[] \<turnstile> pp_identity_operator : (Prop \<rightarrow>\<^sub>o Prop)"
      using typed_pp_identity_operator by (simp add: pp_unary_ty_def)
    show "pp_logical_vocabulary pp_identity_operator"
      by (simp add: pp_identity_operator_def pp_logical_vocabulary_def)
  qed
  then show ?thesis using pp_e_raw_operator_identity by simp
qed

lemma pp_e_raw_operator_closed_den_compose:
  assumes M: "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and N: "[] \<turnstile> N : (Prop \<rightarrow>\<^sub>o Prop)"
  shows "pp_e_raw_operator (pp_e_closed_den (pp_compose M N)) =
    pp_e_raw_operator (pp_e_closed_den M) \<circ>
      pp_e_raw_operator (pp_e_closed_den N)"
proof (rule ext)
  fix P
  let ?P = "pp_n_bacon_embed P"
  let ?N = "pp_e_closed_den N \<acute> ?P"
  have P_domain: "Elem ?P (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain by simp
  have N_domain: "Elem ?N (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF pp_e_closed_den_in_domain[OF N] P_domain])
  have N_power: "Elem ?N (Power Nat)"
    using N_domain by simp
  have N_eta: "pp_n_bacon_embed (pp_n_bacon_extract ?N) = ?N"
    by (rule pp_n_bacon_embed_extract[OF N_power])
  have compose_beta:
      "pp_e_closed_den (pp_compose M N) \<acute> ?P =
        pp_e_closed_den M \<acute> ?N"
    using P_domain pp_e_closed_den_in_domain[OF M]
      pp_e_closed_den_in_domain[OF N]
    by (simp add: pp_e_closed_den_def pp_compose_def Lambda_app
        pp_e_eval_shift)
  show "pp_e_raw_operator (pp_e_closed_den (pp_compose M N)) P =
      (pp_e_raw_operator (pp_e_closed_den M) \<circ>
        pp_e_raw_operator (pp_e_closed_den N)) P"
    unfolding pp_e_raw_operator_def comp_apply compose_beta
    using N_eta by simp
qed

lemma pp_e_exact_operator_stock_compose:
  assumes F: "F \<in> pp_e_exact_operator_stock"
    and G: "G \<in> pp_e_exact_operator_stock"
  shows "F \<circ> G \<in> pp_e_exact_operator_stock"
proof -
  obtain M where M_type:
      "[] \<turnstile> M : (Prop \<rightarrow>\<^sub>o Prop)"
    and M_logical: "pp_logical_vocabulary M"
    and F_M: "F = pp_e_raw_operator (pp_e_closed_den M)"
    using F by (rule pp_e_exact_operator_stockE)
  obtain N where N_type:
      "[] \<turnstile> N : (Prop \<rightarrow>\<^sub>o Prop)"
    and N_logical: "pp_logical_vocabulary N"
    and G_N: "G = pp_e_raw_operator (pp_e_closed_den N)"
    using G by (rule pp_e_exact_operator_stockE)
  have compose_type:
      "[] \<turnstile> pp_compose M N : (Prop \<rightarrow>\<^sub>o Prop)"
  proof -
    have M_unary: "[] \<turnstile> M : pp_unary_ty"
      using M_type by (simp add: pp_unary_ty_def)
    have N_unary: "[] \<turnstile> N : pp_unary_ty"
      using N_type by (simp add: pp_unary_ty_def)
    show ?thesis
      using typed_pp_compose[OF M_unary N_unary]
      by (simp add: pp_unary_ty_def)
  qed
  have compose_logical: "pp_logical_vocabulary (pp_compose M N)"
    using M_logical N_logical
    by (simp add: pp_logical_vocabulary_def pp_compose_def shift_def)
  have denotation:
      "pp_e_raw_operator (pp_e_closed_den (pp_compose M N))
        \<in> pp_e_exact_operator_stock"
    by (rule pp_e_exact_operator_stockI[OF compose_type compose_logical])
  show ?thesis
    using denotation pp_e_raw_operator_closed_den_compose[OF M_type N_type]
    unfolding F_M G_N by simp
qed

end
