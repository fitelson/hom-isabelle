theory PoP_G100_PPt
  imports PoP_K6.PoP_G100_Kernel_ZF_Model Goodman_Legacy_01.Bacon_PP_Modalized_Functionality_Derived
begin

text \<open>Purity of Pure: PP at t in the Model of C_FP
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory holds PP at t in the kernel; Loupe built it on the K6 companion (the HOL-ZF model), with Jacob, on 2026-11-09; not Branden Fitelson's. The route
  is Reticle's, in C_FP's terms as in Caltrop's notes: the purity schema at True and False; zeroary Exhaustion with Application at negation; Propositional Equivalence
  for Pure_t(p) = NC(p), with NC = (\<lambda>p. box p or box not p); necessitation and Modalized Functionality (the library's CEV_unary_modalized_functionality) for
  Pure_t = NC; the purity schema at NC. The calculus is CEV with C_FP's claims added as axioms (CEV_axiom_proves), the calculus k6_plus speaks of.\<close>

section \<open>1. The terms and the claims used\<close>

definition ppt_N :: oterm where "ppt_N = Lam Prop (Neg (Var 0))"

definition ppt_NC :: oterm where "ppt_NC = Lam Prop (Disj (\<box>\<^sub>o (Var 0)) (\<box>\<^sub>o (Neg (Var 0))))"

definition ppt_L :: "oterm list" where
  "ppt_L = [pp_pure Prop ObjTrue, pp_pure Prop ObjFalse, pp_pure rc_u ppt_N, pp_application_closure Prop Prop,
    pp_zeroary_exhaustion, pp_pure rc_u ppt_NC]"

lemma ppt_N_ty: "\<Gamma> \<turnstile> ppt_N : rc_u" unfolding ppt_N_def by (intro has_type.Lam has_type.Neg has_type.Var) simp_all

lemma ppt_NC_ty: "\<Gamma> \<turnstile> ppt_NC : rc_u" unfolding ppt_NC_def
  by (intro has_type.Lam has_type.Disj typed_ObjBox has_type.Neg has_type.Var) simp_all

lemma ppt_consts: "consts_of ObjTrue = {}" "consts_of ObjFalse = {}" "consts_of ppt_N = {}" "consts_of ppt_NC = {}"
  by (simp_all add: ObjFalse_def ObjTrue_def ppt_N_def ppt_NC_def ObjBox_def)

lemma ppt_shift: "shift (pp_Pure Prop) = pp_Pure Prop" "shift ppt_NC = ppt_NC" "shift ObjTrue = ObjTrue"
  by (simp_all add: pp_Pure_def ppt_NC_def ObjBox_def ObjTrue_def shift_def)

lemma ppt_AC_ty: "\<Gamma> \<turnstile> pp_application_closure Prop Prop : Prop"
  by (rule infer_type_sound) (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)

lemma ppt_E0_ty: "\<Gamma> \<turnstile> pp_zeroary_exhaustion : Prop"
  by (rule infer_type_sound) (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)

lemma ppt_L_ty: "A \<in> set ppt_L \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  unfolding ppt_L_def using typed_pp_pure[OF typed_ObjTrue] typed_pp_pure[OF typed_ObjFalse] typed_pp_pure[OF ppt_N_ty]
    typed_pp_pure[OF ppt_NC_ty] ppt_AC_ty ppt_E0_ty by auto

theorem ppt_L_sub: "set ppt_L \<subseteq> pp_CFP_axioms"
  unfolding ppt_L_def using cfp_LP[OF typed_ObjTrue ppt_consts(1)] cfp_LP[OF typed_ObjFalse ppt_consts(2)]
    cfp_LP[OF ppt_N_ty ppt_consts(3)] cfp_LP[OF ppt_NC_ty ppt_consts(4)] cfp_AC cfp_mem(2)[of "[]", unfolded cfp_lit(2)]
  by auto

section \<open>2. Pure_t(p) iff NC(p), in U, from the claims\<close>

lemma ppt_pc:
  assumes "list_all (\<lambda>A. \<Gamma> \<turnstile>\<^sub>U A) Hs" and "\<Gamma> \<turnstile> B : Prop" and "\<And>v. list_all (prop_eval v) Hs \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>U B"
  using assms
proof (induction Hs arbitrary: B)
  case Nil
  then show ?case by (intro U_taut) (simp add: prop_tautology_def)
next
  case (Cons H Hs)
  have hH: "\<Gamma> \<turnstile>\<^sub>U H" using Cons.prems(1) by simp
  have "\<Gamma> \<turnstile>\<^sub>U Imp H B"
    using Cons.prems(1) has_type.Imp[OF U_formula[OF hH] Cons.prems(2)] Cons.prems(3) by (intro Cons.IH) auto
  then show ?case by (rule U_proves.MP[OF hH])
qed

text \<open>The purity schema at True and False: necessary and impossible propositions are pure.\<close>

lemma ppt_dir1:
  assumes ta: "\<Gamma> \<turnstile> a : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse)
    (Imp (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a))) (pp_pure Prop a)))"
proof -
  let ?P = "pp_Pure Prop" and ?G = "Lam Prop (App (pp_Pure Prop) (Neg (Var 0)))"
  have Pt: "\<Gamma> \<turnstile> ?P : Prop \<rightarrow>\<^sub>o Prop" by (rule typed_pp_Pure)
  have tna: "\<Gamma> \<turnstile> Neg a : Prop" and tnna: "\<Gamma> \<turnstile> Neg (Neg a) : Prop" using ta by (auto intro: has_type.Neg)
  have tG: "\<Gamma> \<turnstile> ?G : Prop \<rightarrow>\<^sub>o Prop" by (rule infer_type_sound) (simp add: pp_Pure_def)
  have sym1: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop a ObjTrue) (Eq Prop ObjTrue a)" by (rule U_eq_sym[OF ta typed_ObjTrue])
  have LL1: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ObjTrue a) (Imp (App ?P ObjTrue) (App ?P a))" by (rule u_rc_LL[OF typed_ObjTrue ta Pt])
  have sym2: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop (Neg a) ObjTrue) (Eq Prop ObjTrue (Neg a))" by (rule U_eq_sym[OF tna typed_ObjTrue])
  have LL2: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ObjTrue (Neg a)) (Imp (App ?G ObjTrue) (App ?G (Neg a)))"
    by (rule u_rc_LL[OF typed_ObjTrue tna tG])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?G ObjTrue \<longleftrightarrow>\<^sub>o App ?P (Neg ObjTrue))"
    using u_beta[OF has_type.App[OF tG typed_ObjTrue]] by (simp add: pp_Pure_def subst0_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?G (Neg a) \<longleftrightarrow>\<^sub>o App ?P (Neg (Neg a)))"
    using u_beta[OF has_type.App[OF tG tna]] by (simp add: pp_Pure_def subst0_def)
  have tdn: "\<Gamma> \<turnstile> (Neg (Neg a) \<longleftrightarrow>\<^sub>o a) : Prop" using tnna ta by (intro has_type.Conj has_type.Imp)
  have dn: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Neg (Neg a)) a" by (rule u_rc_eq_of_iff[OF tnna ta u_rc_pc1[OF U_true tdn]]) simp
  have LL3: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop (Neg (Neg a)) a) (Imp (App ?P (Neg (Neg a))) (App ?P a))" by (rule u_rc_LL[OF tnna ta Pt])
  have tB: "\<Gamma> \<turnstile> Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse) (Imp (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a))) (pp_pure Prop a))) : Prop"
    by (intro has_type.Imp has_type.Disj typed_ObjBox typed_pp_pure typed_ObjTrue typed_ObjFalse ta tna)
  show ?thesis
    by (rule ppt_pc[where Hs = "[Imp (Eq Prop a ObjTrue) (Eq Prop ObjTrue a), Imp (Eq Prop ObjTrue a) (Imp (App ?P ObjTrue) (App ?P a)),
      Imp (Eq Prop (Neg a) ObjTrue) (Eq Prop ObjTrue (Neg a)), Imp (Eq Prop ObjTrue (Neg a)) (Imp (App ?G ObjTrue) (App ?G (Neg a))),
      (App ?G ObjTrue \<longleftrightarrow>\<^sub>o App ?P (Neg ObjTrue)), (App ?G (Neg a) \<longleftrightarrow>\<^sub>o App ?P (Neg (Neg a))), Eq Prop (Neg (Neg a)) a,
      Imp (Eq Prop (Neg (Neg a)) a) (Imp (App ?P (Neg (Neg a))) (App ?P a))]"])
      (use sym1 LL1 sym2 LL2 b1 b2 dn LL3 tB in \<open>auto simp: pp_pure_def ObjBox_def ObjFalse_def\<close>)
qed

text \<open>Zeroary Exhaustion, at p and at not p, with Application at negation: pure propositions are noncontingent.\<close>

lemma ppt_dir2:
  assumes ta: "\<Gamma> \<turnstile> a : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (pp_pure rc_u ppt_N) (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion
    (Imp (pp_pure Prop a) (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a))))))"
proof -
  let ?P = "pp_Pure Prop"
  have Pt: "\<Gamma> \<turnstile> ?P : Prop \<rightarrow>\<^sub>o Prop" by (rule typed_pp_Pure)
  have tna: "\<Gamma> \<turnstile> Neg a : Prop" using ta by (rule has_type.Neg)
  have tNa: "\<Gamma> \<turnstile> App ppt_N a : Prop" by (rule has_type.App[OF ppt_N_ty ta])
  have Z1: "\<Gamma> \<turnstile>\<^sub>U Imp pp_zeroary_exhaustion (zI a)" by (rule u_zI[OF ta])
  have Z2: "\<Gamma> \<turnstile>\<^sub>U Imp pp_zeroary_exhaustion (zI (Neg a))" by (rule u_zI[OF tna])
  have AC: "\<Gamma> \<turnstile>\<^sub>U Imp (pp_application_closure Prop Prop)
      (Imp (Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) ppt_N) (pp_pure Prop a)) (pp_pure Prop (App ppt_N a)))"
    by (rule u_rc_ac[OF ppt_N_ty ta])
  have tNa': "\<Gamma> \<turnstile> App (Lam Prop (Neg (Var 0))) a : Prop" using tNa by (simp add: ppt_N_def)
  have bN: "\<Gamma> \<turnstile>\<^sub>U (App ppt_N a \<longleftrightarrow>\<^sub>o Neg a)" using u_beta[OF tNa'] by (simp add: ppt_N_def subst0_def)
  have eN: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (App ppt_N a) (Neg a)" by (rule u_rc_eq_of_iff[OF tNa tna bN])
  have LLN: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop (App ppt_N a) (Neg a)) (Imp (App ?P (App ppt_N a)) (App ?P (Neg a)))"
    by (rule u_rc_LL[OF tNa tna Pt])
  have tB: "\<Gamma> \<turnstile> Imp (pp_pure rc_u ppt_N) (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion
      (Imp (pp_pure Prop a) (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a)))))) : Prop"
    by (intro has_type.Imp has_type.Disj typed_ObjBox typed_pp_pure ppt_N_ty ppt_AC_ty ppt_E0_ty ta tna)
  show ?thesis
    by (rule ppt_pc[where Hs = "[Imp pp_zeroary_exhaustion (zI a), Imp pp_zeroary_exhaustion (zI (Neg a)),
      Imp (pp_application_closure Prop Prop) (Imp (Conj (pp_pure (Prop \<rightarrow>\<^sub>o Prop) ppt_N) (pp_pure Prop a)) (pp_pure Prop (App ppt_N a))),
      Eq Prop (App ppt_N a) (Neg a), Imp (Eq Prop (App ppt_N a) (Neg a)) (Imp (App ?P (App ppt_N a)) (App ?P (Neg a)))]"])
      (use Z1 Z2 AC eN LLN tB in \<open>auto simp: zI_def pp_pure_def\<close>)
qed

lemma ppt_iff_U:
  assumes ta: "\<Gamma> \<turnstile> a : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse) (Imp (pp_pure rc_u ppt_N)
    (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion (App (pp_Pure Prop) a \<longleftrightarrow>\<^sub>o App ppt_NC a)))))"
proof -
  have tna: "\<Gamma> \<turnstile> Neg a : Prop" using ta by (rule has_type.Neg)
  have tNCa: "\<Gamma> \<turnstile> App ppt_NC a : Prop" by (rule has_type.App[OF ppt_NC_ty ta])
  have tNCa': "\<Gamma> \<turnstile> App (Lam Prop (Disj (\<box>\<^sub>o (Var 0)) (\<box>\<^sub>o (Neg (Var 0))))) a : Prop" using tNCa by (simp add: ppt_NC_def)
  have bNC: "\<Gamma> \<turnstile>\<^sub>U (App ppt_NC a \<longleftrightarrow>\<^sub>o Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a)))" using u_beta[OF tNCa'] by (simp add: ppt_NC_def subst0_def)
  have tPa: "\<Gamma> \<turnstile> App (pp_Pure Prop) a : Prop" by (rule has_type.App[OF typed_pp_Pure ta])
  have tB: "\<Gamma> \<turnstile> Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse) (Imp (pp_pure rc_u ppt_N)
    (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion (App (pp_Pure Prop) a \<longleftrightarrow>\<^sub>o App ppt_NC a))))) : Prop"
    by (intro has_type.Imp has_type.Conj typed_pp_pure typed_ObjTrue typed_ObjFalse ppt_N_ty ppt_AC_ty ppt_E0_ty tPa tNCa)
  show ?thesis
    by (rule ppt_pc[where Hs = "[Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse) (Imp (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a))) (pp_pure Prop a))),
      Imp (pp_pure rc_u ppt_N) (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion (Imp (pp_pure Prop a) (Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a)))))),
      (App ppt_NC a \<longleftrightarrow>\<^sub>o Disj (\<box>\<^sub>o a) (\<box>\<^sub>o (Neg a)))]"])
      (use ppt_dir1[OF ta] ppt_dir2[OF ta] bNC tB in \<open>auto simp: pp_pure_def\<close>)
qed

section \<open>3. PP_t in CEV with the claims as axioms\<close>

lemma ppt_ax: "set ppt_L \<subseteq> T \<Longrightarrow> A \<in> set ppt_L \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  by (rule CEV_axiom_proves.Axiom) (auto intro: ppt_L_ty)

lemma ppt_plus_pc1:
  assumes a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ B"
proof -
  have "prop_tautology \<Gamma> (Imp A B)" unfolding prop_tautology_def using CEV_axiom_proves_formula[OF a] b t by auto
  then show ?thesis by (rule CEV_axiom_proves.MP[OF a CEV_axiom_proves.Base[OF CEV_prop_tautology]])
qed

lemma ppt_plus_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue" by (rule CEV_axiom_proves.Base[OF U_sub_CEV[OF U_true]])

text \<open>The claims give Pure_t(p) iff NC(p), with p free.\<close>

lemma ppt_plus_iff:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ (App (pp_Pure Prop) (Var 0) \<longleftrightarrow>\<^sub>o App ppt_NC (Var 0))"
proof -
  have tv: "[Prop] \<turnstile> Var 0 : Prop" by (simp add: lookup_def)
  have b: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (pp_pure Prop ObjTrue) (Imp (pp_pure Prop ObjFalse) (Imp (pp_pure rc_u ppt_N)
    (Imp (pp_application_closure Prop Prop) (Imp pp_zeroary_exhaustion (App (pp_Pure Prop) (Var 0) \<longleftrightarrow>\<^sub>o App ppt_NC (Var 0))))))"
    by (rule CEV_axiom_proves.Base[OF U_sub_CEV[OF ppt_iff_U[OF tv]]])
  have m1: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjTrue" by (rule ppt_ax[OF T]) (simp add: ppt_L_def)
  have m2: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure Prop ObjFalse" by (rule ppt_ax[OF T]) (simp add: ppt_L_def)
  have m3: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure rc_u ppt_N" by (rule ppt_ax[OF T]) (simp add: ppt_L_def)
  have m4: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_application_closure Prop Prop" by (rule ppt_ax[OF T]) (simp add: ppt_L_def)
  have m5: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_zeroary_exhaustion" by (rule ppt_ax[OF T]) (simp add: ppt_L_def)
  show ?thesis by (rule CEV_axiom_proves.MP[OF m5 CEV_axiom_proves.MP[OF m4 CEV_axiom_proves.MP[OF m3
    CEV_axiom_proves.MP[OF m2 CEV_axiom_proves.MP[OF m1 b]]]]])
qed

text \<open>Propositional Equivalence: Pure_t(p) = NC(p), with p free.\<close>

lemma ppt_plus_pe:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (App (pp_Pure Prop) (Var 0)) (App ppt_NC (Var 0))"
proof -
  have tF: "[Prop] \<turnstile> App (pp_Pure Prop) (Var 0) : Prop" by (rule has_type.App[OF typed_pp_Pure]) (simp add: lookup_def)
  have tG: "[Prop] \<turnstile> App ppt_NC (Var 0) : Prop" by (rule has_type.App[OF ppt_NC_ty]) (simp add: lookup_def)
  have z: "zeta_body [] (App (pp_Pure Prop) (Var 0)) (App ppt_NC (Var 0)) = (App (pp_Pure Prop) (Var 0) \<longleftrightarrow>\<^sub>o App ppt_NC (Var 0))"
    by (simp add: zeta_body_def fresh_vars_def)
  have "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq (arrow_type [] Prop) (App (pp_Pure Prop) (Var 0)) (App ppt_NC (Var 0))"
    by (rule CEV_axiom_proves.VectorEquivalence) (use tF tG ppt_plus_iff[OF T] z in simp_all)
  then show ?thesis by simp
qed

text \<open>Generalization and necessitation: necessarily, for every p, Pure_t(p) = NC(p).\<close>

lemma ppt_plus_all:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ mf_condition Prop (pp_Pure Prop) ppt_NC"
proof -
  let ?Q = "Eq Prop (App (pp_Pure Prop) (Var 0)) (App ppt_NC (Var 0))"
  have tQ: "[Prop] \<turnstile> ?Q : Prop" using CEV_axiom_proves_formula[OF ppt_plus_pe[OF T]] .
  have q: "[Prop] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (shift ObjTrue) ?Q"
    by (rule ppt_plus_pc1[OF ppt_plus_pe[OF T]]) (use tQ typed_ObjTrue in \<open>auto simp: ppt_shift intro: has_type.Imp\<close>)
  have g: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Forall Prop ?Q)" by (rule CEV_axiom_proves.Gen[OF typed_ObjTrue tQ q])
  have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Forall Prop ?Q" by (rule CEV_axiom_proves.MP[OF ppt_plus_true g])
  then show ?thesis by (simp add: mf_condition_def ppt_shift)
qed

lemma ppt_plus_box:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (mf_condition Prop (pp_Pure Prop) ppt_NC)"
proof -
  let ?A = "mf_condition Prop (pp_Pure Prop) ppt_NC"
  have tA: "[] \<turnstile> ?A : Prop" by (rule typed_mf_condition[OF typed_pp_Pure ppt_NC_ty])
  have i: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (?A \<longleftrightarrow>\<^sub>o ObjTrue)"
    by (rule ppt_plus_pc1[OF ppt_plus_all[OF T]]) (use tA typed_ObjTrue in \<open>auto intro: has_type.Imp has_type.Conj\<close>)
  have i2: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ (?A \<longleftrightarrow>\<^sub>o ObjTrue)" by (rule CEV_axiom_proves.MP[OF ppt_plus_true i])
  have z: "zeta_body [] ?A ObjTrue = (?A \<longleftrightarrow>\<^sub>o ObjTrue)" by (simp add: zeta_body_def fresh_vars_def)
  have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq (arrow_type [] Prop) ?A ObjTrue"
    by (rule CEV_axiom_proves.VectorEquivalence) (use tA typed_ObjTrue i2 z in simp_all)
  then show ?thesis by (simp add: ObjBox_def)
qed

text \<open>Modalized Functionality: Pure_t = NC.\<close>

lemma ppt_plus_eq:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq rc_u (pp_Pure Prop) ppt_NC"
  by (rule CEV_axiom_proves.MP[OF ppt_plus_box[OF T]
    CEV_axiom_proves.Base[OF CEV_unary_modalized_functionality[OF typed_pp_Pure ppt_NC_ty]]])

text \<open>The purity schema at NC, and Leibniz's law: PP_t.\<close>

theorem ppt_plus:
  assumes T: "set ppt_L \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_purity_of_pure Prop"
proof -
  have lp: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ App rc_p ppt_NC" using ppt_ax[OF T, of "pp_pure rc_u ppt_NC"] by (simp add: ppt_L_def pp_pure_def)
  have sym: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq rc_u (pp_Pure Prop) ppt_NC) (Eq rc_u ppt_NC (pp_Pure Prop))"
    by (rule CEV_axiom_proves.Base[OF U_sub_CEV[OF U_eq_sym[OF typed_pp_Pure ppt_NC_ty]]])
  have LL: "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp (Eq rc_u ppt_NC (pp_Pure Prop)) (Imp (App rc_p ppt_NC) (App rc_p (pp_Pure Prop)))"
    by (rule CEV_axiom_proves.Base[OF U_sub_CEV[OF u_rc_LL[OF ppt_NC_ty typed_pp_Pure rc_p_ty]]])
  have "[] ; T \<turnstile>\<^sub>CEV\<^sup>+ App rc_p (pp_Pure Prop)"
    by (rule CEV_axiom_proves.MP[OF lp CEV_axiom_proves.MP[OF CEV_axiom_proves.MP[OF ppt_plus_eq[OF T] sym] LL]])
  then show ?thesis by (simp add: pp_purity_of_pure_def pp_pure_def)
qed

theorem ppt_plus_L: "[] ; set ppt_L \<turnstile>\<^sub>CEV\<^sup>+ pp_purity_of_pure Prop" by (rule ppt_plus) simp

theorem ppt_plus_CFP: "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_purity_of_pure Prop" by (rule ppt_plus[OF ppt_L_sub])

section \<open>4. PP_t in the model of C_FP\<close>

theorem ppt_valid: "k6_gv [] (pp_purity_of_pure Prop)"
  by (rule GenericExactBaconConstants.ExactBaconHenkin.CEV_axiom_soundness[OF k6_sound k6_zeta k6_model ppt_plus_CFP])

theorem ppt_model: "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set (insert (pp_purity_of_pure Prop) pp_CFP_axioms)"
  using k6_model k6_all[OF typed_pp_purity_of_pure ppt_valid]
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast

theorem ppt_k6: "\<not> [] ; insert (pp_purity_of_pure Prop) pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  using k6_local[of "[]" "insert (pp_purity_of_pure Prop) pp_CFP_axioms" ObjFalse] ppt_model
    GenericExactBaconConstants.ExactBaconHenkin.ObjFalse_not_gvalid
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast

theorem ppt_k6_plus: "CEV_axiom_consistent [] (insert (pp_purity_of_pure Prop) pp_CFP_axioms)"
  by (rule GenericExactBaconConstants.ExactBaconHenkin.CEV_axiom_consistent_of_gvalid[OF k6_sound k6_zeta ppt_model])

end
