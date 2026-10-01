theory Classicism_2_11_Rigid_Semantics
  imports Classicism_2_11_Order_Semantics
begin

section \<open>Generic semantics of Rigid and Rigid Comprehension at type t→t\<close>

text \<open>
  Rigid := λY.□∀X((∀z(Yz → □Xz)) ↔ Y ≤ X) and Rigid Comprehension
  ∀X∃Y(Rigid Y ∧ ∀z(Xz ↔ Yz)), pp.27–28, instantiated at σs = [t],
  so τ = t→t. In every action model over the standard stock, Rigid Y
  at a root arrow h expresses the reading below over all arrows i out
  of target h, with the value of Y moved along i; at the root identity
  this is exactly c211_prigid, and RC is exactly c211_pRC. Hence a
  model in which c211_pRC fails does not validate RC at t→t.
\<close>

subsection \<open>Quantifier reshaping\<close>

lemma c211_ball_explode_Elem: "(\<forall>x\<in>explode A. P x) \<longleftrightarrow> (\<forall>x. Elem x A \<longrightarrow> P x)"
  by (simp only: Ball_def explode_Elem)

lemma c211_bex_explode_Elem: "(\<exists>x\<in>explode A. P x) \<longleftrightarrow> (\<exists>x. Elem x A \<and> P x)"
  by (simp only: Bex_def explode_Elem)

lemma c211_all_reshape:
  "(\<forall>i. A i \<longrightarrow> B i \<longrightarrow> (\<forall>X. C i X \<longrightarrow> E i X)) \<longleftrightarrow> (\<forall>i X. A i \<longrightarrow> B i \<longrightarrow> C i X \<longrightarrow> E i X)"
  by blast

context c211_sem
begin

subsection \<open>The literal formulas at t→t\<close>

abbreviation rY :: nat where "rY \<equiv> c211_v (Arr Prop Prop) 14"
abbreviation rX :: nat where "rX \<equiv> c211_v (Arr Prop Prop) 15"
abbreviation rz :: nat where "rz \<equiv> c211_v Prop 20"
abbreviation rP :: nat where "rP \<equiv> c211_v (Arr Prop Prop) 16"
abbreviation rQ :: nat where "rQ \<equiv> c211_v (Arr Prop Prop) 17"

abbreviation rleft :: "'c paper_named_term" where
  "rleft \<equiv> named_paper_all Prop (NLam rz
    (c211_imp (NApp (NVar rY) (NVar rz)) (c211_box (NApp (NVar rX) (NVar rz)))))"

abbreviation rbody :: "'c paper_named_term" where
  "rbody \<equiv> c211_iff rleft (c211_le (Arr Prop Prop) (NVar rY) (NVar rX))"

abbreviation rbox :: "'c paper_named_term" where
  "rbox \<equiv> c211_box (named_paper_all (Arr Prop Prop) (NLam rX rbody))"

abbreviation rcoext :: "'c paper_named_term" where
  "rcoext \<equiv> named_paper_all Prop (NLam rz (c211_iff (NApp (NVar rP) (NVar rz)) (NApp (NVar rQ) (NVar rz))))"

lemma rigid_Prop: "(c211_rigid [Prop] :: 'c paper_named_term) = NLam rY rbox"
  by (simp only: c211_rigid_def c211_rtype_Prop c211_zs_Prop c211_vapp_def paper_R_all_vec.simps
    named_app_vec.simps list.map c211_v_type)

lemma RC_Prop: "(c211_RC [Prop] :: 'c paper_named_term) =
    named_paper_all (Arr Prop Prop) (NLam rP (named_paper_ex (Arr Prop Prop) (NLam rQ
      (named_paper_and (NApp (c211_rigid [Prop]) (NVar rQ)) rcoext))))"
  by (simp only: c211_RC_def c211_rtype_Prop c211_zs_Prop c211_vapp_def paper_R_all_vec.simps
    named_app_vec.simps list.map c211_v_type)

lemma tt_type: "paper_R_type (Arr Prop Prop)" and tt_relational: "paper_R_relational (Arr Prop Prop)"
  by (simp_all add: paper_R_relational_def)

lemma tr_value: "n v = Some a \<Longrightarrow> tr j n v = Some (T (c211_G v) j a)"
  by (simp add: paper_ZF_action_transport_assignment_def paper_hom_assignment_def)

lemma app_var_language:
  "c211_G f = Arr \<sigma> Prop \<Longrightarrow> c211_G x = \<sigma> \<Longrightarrow> paper_R_type (Arr \<sigma> Prop) \<Longrightarrow>
    lang (NApp (NVar f) (NVar x)) Prop"
  by (rule paper_R_language_App[OF paper_R_language_Var paper_R_language_Var]) simp_all

lemma sat_app_var:
  assumes arrow: "k \<in> explode Ar" and typed: "env (target k) n"
    and ft: "c211_G f = Arr \<sigma> Prop" and xt: "c211_G x = \<sigma>"
    and nf: "n f = Some F" and nx: "n x = Some a"
  shows "sat k n (NApp (NVar f) (NVar x)) \<longleftrightarrow> c211_pcur identity (target k) F a"
proof -
  have object: "target k \<in> Obj" by (rule C.target_object[OF arrow])
  have rt: "paper_R_type (Arr \<sigma> Prop)"
    using paper_ZF_action_env_assigned_R[OF typed nf] by (simp only: ft)
  have Fm: "F \<in> explode (D (Arr \<sigma> Prop) (target k))"
    using paper_ZF_action_env_value[OF typed nf] by (simp only: ft)
  have am: "a \<in> explode (D \<sigma> (target k))"
    using paper_ZF_action_env_value[OF typed nx] by (simp only: xt)
  have ef: "ev (NVar f) k n = Some F" by (simp only: paper_ZF_action_eval.simps nf)
  have ex: "ev (NVar x) k n = Some a" by (simp only: paper_ZF_action_eval.simps nx)
  show ?thesis by (simp only: sat_value[OF ev_app[OF object rt ef Fm ex am]] c211_pcur_def)
qed

subsection \<open>The left side ∀z(Yz → □Xz) and the body of Rigid\<close>

lemma rigid_left:
  assumes arrow: "k \<in> explode Ar" and origin: "source k = Root" and typed: "env (target k) m"
    and mY: "m rY = Some yy" and mX: "m rX = Some X"
  shows "sat k m rleft \<longleftrightarrow>
    (\<forall>z. Elem z (D Prop (target k)) \<longrightarrow> c211_pcur identity (target k) yy z \<longrightarrow>
      (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target k \<longrightarrow>
        c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))"
proof -
  let ?A = "NApp (NVar rY) (NVar rz) :: 'c paper_named_term"
  let ?B = "NApp (NVar rX) (NVar rz) :: 'c paper_named_term"
  have pp: "paper_R_type Prop" by simp
  have Al: "lang ?A Prop" by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  have Bl: "lang ?B Prop" by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  have bBl: "lang (c211_box ?B) Prop" by (rule paper_R_named_box_language[OF c211_rich Bl])
  have bodyl: "lang (c211_imp ?A (c211_box ?B)) Prop" by (rule c211_connective_language(3)[OF Al bBl])
  have la: "named_adequate m (NLam rz (c211_imp ?A (c211_box ?B)))"
    using mY mX by (auto simp: named_adequate_def c211_fv_simps)
  have point: "sat k (m(rz := Some z)) (c211_imp ?A (c211_box ?B)) \<longleftrightarrow>
      (c211_pcur identity (target k) yy z \<longrightarrow>
        (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target k \<longrightarrow>
          c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))"
    if zm: "z \<in> explode (D Prop (target k))" for z
  proof -
    let ?n = "m(rz := Some z)"
    have nt: "env (target k) ?n" by (rule paper_ZF_action_env_update[OF typed c211_v_type pp zm])
    have nY: "?n rY = Some yy" using mY by simp
    have nX: "?n rX = Some X" using mX by simp
    have nz: "?n rz = Some z" by simp
    have Aa: "named_adequate ?n ?A" and Ba: "named_adequate ?n ?B"
      using mY mX by (auto simp: named_adequate_def)
    have bBa: "named_adequate ?n (c211_box ?B)" using Ba by (simp only: named_adequate_def paper_R_named_box_fv)
    have s1: "sat k ?n ?A \<longleftrightarrow> c211_pcur identity (target k) yy z"
      by (rule sat_app_var[where f=rY and x=rz, OF arrow nt c211_v_type c211_v_type nY nz])
    have inner: "sat (compose j k) (tr j ?n) ?B \<longleftrightarrow>
        c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)"
      if ja: "j \<in> explode Ar" and js: "source j = target k" for j
    proof -
      note c = composite[OF arrow origin ja js]
      have st: "env (source j) ?n" using nt by (simp only: js)
      have ut: "env (target (compose j k)) (tr j ?n)"
        by (simp only: c(3); rule transported_env[OF ja st])
      have uX: "tr j ?n rX = Some (T (Arr Prop Prop) j X)" using tr_value[where n="?n" and v=rX, OF nX] by (simp only: c211_v_type)
      have uz: "tr j ?n rz = Some (T Prop j z)" using tr_value[where n="?n" and v=rz, OF nz] by (simp only: c211_v_type)
      show ?thesis
        by (simp only: sat_app_var[where f=rX and x=rz, OF c(1) ut c211_v_type c211_v_type uX uz] c(3))
    qed
    have s2: "sat k ?n (c211_box ?B) \<longleftrightarrow>
        (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target k \<longrightarrow>
          c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z))"
      using inner by (simp only: sat_box[OF arrow origin nt Bl Ba]) blast
    show ?thesis by (simp only: sat_imp[OF arrow origin nt Al bBl Aa bBa] s1 s2)
  qed
  have "sat k m rleft \<longleftrightarrow>
      (\<forall>z\<in>explode (D Prop (target k)). sat k (m(rz := Some z)) (c211_imp ?A (c211_box ?B)))"
    by (rule sat_all[OF arrow origin typed bodyl c211_v_type pp la])
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D Prop (target k)). c211_pcur identity (target k) yy z \<longrightarrow>
      (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target k \<longrightarrow>
        c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))"
    by (rule ball_cong[OF refl point])
  finally show ?thesis by (simp only: c211_ball_explode_Elem)
qed

lemma rleft_language: "lang rleft Prop"
proof -
  have Al: "lang (NApp (NVar rY) (NVar rz) :: 'c paper_named_term) Prop"
    by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  have Bl: "lang (NApp (NVar rX) (NVar rz) :: 'c paper_named_term) Prop"
    by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  show ?thesis
    by (rule c211_all_language[OF _ c211_connective_language(3)[OF Al
      paper_R_named_box_language[OF c211_rich Bl]]]) simp
qed

lemma rbody_language: "lang rbody Prop"
  by (rule c211_connective_language(4)[OF rleft_language
    c211_le_language[OF tt_relational c211_lang_Var[OF tt_type] c211_lang_Var[OF tt_type]]])

lemma rigid_body:
  assumes arrow: "k \<in> explode Ar" and origin: "source k = Root" and typed: "env (target k) m"
    and mY: "m rY = Some yy" and mX: "m rX = Some X"
  shows "sat k m rbody \<longleftrightarrow>
    ((\<forall>z. Elem z (D Prop (target k)) \<longrightarrow> c211_pcur identity (target k) yy z \<longrightarrow>
      (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target k \<longrightarrow>
        c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
     \<longleftrightarrow> ple (Arr Prop Prop) (target k) yy X)"
proof -
  let ?R = "c211_le (Arr Prop Prop) (NVar rY) (NVar rX) :: 'c paper_named_term"
  have Rl: "lang ?R Prop"
    by (rule c211_le_language[OF tt_relational c211_lang_Var[OF tt_type] c211_lang_Var[OF tt_type]])
  have La: "named_adequate m rleft" and Ra: "named_adequate m ?R"
    using mY mX by (auto simp: named_adequate_def c211_fv_simps)
  have eY: "ev (NVar rY) k m = Some yy" by (simp only: paper_ZF_action_eval.simps mY)
  have eX: "ev (NVar rX) k m = Some X" by (simp only: paper_ZF_action_eval.simps mX)
  show ?thesis
    by (simp only: sat_iff[OF arrow origin typed rleft_language Rl La Ra]
      rigid_left[OF arrow origin typed mY mX]
      le_holds[OF tt_relational c211_lang_Var[OF tt_type] c211_lang_Var[OF tt_type]
        arrow origin typed Ra eY eX])
qed

subsection \<open>G1: Rigid Y at a root arrow\<close>

theorem rigid_holds:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and yl: "lang Y (Arr Prop Prop)" and adequate: "named_adequate g (NApp (c211_rigid [Prop]) Y)"
    and ye: "ev Y h g = Some y"
  shows "sat h g (NApp (c211_rigid [Prop]) Y) \<longleftrightarrow>
    (\<forall>i X. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> Elem X (D (Arr Prop Prop) (target i)) \<longrightarrow>
      ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
          c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
          (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
            c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
       \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X))"
proof -
  let ?Al = "named_paper_all (Arr Prop Prop) (NLam rX rbody)"
  let ?g = "g(rY := Some y)"
  have ya: "named_adequate g Y" using adequate by (simp add: named_adequate_def)
  have ym: "y \<in> explode (D (Arr Prop Prop) (target h))" by (rule ev_member[OF yl arrow origin typed ya ye])
  have lt: "list_all paper_R_type [Prop]" by simp
  have rl: "lang (c211_rigid [Prop]) (Arr (Arr Prop Prop) Prop)"
    using c211_rigid_language[OF lt, of \<Sigma>] by (simp only: c211_rtype_Prop)
  have ll: "lang (NLam rY rbox) (Arr (Arr Prop Prop) Prop)" using rl by (simp only: rigid_Prop)
  have cl: "named_fv (c211_rigid [Prop] :: 'c paper_named_term) = {}" by (rule c211_rigid_closed)
  have la: "named_adequate g (NLam rY rbox)"
    using cl by (simp only: named_adequate_def rigid_Prop empty_subsetI)
  have red: "ev (NApp (c211_rigid [Prop]) Y) h g = ev rbox h ?g"
    by (simp only: rigid_Prop; rule ev_beta[OF arrow origin typed ll c211_v_type yl la ya ye])
  have gt: "env (target h) ?g" by (rule paper_ZF_action_env_update[OF typed c211_v_type tt_type ym])
  have All: "lang ?Al Prop" by (rule c211_all_language[OF tt_type rbody_language])
  have Ala: "named_adequate ?g ?Al" by (auto simp: named_adequate_def c211_fv_simps)
  have per_i: "sat (compose i h) (tr i ?g) ?Al \<longleftrightarrow>
      (\<forall>X. Elem X (D (Arr Prop Prop) (target i)) \<longrightarrow>
        ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
            c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
            (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
              c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
         \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X))"
    if ia: "i \<in> explode Ar" and meet: "source i = target h" for i
  proof -
    let ?k = "compose i h" and ?u = "tr i ?g"
    note c = composite[OF arrow origin ia meet]
    have st: "env (source i) ?g" using gt by (simp only: meet)
    have ut: "env (target ?k) ?u" by (simp only: c(3); rule transported_env[OF ia st])
    have uY: "?u rY = Some (T (Arr Prop Prop) i y)"
      using tr_value[of ?g rY y i] by (simp only: c211_v_type fun_upd_same)
    have ua: "named_adequate ?u (NLam rX rbody)"
      using uY by (auto simp: named_adequate_def c211_fv_simps)
    have each: "sat ?k (?u(rX := Some X)) rbody \<longleftrightarrow>
        ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
            c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
            (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
              c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
         \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X)"
      if Xm: "X \<in> explode (D (Arr Prop Prop) (target ?k))" for X
    proof -
      have mt: "env (target ?k) (?u(rX := Some X))"
        by (rule paper_ZF_action_env_update[OF ut c211_v_type tt_type Xm])
      have mY: "(?u(rX := Some X)) rY = Some (T (Arr Prop Prop) i y)" using uY by simp
      have mX: "(?u(rX := Some X)) rX = Some X" by simp
      show ?thesis by (simp only: rigid_body[OF c(1) c(2) mt mY mX] c(3))
    qed
    have "sat ?k ?u ?Al \<longleftrightarrow> (\<forall>X\<in>explode (D (Arr Prop Prop) (target ?k)). sat ?k (?u(rX := Some X)) rbody)"
      by (rule sat_all[OF c(1) c(2) ut rbody_language c211_v_type tt_type ua])
    also have "\<dots> \<longleftrightarrow> (\<forall>X\<in>explode (D (Arr Prop Prop) (target ?k)).
        ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
            c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
            (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
              c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
         \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X))"
      by (rule ball_cong[OF refl each])
    finally show ?thesis by (simp only: c(3) c211_ball_explode_Elem)
  qed
  have "sat h g (NApp (c211_rigid [Prop]) Y) \<longleftrightarrow> sat h ?g rbox" by (rule sat_ev_cong[OF red])
  also have "\<dots> \<longleftrightarrow> (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> sat (compose i h) (tr i ?g) ?Al)"
    by (rule sat_box[OF arrow origin gt All Ala])
  also have "\<dots> \<longleftrightarrow> (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow>
      (\<forall>X. Elem X (D (Arr Prop Prop) (target i)) \<longrightarrow>
        ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
            c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
            (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
              c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
         \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X)))"
    using per_i by (simp only: cong: imp_cong)
  also have "\<dots> \<longleftrightarrow> (\<forall>i X. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> Elem X (D (Arr Prop Prop) (target i)) \<longrightarrow>
      ((\<forall>z. Elem z (D Prop (target i)) \<longrightarrow>
          c211_pcur identity (target i) (T (Arr Prop Prop) i y) z \<longrightarrow>
          (\<forall>j. j \<in> explode Ar \<longrightarrow> source j = target i \<longrightarrow>
            c211_pcur identity (target j) (T (Arr Prop Prop) j X) (T Prop j z)))
       \<longleftrightarrow> ple (Arr Prop Prop) (target i) (T (Arr Prop Prop) i y) X))"
    by (rule c211_all_reshape)
  finally show ?thesis .
qed

subsection \<open>G2: Rigid Comprehension at the root\<close>

theorem RC_holds_root:
  assumes typed: "env Root g"
  shows "sat (identity Root) g (c211_RC [Prop]) \<longleftrightarrow> c211_pRC Ar source target identity D T Root"
proof -
  note r = c211_root_identity[OF model]
  let ?e = "identity Root"
  let ?Rg = "NApp (c211_rigid [Prop]) (NVar rQ) :: 'c paper_named_term"
  let ?Ex = "named_paper_ex (Arr Prop Prop) (NLam rQ (named_paper_and ?Rg rcoext))"
  have pp: "paper_R_type Prop" by simp
  have et: "env (target ?e) g" by (simp only: r(3); rule typed)
  have lt: "list_all paper_R_type [Prop]" by simp
  have rl: "lang (c211_rigid [Prop]) (Arr (Arr Prop Prop) Prop)"
    using c211_rigid_language[OF lt, of \<Sigma>] by (simp only: c211_rtype_Prop)
  have Rgl: "lang ?Rg Prop" by (rule paper_R_language_App[OF rl c211_lang_Var[OF tt_type]])
  have Pl: "lang (NApp (NVar rP) (NVar rz) :: 'c paper_named_term) Prop"
    by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  have Ql: "lang (NApp (NVar rQ) (NVar rz) :: 'c paper_named_term) Prop"
    by (rule app_var_language[OF c211_v_type c211_v_type tt_type])
  have iffl: "lang (c211_iff (NApp (NVar rP) (NVar rz)) (NApp (NVar rQ) (NVar rz)) :: 'c paper_named_term) Prop"
    by (rule c211_connective_language(4)[OF Pl Ql])
  have Cl: "lang rcoext Prop" by (rule c211_all_language[OF pp iffl])
  have andl: "lang (named_paper_and ?Rg rcoext) Prop" by (rule paper_R_named_and_language[OF Rgl Cl])
  have Exl: "lang ?Ex Prop" by (rule c211_ex_language[OF tt_type andl])
  have cl: "named_fv (c211_rigid [Prop] :: 'c paper_named_term) = {}" by (rule c211_rigid_closed)
  have Exa: "named_adequate g (NLam rP ?Ex)" using cl by (auto simp: named_adequate_def c211_fv_simps)
  have per_x: "sat ?e (g(rP := Some x)) ?Ex \<longleftrightarrow>
      (\<exists>y. Elem y (D (Arr Prop Prop) Root) \<and> c211_prigid Ar source target identity D T Root y \<and>
        (\<forall>z. Elem z (D Prop Root) \<longrightarrow> (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z)))"
    if xm: "x \<in> explode (D (Arr Prop Prop) (target ?e))" for x
  proof -
    let ?m = "g(rP := Some x)"
    have mt: "env (target ?e) ?m" by (rule paper_ZF_action_env_update[OF et c211_v_type tt_type xm])
    have ma: "named_adequate ?m (NLam rQ (named_paper_and ?Rg rcoext))"
      using cl by (auto simp: named_adequate_def c211_fv_simps)
    have per_y: "sat ?e (?m(rQ := Some y)) (named_paper_and ?Rg rcoext) \<longleftrightarrow>
        c211_prigid Ar source target identity D T Root y \<and>
        (\<forall>z. Elem z (D Prop Root) \<longrightarrow> (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z))"
      if ym: "y \<in> explode (D (Arr Prop Prop) (target ?e))" for y
    proof -
      let ?n = "?m(rQ := Some y)"
      have nt: "env (target ?e) ?n" by (rule paper_ZF_action_env_update[OF mt c211_v_type tt_type ym])
      have nP: "?n rP = Some x" by simp
      have nQ: "?n rQ = Some y" by simp
      have Rga: "named_adequate ?n ?Rg" using cl by (auto simp: named_adequate_def)
      have Ca: "named_adequate ?n rcoext" by (auto simp: named_adequate_def c211_fv_simps)
      have eQ: "ev (NVar rQ) ?e ?n = Some y" by (simp only: paper_ZF_action_eval.simps nQ)
      have rig: "sat ?e ?n ?Rg \<longleftrightarrow> c211_prigid Ar source target identity D T Root y"
        by (simp only: rigid_holds[OF r(1) r(2) nt c211_lang_Var[OF tt_type] Rga eQ] r(3)
          c211_prigid_def)
      have co_z: "sat ?e (?n(rz := Some z)) (c211_iff (NApp (NVar rP) (NVar rz)) (NApp (NVar rQ) (NVar rz))) \<longleftrightarrow>
          (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z)"
        if zm: "z \<in> explode (D Prop (target ?e))" for z
      proof -
        let ?o = "?n(rz := Some z)"
        have ot: "env (target ?e) ?o" by (rule paper_ZF_action_env_update[OF nt c211_v_type pp zm])
        have oP: "?o rP = Some x" and oQ: "?o rQ = Some y" and oz: "?o rz = Some z" by simp_all
        have Pa: "named_adequate ?o (NApp (NVar rP) (NVar rz))"
          and Qa: "named_adequate ?o (NApp (NVar rQ) (NVar rz))"
          by (auto simp: named_adequate_def)
        show ?thesis
          by (simp only: sat_iff[OF r(1) r(2) ot Pl Ql Pa Qa]
            sat_app_var[where f=rP and x=rz, OF r(1) ot c211_v_type c211_v_type oP oz]
            sat_app_var[where f=rQ and x=rz, OF r(1) ot c211_v_type c211_v_type oQ oz] r(3))
      qed
      have na: "named_adequate ?n (NLam rz (c211_iff (NApp (NVar rP) (NVar rz)) (NApp (NVar rQ) (NVar rz))))"
        by (auto simp: named_adequate_def c211_fv_simps)
      have co: "sat ?e ?n rcoext \<longleftrightarrow>
          (\<forall>z. Elem z (D Prop Root) \<longrightarrow> (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z))"
      proof -
        have "sat ?e ?n rcoext \<longleftrightarrow> (\<forall>z\<in>explode (D Prop (target ?e)).
            sat ?e (?n(rz := Some z)) (c211_iff (NApp (NVar rP) (NVar rz)) (NApp (NVar rQ) (NVar rz))))"
          by (rule sat_all[OF r(1) r(2) nt iffl c211_v_type pp na])
        also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D Prop (target ?e)).
            (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z))"
          by (rule ball_cong[OF refl co_z])
        finally show ?thesis by (simp only: r(3) c211_ball_explode_Elem)
      qed
      show ?thesis by (simp only: sat_and[OF r(1) r(2) nt Rgl Cl Rga Ca] rig co)
    qed
    have "sat ?e ?m ?Ex \<longleftrightarrow> (\<exists>y\<in>explode (D (Arr Prop Prop) (target ?e)).
        sat ?e (?m(rQ := Some y)) (named_paper_and ?Rg rcoext))"
      by (rule sat_ex[OF r(1) r(2) mt andl c211_v_type tt_type ma])
    also have "\<dots> \<longleftrightarrow> (\<exists>y\<in>explode (D (Arr Prop Prop) (target ?e)).
        c211_prigid Ar source target identity D T Root y \<and>
        (\<forall>z. Elem z (D Prop Root) \<longrightarrow> (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z)))"
      by (rule bex_cong[OF refl per_y])
    finally show ?thesis by (simp only: r(3) c211_bex_explode_Elem)
  qed
  have "sat ?e g (c211_RC [Prop]) \<longleftrightarrow>
      (\<forall>x\<in>explode (D (Arr Prop Prop) (target ?e)). sat ?e (g(rP := Some x)) ?Ex)"
    by (simp only: RC_Prop; rule sat_all[OF r(1) r(2) et Exl c211_v_type tt_type Exa])
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>explode (D (Arr Prop Prop) (target ?e)).
      (\<exists>y. Elem y (D (Arr Prop Prop) Root) \<and> c211_prigid Ar source target identity D T Root y \<and>
        (\<forall>z. Elem z (D Prop Root) \<longrightarrow> (c211_pcur identity Root x z \<longleftrightarrow> c211_pcur identity Root y z))))"
    by (rule ball_cong[OF refl per_x])
  also have "\<dots> \<longleftrightarrow> c211_pRC Ar source target identity D T Root"
    by (simp only: r(3) c211_ball_explode_Elem c211_pRC_def)
  finally show ?thesis .
qed

subsection \<open>G3: failure of c211_pRC refutes the validity of RC at t→t\<close>

theorem RC_not_valid:
  assumes fails: "\<not> c211_pRC Ar source target identity D T Root"
  shows "\<not> c211_valid \<Sigma> c211_G Ar source target compose identity Root D T I (c211_RC [Prop])"
proof
  assume valid: "c211_valid \<Sigma> c211_G Ar source target compose identity Root D T I (c211_RC [Prop])"
  note r = c211_root_identity[OF model]
  have et: "env (target (identity Root)) Map.empty" by (rule paper_ZF_action_env_empty)
  have cl: "named_fv (c211_RC [Prop] :: 'c paper_named_term) = {}" by (rule c211_RC_closed)
  have ea: "named_adequate Map.empty (c211_RC [Prop] :: 'c paper_named_term)"
    by (simp only: named_adequate_def cl empty_subsetI)
  have "sat (identity Root) Map.empty (c211_RC [Prop])"
    using valid et ea unfolding c211_valid_def by blast
  then have "c211_pRC Ar source target identity D T Root"
    by (simp only: RC_holds_root[OF paper_ZF_action_env_empty])
  then show False using fails by contradiction
qed

end

subsection \<open>Exported endpoints\<close>

lemmas c211_rigid_holds = c211_sem.rigid_holds[unfolded c211_sem_def]
lemmas c211_RC_holds_root = c211_sem.RC_holds_root[unfolded c211_sem_def]
lemmas c211_RC_not_valid = c211_sem.RC_not_valid[unfolded c211_sem_def]

text \<open>
  Sources: Rigid and Rigid Comprehension, pp.27–28; Figure 1, p.6;
  Definitions 3.18–3.20, pp.55–56. These are generic: they hold in
  every action model over the standard stock and do not by themselves
  assert that c211_pRC fails in the concrete Proposition 2.11 model.
\<close>

ML \<open>
  val c211_rigid_semantics_names = ["c211_rigid_holds", "c211_RC_holds_root", "c211_RC_not_valid",
    "c211_sem.rigid_left", "c211_sem.rigid_body", "c211_sem.sat_app_var", "c211_sem.rigid_Prop",
    "c211_sem.RC_Prop"];
  val facts = map (Proof_Context.get_thm \<^context>) c211_rigid_semantics_names;
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln ("C211-RIGID-SEMANTICS: " ^ string_of_int (length facts) ^
    " clean generic endpoints (Rigid at t→t, RC at the root, RC refutation criterion)");
\<close>

end
