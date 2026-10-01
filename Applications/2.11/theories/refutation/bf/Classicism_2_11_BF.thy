theory Classicism_2_11_BF
  imports "Classicism_2_11_Formulas.Classicism_2_11_Extension" "Classicism_2_11_Formulas.Classicism_2_11_Syntax"
    "Classicism_2_11_Formulas.Classicism_2_11_World_Cases"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Box_Truth"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Binder_Truth"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Logical_Truth"
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Model_Truth_Separation"
begin

section \<open>Proposition 3.24(ii): BF from root-arrow surjectivity\<close>

text \<open>
  Source: Bacon–Dorr, Classicism, Proposition 3.24(ii) and footnote 80
  (p.58). In any action model over the standard stock, if every element
  of D σ at the target of a root arrow h is the transport along h of an
  element of D σ at the root, then BF at σ, ∀x□P → □∀xP, is true at the
  identity arrow of the root under every typed adequate assignment.

  Proof. Suppose ∀x□P holds at the root under g. Let h be a root arrow
  and a ∈ D σ (target h). Choose b at the root with T σ h b = a. Then □P
  holds at the root under g(x:=b), so P holds at h∘id under the
  transport of g(x:=b) along h, which is (h∘g)(x:=a). Hence ∀xP holds at
  h∘id under h∘g, for every root arrow h; that is, □∀xP holds at the root.

  The truth clauses below are read off the BBK model of each root arrow.
  The clause for □ (truth along every outgoing arrow) is derived from
  the BBK box clause, □P iff P denotes the same proposition as P ∨ ¬P,
  and the naturality test for membership of outgoing arrows.
\<close>

subsection \<open>Truth clauses at root arrows\<close>

locale c211_bf_sem =
  fixes \<Sigma> :: "'c ssignature" and Obj :: "'o set" and Ar :: ZF
    and source :: "ZF \<Rightarrow> 'o" and target :: "ZF \<Rightarrow> 'o"
    and compose :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" and identity :: "'o \<Rightarrow> ZF" and Root :: 'o
    and D :: "otype \<Rightarrow> 'o \<Rightarrow> ZF" and T :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF"
    and I :: "otype \<Rightarrow> 'c \<Rightarrow> ZF"
  assumes model: "paper_ZF_action_model \<Sigma> c211_G Obj Ar source target compose identity Root D T I"
begin

abbreviation ev :: "'c paper_named_term \<Rightarrow> ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option" where
  "ev A h g \<equiv> paper_ZF_action_eval Ar source target compose identity D T I c211_G A h g"

abbreviation sat :: "ZF \<Rightarrow> ZF named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "sat h g P \<equiv> paper_ZF_action_holds Ar source target compose identity D T I c211_G h g P"

abbreviation tr :: "ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF named_assignment" where
  "tr i g \<equiv> paper_ZF_action_transport_assignment c211_G T i g"

abbreviation env :: "'o \<Rightarrow> ZF named_assignment \<Rightarrow> bool" where
  "env W g \<equiv> paper_ZF_action_env_typed D c211_G W g"

abbreviation lang :: "'c paper_named_term \<Rightarrow> otype \<Rightarrow> bool" where
  "lang A \<tau> \<equiv> paper_R_in_language \<Sigma> c211_G A \<tau>"

abbreviation den :: "ZF \<Rightarrow> ZF named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> ZF" where
  "den h \<equiv> paper_ZF_action_bbk_denote Ar source target compose identity D T I c211_G h"

abbreviation val :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "val h \<equiv> paper_ZF_action_bbk_valuation target identity h"

abbreviation bdom :: "ZF \<Rightarrow> otype \<Rightarrow> ZF set" where
  "bdom h \<equiv> paper_ZF_action_bbk_domain D (target h)"

lemma premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity Root D T I"
  using model unfolding paper_ZF_action_model_def by blast

sublocale C: paper_rooted_category Obj "explode Ar" source target compose identity Root
  using premodel unfolding paper_ZF_action_premodel_def by blast

lemma bbk:
  "h \<in> explode Ar \<Longrightarrow> source h = Root \<Longrightarrow> paper_R_bbk_model \<Sigma> c211_G (bdom h) (den h) (val h)"
  by (rule paper_ZF_action_to_R_bbk_model[OF model])

lemma btyped: "env W g \<Longrightarrow> named_env_typed (paper_ZF_action_bbk_domain D W) c211_G g"
  by (rule iffD2[OF paper_ZF_action_bbk_env_iff])

lemma composite:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and ia: "i \<in> explode Ar" and meet: "source i = target h"
  shows "compose i h \<in> explode Ar" "source (compose i h) = Root" "target (compose i h) = target i"
proof -
  have meeting: "target h = source i" by (rule meet[symmetric])
  show "compose i h \<in> explode Ar" by (rule C.compose_arrow[OF arrow ia meeting])
  show "source (compose i h) = Root" by (simp only: C.compose_source[OF arrow ia meeting] origin)
  show "target (compose i h) = target i" by (rule C.compose_target[OF arrow ia meeting])
qed

lemma transported_env:
  assumes ia: "i \<in> explode Ar" and typed: "env (source i) g"
  shows "env (target i) (tr i g)"
  by (rule paper_ZF_premodel_transport_env_typed[OF premodel ia typed])

lemma ev_value:
  assumes "lang A \<rho>" "h \<in> explode Ar" "source h = Root" "env (target h) g" "named_adequate g A"
  obtains v where "ev A h g = Some v" "v \<in> explode (D \<rho> (target h))"
  by (rule paper_ZF_action_model_eval_value[OF model assms])

lemma sat_bbk:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and aa: "named_adequate g A"
  shows "sat h g A \<longleftrightarrow> val h (den h g A)"
  by (rule paper_ZF_action_bbk_holds_iff[OF model al arrow origin btyped[OF typed] aa])

lemma den_value: "ev A h g = Some a \<Longrightarrow> den h g A = a"
  by (simp only: paper_ZF_action_bbk_denote_def option.sel)

lemma sat_not:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and aa: "named_adequate g A"
  shows "sat h g (named_paper_not A) \<longleftrightarrow> \<not> sat h g A"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have nl: "lang (named_paper_not A) Prop" by (rule paper_R_named_not_language[OF al])
  have na: "named_adequate g (named_paper_not A)"
    using aa by (simp only: named_adequate_def named_paper_primitive_fv)
  show ?thesis
    by (simp only: sat_bbk[OF arrow origin typed nl na] sat_bbk[OF arrow origin typed al aa]
      M.paper_R_named_not_truth[OF al btyped[OF typed] aa])
qed

lemma sat_or:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and bl: "lang B Prop"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "sat h g (named_paper_or A B) \<longleftrightarrow> sat h g A \<or> sat h g B"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have cl: "lang (named_paper_or A B) Prop" by (rule paper_R_named_or_language[OF al bl])
  have ca: "named_adequate g (named_paper_or A B)"
    using aa ba by (simp only: named_adequate_def named_paper_primitive_fv Un_subset_iff; rule conjI)
  show ?thesis
    by (simp only: sat_bbk[OF arrow origin typed cl ca] sat_bbk[OF arrow origin typed al aa]
      sat_bbk[OF arrow origin typed bl ba] M.paper_R_named_or_truth[OF al bl btyped[OF typed] aa ba])
qed

lemma sat_imp:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and bl: "lang B Prop"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "sat h g (c211_imp A B) \<longleftrightarrow> (sat h g A \<longrightarrow> sat h g B)"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have cl: "lang (c211_imp A B) Prop" by (rule c211_connective_language(3)[OF al bl])
  have ca: "named_adequate g (c211_imp A B)"
    using aa ba by (simp only: named_adequate_def named_paper_defined_fv Un_subset_iff; rule conjI)
  show ?thesis
    by (simp only: sat_bbk[OF arrow origin typed cl ca] sat_bbk[OF arrow origin typed al aa]
      sat_bbk[OF arrow origin typed bl ba] M.paper_R_named_paper_imp_truth[OF al bl btyped[OF typed] aa ba])
qed

lemma sat_all:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and body: "lang A Prop" and nt: "c211_G n = \<sigma>" and rt: "paper_R_type \<sigma>"
    and adequate: "named_adequate g (NLam n A)"
  shows "sat h g (named_paper_all \<sigma> (NLam n A)) \<longleftrightarrow>
    (\<forall>a\<in>explode (D \<sigma> (target h)). sat h (g(n := Some a)) A)"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have ql: "lang (named_paper_all \<sigma> (NLam n A)) Prop"
    by (rule paper_R_named_all_binder_language[OF body nt rt])
  have qa: "named_adequate g (named_paper_all \<sigma> (NLam n A))"
    using adequate by (simp add: named_adequate_def named_paper_all_def)
  have inst: "val h (den h (g(n := Some a)) A) \<longleftrightarrow> sat h (g(n := Some a)) A"
    if am: "a \<in> explode (D \<sigma> (target h))" for a
  proof -
    have ut: "env (target h) (g(n := Some a))" by (rule paper_ZF_action_env_update[OF typed nt rt am])
    have ua: "named_adequate (g(n := Some a)) A"
      by (rule iffD2[OF named_binder_update_adequate_iff adequate])
    show ?thesis by (rule sym, rule sat_bbk[OF arrow origin ut body ua])
  qed
  have "sat h g (named_paper_all \<sigma> (NLam n A)) \<longleftrightarrow> val h (den h g (named_paper_all \<sigma> (NLam n A)))"
    by (rule sat_bbk[OF arrow origin typed ql qa])
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>bdom h \<sigma>. val h (den h (g(n := Some a)) A))"
    by (rule M.paper_R_forall_binder_truth[OF body nt rt btyped[OF typed] adequate])
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>explode (D \<sigma> (target h)). sat h (g(n := Some a)) A)"
    by (rule ball_cong[OF paper_ZF_action_bbk_domain_R[OF rt] inst])
  finally show ?thesis .
qed

lemma sat_taut:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and pl: "lang P Prop" and pa: "named_adequate g P"
  shows "sat h g (named_paper_or P (named_paper_not P))"
proof -
  have nl: "lang (named_paper_not P) Prop" by (rule paper_R_named_not_language[OF pl])
  have na: "named_adequate g (named_paper_not P)"
    using pa by (simp only: named_adequate_def named_paper_primitive_fv)
  show ?thesis
    by (simp only: sat_or[OF arrow origin typed pl nl pa na] sat_not[OF arrow origin typed pl pa]; blast)
qed

text \<open>Necessity at a root arrow h quantifies over the arrows out of target h.\<close>

theorem sat_box:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and pl: "lang P Prop" and pa: "named_adequate g P"
  shows "sat h g (c211_box P) \<longleftrightarrow>
    (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> sat (compose i h) (tr i g) P)"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  let ?Q = "named_paper_or P (named_paper_not P)"
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have ql: "lang ?Q Prop"
    by (rule paper_R_named_or_language[OF pl paper_R_named_not_language[OF pl]])
  have qa: "named_adequate g ?Q"
    using pa by (simp only: named_adequate_def named_paper_primitive_fv Un_absorb)
  have bl: "lang (c211_box P) Prop" by (rule paper_R_named_box_language[OF c211_rich pl])
  have ba: "named_adequate g (c211_box P)"
    using pa by (simp only: named_adequate_def paper_R_named_box_fv)
  obtain p where pe: "ev P h g = Some p" and pm: "p \<in> explode (D Prop (target h))"
    by (rule ev_value[OF pl arrow origin typed pa])
  obtain t where te: "ev ?Q h g = Some t" and tm: "t \<in> explode (D Prop (target h))"
    by (rule ev_value[OF ql arrow origin typed qa])
  have tests: "Elem i p \<longleftrightarrow> sat (compose i h) (tr i g) P" "Elem i t"
    if ia: "i \<in> explode Ar" and meet: "source i = target h" for i
  proof -
    have meeting: "target h = source i" by (rule meet[symmetric])
    note c = composite[OF arrow origin ia meet]
    have st: "env (source i) g" using typed by (simp only: meet)
    have ut: "env (target (compose i h)) (tr i g)"
      by (simp only: c(3); rule transported_env[OF ia st])
    have ua: "named_adequate (tr i g) P" by (simp only: paper_ZF_action_transport_adequate_iff; rule pa)
    have ptest: "sat (compose i h) (tr i g) P \<longleftrightarrow> Elem i p"
      by (rule paper_ZF_action_model_formula_outgoing_truth[OF model pl arrow origin typed pa pe ia meeting])
    have ttest: "sat (compose i h) (tr i g) ?Q \<longleftrightarrow> Elem i t"
      by (rule paper_ZF_action_model_formula_outgoing_truth[OF model ql arrow origin typed qa te ia meeting])
    have taut: "sat (compose i h) (tr i g) ?Q" by (rule sat_taut[OF c(1) c(2) ut pl ua])
    show "Elem i p \<longleftrightarrow> sat (compose i h) (tr i g) P" by (rule sym[OF ptest])
    show "Elem i t" by (rule iffD1[OF ttest taut])
  qed
  have "sat h g (c211_box P) \<longleftrightarrow> val h (den h g (c211_box P))"
    by (rule sat_bbk[OF arrow origin typed bl ba])
  also have "\<dots> \<longleftrightarrow> den h g P = den h g ?Q"
    by (rule M.paper_R_named_box_truth[OF pl btyped[OF typed] pa])
  also have "\<dots> \<longleftrightarrow> p = t" by (simp only: den_value[OF pe] den_value[OF te])
  also have "\<dots> \<longleftrightarrow> (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> Elem i p)"
  proof
    assume eq: "p = t"
    show "\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> Elem i p"
    proof (intro allI impI)
      fix i
      assume ia: "i \<in> explode Ar" and meet: "source i = target h"
      show "Elem i p" by (simp only: eq; rule tests(2)[OF ia meet])
    qed
  next
    assume all: "\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> Elem i p"
    show "p = t"
    proof (rule iffD2[OF Ext], intro allI)
      fix j
      show "Elem j p \<longleftrightarrow> Elem j t"
      proof
        assume jp: "Elem j p"
        have legit: "j \<in> explode Ar \<and> source j = target h"
          by (rule paper_ZF_premodel_proposition_member[OF premodel object pm jp])
        show "Elem j t" by (rule tests(2)[OF conjunct1[OF legit] conjunct2[OF legit]])
      next
        assume jt: "Elem j t"
        have legit: "j \<in> explode Ar \<and> source j = target h"
          by (rule paper_ZF_premodel_proposition_member[OF premodel object tm jt])
        show "Elem j p" using all legit by blast
      qed
    qed
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>i. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> sat (compose i h) (tr i g) P)"
    using tests(1) by blast
  finally show ?thesis .
qed

subsection \<open>BF at the root\<close>

lemma bf_adequacy:
  assumes "named_adequate g (c211_BF \<sigma> n P)"
  shows "named_adequate g (NLam n P)" "named_adequate g (NLam n (c211_box P))"
    "named_adequate g (named_paper_all \<sigma> (NLam n (c211_box P)))"
    "named_adequate g (named_paper_all \<sigma> (NLam n P))"
    "named_adequate g (c211_box (named_paper_all \<sigma> (NLam n P)))"
  using assms
  by (simp_all add: named_adequate_def c211_BF_fv named_paper_all_def paper_R_named_box_fv)

theorem bf_root:
  assumes rt: "paper_R_type \<sigma>" and nt: "c211_G n = \<sigma>" and pl: "lang P Prop"
    and onto: "\<forall>h y. h \<in> explode Ar \<longrightarrow> source h = Root \<longrightarrow> Elem y (D \<sigma> (target h)) \<longrightarrow>
      (\<exists>x. Elem x (D \<sigma> Root) \<and> T \<sigma> h x = y)"
    and typed: "env Root g" and adequate: "named_adequate g (c211_BF \<sigma> n P)"
  shows "sat (identity Root) g (c211_BF \<sigma> n P)"
proof -
  let ?h = "identity Root"
  have arrow: "?h \<in> explode Ar" by (rule C.identity_arrow[OF C.root_object])
  have origin: "source ?h = Root" by (rule C.identity_source[OF C.root_object])
  have goal: "target ?h = Root" by (rule C.identity_target[OF C.root_object])
  have ht: "env (target ?h) g" by (simp only: goal typed)
  note ad = bf_adequacy[OF adequate]
  have bl: "lang (c211_box P) Prop" by (rule paper_R_named_box_language[OF c211_rich pl])
  have al: "lang (named_paper_all \<sigma> (NLam n (c211_box P))) Prop"
    by (rule paper_R_named_all_binder_language[OF bl nt rt])
  have ql: "lang (named_paper_all \<sigma> (NLam n P)) Prop"
    by (rule paper_R_named_all_binder_language[OF pl nt rt])
  have cl: "lang (c211_box (named_paper_all \<sigma> (NLam n P))) Prop"
    by (rule paper_R_named_box_language[OF c211_rich ql])
  have conclusion: "sat ?h g (c211_box (named_paper_all \<sigma> (NLam n P)))"
    if prem: "sat ?h g (named_paper_all \<sigma> (NLam n (c211_box P)))"
  proof -
    have boxed: "sat ?h (g(n := Some b)) (c211_box P)" if bm: "b \<in> explode (D \<sigma> Root)" for b
      using iffD1[OF sat_all[OF arrow origin ht bl nt rt ad(2)] prem] bm by (simp only: goal)
    show ?thesis
    proof (rule iffD2[OF sat_box[OF arrow origin ht ql ad(4)]], intro allI impI)
      fix i assume ia: "i \<in> explode Ar" and meet: "source i = target ?h"
      have iroot: "source i = Root" by (simp only: meet goal)
      note c = composite[OF arrow origin ia meet]
      have st: "env (source i) g" using ht by (simp only: meet)
      have it: "env (target (compose i ?h)) (tr i g)"
        by (simp only: c(3); rule transported_env[OF ia st])
      have ia': "named_adequate (tr i g) (NLam n P)"
        by (simp only: paper_ZF_action_transport_adequate_iff; rule ad(1))
      show "sat (compose i ?h) (tr i g) (named_paper_all \<sigma> (NLam n P))"
      proof (rule iffD2[OF sat_all[OF c(1) c(2) it pl nt rt ia']], rule ballI)
        fix a assume am: "a \<in> explode (D \<sigma> (target (compose i ?h)))"
        have ay: "Elem a (D \<sigma> (target i))" using am by (simp only: c(3) explode_Elem)
        obtain b where bm: "Elem b (D \<sigma> Root)" and ba: "T \<sigma> i b = a"
          using onto ia iroot ay by blast
        have be: "b \<in> explode (D \<sigma> Root)" by (simp only: explode_Elem bm)
        have bt: "env (target ?h) (g(n := Some b))"
          by (simp only: goal; rule paper_ZF_action_env_update[OF typed nt rt be])
        have bpa: "named_adequate (g(n := Some b)) P"
          by (rule iffD2[OF named_binder_update_adequate_iff ad(1)])
        have "sat (compose i ?h) (tr i (g(n := Some b))) P"
          using iffD1[OF sat_box[OF arrow origin bt pl bpa] boxed[OF be]] ia meet by blast
        then show "sat (compose i ?h) ((tr i g)(n := Some a)) P"
          by (simp only: paper_ZF_action_transport_update nt ba)
      qed
    qed
  qed
  show ?thesis unfolding c211_BF_def
    by (rule iffD2[OF sat_imp[OF arrow origin ht al cl ad(3) ad(5)]]) (rule impI, erule conclusion)
qed

end

theorem c211_BF_valid:
  assumes model: "paper_ZF_action_model \<Sigma> c211_G Obj Ar source target compose identity Root D T I"
    and rt: "paper_R_type \<sigma>" and nt: "c211_G n = \<sigma>"
    and pl: "paper_R_in_language \<Sigma> c211_G P Prop"
    and onto: "\<forall>h y. h \<in> explode Ar \<longrightarrow> source h = Root \<longrightarrow> Elem y (D \<sigma> (target h)) \<longrightarrow>
      (\<exists>x. Elem x (D \<sigma> Root) \<and> T \<sigma> h x = y)"
  shows "c211_valid \<Sigma> c211_G Ar source target compose identity Root D T I (c211_BF \<sigma> n P)"
proof -
  interpret S: c211_bf_sem \<Sigma> Obj Ar source target compose identity Root D T I
    by (rule c211_bf_sem.intro[OF model])
  have goal: "target (identity Root) = Root" by (rule c211_root_identity(3)[OF model])
  show ?thesis
    unfolding c211_valid_def
  proof (intro conjI allI impI)
    show "paper_R_in_language \<Sigma> c211_G (c211_BF \<sigma> n P) Prop" by (rule c211_BF_language[OF rt nt pl])
    fix g
    assume typed: "paper_ZF_action_env_typed D c211_G (target (identity Root)) g"
      and adequate: "named_adequate g (c211_BF \<sigma> n P)"
    have rtyped: "paper_ZF_action_env_typed D c211_G Root g" using typed by (simp only: goal)
    show "paper_ZF_action_holds Ar source target compose identity D T I c211_G (identity Root) g
        (c211_BF \<sigma> n P)"
      by (rule S.bf_root[OF rt nt pl onto rtyped adequate])
  qed
qed

subsection \<open>The concrete model\<close>

lemma c211_concrete_onto:
  "\<forall>h y. h \<in> explode pa_Ar \<longrightarrow> Fst h = raw_root \<longrightarrow> Elem y (paper_D \<sigma> (Snd h)) \<longrightarrow>
    (\<exists>x. Elem x (paper_D \<sigma> raw_root) \<and> paper_T \<sigma> h x = y)"
proof (intro allI impI)
  fix h y assume arrow: "h \<in> explode pa_Ar" and origin: "Fst h = raw_root"
    and ym: "Elem y (paper_D \<sigma> (Snd h))"
  show "\<exists>x. Elem x (paper_D \<sigma> raw_root) \<and> paper_T \<sigma> h x = y"
    using c211_raw_T_onto_arrows[OF arrow ym] by (simp only: origin)
qed

corollary c211_BF_concrete:
  assumes rt: "paper_R_type \<sigma>" and nt: "c211_G n = \<sigma>"
    and pl: "paper_R_in_language S c211_G P Prop"
  shows "c211_valid S c211_G pa_Ar Fst Snd pa_compose pa_id raw_root paper_D paper_T paper_I
    (c211_BF \<sigma> n P)"
  by (rule c211_BF_valid[OF concrete_paper_standard_model rt nt pl c211_concrete_onto])

ML \<open>
  val facts = [@{thm c211_bf_sem.sat_box}, @{thm c211_bf_sem.sat_all}, @{thm c211_bf_sem.sat_imp},
    @{thm c211_bf_sem.bf_adequacy(1)}, @{thm c211_bf_sem.bf_root}, @{thm c211_BF_valid},
    @{thm c211_concrete_onto}, @{thm c211_BF_concrete}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-BF: Proposition 3.24(ii), BF from root-arrow surjectivity; concrete model instance";
\<close>

end
