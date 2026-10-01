theory Classicism_2_11_Order_Semantics
  imports "Classicism_2_11_Formulas.Classicism_2_11_Order_Defs"
    "Classicism_2_11_Formulas.Classicism_2_11_Extension"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Box_Truth"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Binder_Truth"
    "Bacon_Classicism_Action_Development.Bacon_Source_Relational_Logical_Truth"
    "Bacon_Classicism_ZF_Representation.Bacon_Source_ZF_Model_Truth_Separation"
begin

section \<open>Generic semantics of the Proposition 2.11 formulas\<close>

text \<open>
  Every result below holds in EVERY action model of Definition 3.20
  (p.56) over the standard stock. Truth is the paper's A,h,g ⊩ P at
  an arbitrary root arrow h:W₀→W. The lifted operators of Figure 1
  (p.6) are evaluated semantically: application of the value of a
  closed λ-constant, never syntactic β-reduction with substitution.
  Evaluation of NApp(NLam n B) Y updates the assignment at n
  (abstraction clause of Definition 3.19 at the identity pair).

  Consequences: ≤τ is the pointwise order c211_pleq; x ≤ ¬x is
  c211_pempty; Atom and Atomicity are c211_patom and c211_patomic;
  □P quantifies over every outgoing arrow; c211_pcomplete suffices
  for Boolean Completeness (pp.23–24).
\<close>

subsection \<open>Order facts that need no model\<close>

lemma c211_pleq_refl: "c211_pleq Ar source target D \<tau> W a a"
  by (induction \<tau> arbitrary: W a) simp_all

lemma c211_pleq_trans:
  "c211_pleq Ar source target D \<tau> W a b \<Longrightarrow> c211_pleq Ar source target D \<tau> W b c \<Longrightarrow>
    c211_pleq Ar source target D \<tau> W a c"
proof (induction \<tau> arbitrary: W a b c)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by simp
next
  case (Arr \<sigma> \<rho>)
  show ?case unfolding c211_pleq.simps
  proof (intro allI impI)
    fix i x
    assume ia: "i \<in> explode Ar" and si: "source i = W" and xm: "Elem x (D \<sigma> (target i))"
    have ab: "c211_pleq Ar source target D \<rho> (target i) (app a (Opair i x)) (app b (Opair i x))"
      using Arr.prems(1) ia si xm by (simp only: c211_pleq.simps)
    have bc: "c211_pleq Ar source target D \<rho> (target i) (app b (Opair i x)) (app c (Opair i x))"
      using Arr.prems(2) ia si xm by (simp only: c211_pleq.simps)
    show "c211_pleq Ar source target D \<rho> (target i) (app a (Opair i x)) (app c (Opair i x))"
      by (rule Arr.IH(2)[OF ab bc])
  qed
qed

lemma c211_pempty_pleq:
  "c211_pempty Ar source target D \<tau> W a \<Longrightarrow> c211_pleq Ar source target D \<tau> W a b"
proof (induction \<tau> arbitrary: W a b)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by simp
next
  case (Arr \<sigma> \<rho>)
  show ?case using Arr.prems Arr.IH(2) by (simp only: c211_pempty.simps c211_pleq.simps) blast
qed

lemma c211_relational_facts:
  assumes "paper_R_relational \<tau>"
  shows "paper_R_type \<tau>" "paper_R_type (Arr \<tau> \<tau>)" "paper_R_type (Arr \<tau> (Arr \<tau> \<tau>))"
    "paper_R_type (Arr \<tau> Prop)"
  using assms by (simp_all add: paper_R_relational_def)

subsection \<open>The model context\<close>

locale c211_sem =
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

abbreviation ple :: "otype \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "ple \<equiv> c211_pleq Ar source target D"

abbreviation pem :: "otype \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> bool" where
  "pem \<equiv> c211_pempty Ar source target D"

lemma premodel: "paper_ZF_action_premodel \<Sigma> Obj Ar source target compose identity Root D T I"
  using model unfolding paper_ZF_action_model_def by blast

sublocale C: paper_rooted_category Obj "explode Ar" source target compose identity Root
  using premodel unfolding paper_ZF_action_premodel_def by blast

lemma action:
  "paper_R_type \<rho> \<Longrightarrow>
    paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D \<rho> W)) (T \<rho>)"
  using premodel unfolding paper_ZF_action_premodel_def by blast

lemma fun_subaction:
  "paper_R_type (Arr \<sigma> \<tau>) \<Longrightarrow>
    paper_subaction Obj (explode Ar) source target compose identity
      (\<lambda>W. explode (D (Arr \<sigma> \<tau>) W)) (T (Arr \<sigma> \<tau>))
      (\<lambda>W. explode (paper_ZF_exponential_code Ar source target compose (D \<sigma>) (T \<sigma>) (D \<tau>) (T \<tau>) W))
      (paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>))"
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

lemma tr_empty: "tr i Map.empty = Map.empty"
  by (rule ext) (simp add: paper_ZF_action_transport_assignment_def paper_hom_assignment_def)

lemma transported_env:
  assumes ia: "i \<in> explode Ar" and typed: "env (source i) g"
  shows "env (target i) (tr i g)"
  by (rule paper_ZF_premodel_transport_env_typed[OF premodel ia typed])

subsection \<open>Graph facts for function values\<close>

lemma app_type:
  "W \<in> Obj \<Longrightarrow> paper_R_type (Arr \<sigma> \<tau>) \<Longrightarrow> f \<in> explode (D (Arr \<sigma> \<tau>) W) \<Longrightarrow>
    a \<in> explode (D \<sigma> W) \<Longrightarrow> app f (Opair (identity W) a) \<in> explode (D \<tau> W)"
  by (rule paper_ZF_premodel_application_type[OF premodel])

lemma fun_graph:
  assumes object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<rho>)"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) W)"
  shows "a \<in> explode (paper_ZF_Pi (paper_ZF_pair_code Ar source target (D \<sigma>) W)
    (\<lambda>z. D \<rho> (target (Fst z))))"
  by (rule paper_ZF_exponential_code_graph[OF
    paper_ZF_premodel_function_in_exponential[OF premodel object rt am]])

lemma fun_value:
  assumes object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<rho>)"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) W)"
    and ia: "i \<in> explode Ar" and si: "source i = W" and xm: "x \<in> explode (D \<sigma> (target i))"
  shows "app a (Opair i x) \<in> explode (D \<rho> (target i))"
proof -
  have pair: "Elem (Opair i x) (paper_ZF_pair_code Ar source target (D \<sigma>) W)"
    unfolding paper_ZF_pair_code_member using ia si xm by blast
  have "Elem (app a (Opair i x)) (D \<rho> (target (Fst (Opair i x))))"
    by (rule paper_ZF_Pi_value[OF fun_graph[OF object rt am] pair])
  then show ?thesis by (simp only: Fst explode_Elem)
qed

lemma fun_lambda:
  assumes object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<rho>)"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) W)"
  shows "a = Lambda (paper_ZF_pair_code Ar source target (D \<sigma>) W) (app a)"
proof -
  let ?P = "paper_ZF_pair_code Ar source target (D \<sigma>) W"
  have "a \<in> explode (Fun ?P (Sum (Repl ?P (\<lambda>z. D \<rho> (target (Fst z))))))"
    by (rule paper_ZF_Pi_graph[OF fun_graph[OF object rt am]])
  then have "Elem a (Fun ?P (Sum (Repl ?P (\<lambda>z. D \<rho> (target (Fst z))))))"
    by (simp only: explode_Elem)
  then obtain f where shape: "a = Lambda ?P f" using Elem_Fun_Lambda by blast
  have "Lambda ?P f = Lambda ?P (app (Lambda ?P f))"
    by (simp add: Lambda_ext Lambda_app)
  then show ?thesis by (simp only: shape[symmetric])
qed

lemma fun_ext:
  assumes object: "W \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<rho>)"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) W)" and bm: "b \<in> explode (D (Arr \<sigma> \<rho>) W)"
    and same: "\<And>i x. i \<in> explode Ar \<Longrightarrow> source i = W \<Longrightarrow> x \<in> explode (D \<sigma> (target i)) \<Longrightarrow>
      app a (Opair i x) = app b (Opair i x)"
  shows "a = b"
proof -
  let ?P = "paper_ZF_pair_code Ar source target (D \<sigma>) W"
  have pointwise: "\<forall>z. Elem z ?P \<longrightarrow> app a z = app b z"
  proof (intro allI impI)
    fix z
    assume zm: "Elem z ?P"
    obtain i x where ia: "i \<in> explode Ar" and si: "source i = W"
      and xm: "x \<in> explode (D \<sigma> (target i))" and shape: "z = Opair i x"
      by (rule paper_ZF_pair_codeE[OF zm])
    show "app a z = app b z" by (simp only: shape same[OF ia si xm])
  qed
  have "Lambda ?P (app a) = Lambda ?P (app b)"
    by (simp only: Lambda_ext; rule conjI[OF refl pointwise])
  then show ?thesis by (simp only: fun_lambda[OF object rt am, symmetric] fun_lambda[OF object rt bm, symmetric])
qed

lemma exp_transport_app:
  assumes rt: "paper_R_type (Arr \<sigma> \<rho>)" and ia: "i \<in> explode Ar"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) (source i))" and xm: "x \<in> explode (D \<sigma> (target i))"
  shows "app (T (Arr \<sigma> \<rho>) i a) (Opair (identity (target i)) x) = app a (Opair i x)"
proof -
  have object: "target i \<in> Obj" by (rule C.target_object[OF ia])
  have transport: "T (Arr \<sigma> \<rho>) i a = paper_ZF_exponential_transport_code Ar source target compose (D \<sigma>) i a"
    by (rule paper_subaction_transport[OF fun_subaction[OF rt] ia am])
  have pair: "Elem (Opair (identity (target i)) x) (paper_ZF_pair_code Ar source target (D \<sigma>) (target i))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object xm])
  show ?thesis
    by (simp only: transport paper_ZF_exponential_transport_apply[OF pair] C.identity_left[OF ia])
qed

subsection \<open>Evaluation at the identity pair\<close>

lemma ev_value:
  assumes "lang A \<rho>" "h \<in> explode Ar" "source h = Root" "env (target h) g" "named_adequate g A"
  obtains v where "ev A h g = Some v" "v \<in> explode (D \<rho> (target h))"
  by (rule paper_ZF_action_model_eval_value[OF model assms])

lemma ev_member:
  "lang A \<rho> \<Longrightarrow> h \<in> explode Ar \<Longrightarrow> source h = Root \<Longrightarrow> env (target h) g \<Longrightarrow>
    named_adequate g A \<Longrightarrow> ev A h g = Some v \<Longrightarrow> v \<in> explode (D \<rho> (target h))"
  by (rule paper_ZF_action_model_eval_member[OF model])

lemma ev_app:
  assumes object: "target h \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and fe: "ev F h g = Some f" and fm: "f \<in> explode (D (Arr \<sigma> \<tau>) (target h))"
    and ae: "ev A h g = Some a" and am: "a \<in> explode (D \<sigma> (target h))"
  shows "ev (NApp F A) h g = Some (app f (Opair (identity (target h)) a))"
  by (rule paper_ZF_action_eval_application[OF fe ae
    paper_ZF_premodel_application_graph(1)[OF premodel object rt fm am]
    paper_ZF_premodel_application_graph(2)[OF premodel object rt fm am]])

lemma ev_lam:
  assumes arrow: "h \<in> explode Ar" and typed: "env (target h) g"
    and lam: "ev (NLam n B) h g = Some F" and ym: "y \<in> explode (D (c211_G n) (target h))"
  shows "Some (app F (Opair (identity (target h)) y)) = ev B h (g(n := Some y))"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have pair: "Elem (Opair (identity (target h)) y)
      (paper_ZF_pair_code Ar source target (D (c211_G n)) (target h))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object ym])
  have "Some (app F (Opair (identity (target h)) y)) =
      ev B (compose (identity (target h)) h) ((tr (identity (target h)) g)(n := Some y))"
    by (rule paper_ZF_action_eval_abstraction_apply[OF lam pair])
  then show ?thesis
    by (simp only: C.identity_left[OF arrow]
      paper_ZF_action_assignment_transport_identity[OF action object typed])
qed

lemma ev_beta:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and ll: "lang (NLam n B) (Arr \<sigma> \<tau>)" and nt: "c211_G n = \<sigma>" and yl: "lang Y \<sigma>"
    and la: "named_adequate g (NLam n B)" and ya: "named_adequate g Y"
    and ye: "ev Y h g = Some y"
  shows "ev (NApp (NLam n B) Y) h g = ev B h (g(n := Some y))"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  obtain F where fe: "ev (NLam n B) h g = Some F" and fm: "F \<in> explode (D (Arr \<sigma> \<tau>) (target h))"
    by (rule ev_value[OF ll arrow origin typed la])
  have ym: "y \<in> explode (D \<sigma> (target h))" by (rule ev_member[OF yl arrow origin typed ya ye])
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF ll])
  have yn: "y \<in> explode (D (c211_G n) (target h))" using ym by (simp only: nt)
  show ?thesis by (simp only: ev_app[OF object rt fe fm ye ym] ev_lam[OF arrow typed fe yn])
qed

lemma ev_beta2:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and ll: "lang (NLam n (NLam m B)) (Arr \<sigma>1 (Arr \<sigma>2 \<tau>))"
    and nt: "c211_G n = \<sigma>1" and mt: "c211_G m = \<sigma>2"
    and al: "lang A1 \<sigma>1" and bl: "lang A2 \<sigma>2"
    and la: "named_adequate g (NLam n (NLam m B))"
    and aa: "named_adequate g A1" and ba: "named_adequate g A2"
    and ae: "ev A1 h g = Some a1" and be: "ev A2 h g = Some a2"
  shows "ev (NApp (NApp (NLam n (NLam m B)) A1) A2) h g = ev B h (g(n := Some a1, m := Some a2))"
proof -
  let ?L = "NLam n (NLam m B)"
  let ?W = "target h"
  have object: "?W \<in> Obj" by (rule C.target_object[OF arrow])
  obtain F where fe: "ev ?L h g = Some F" and fm: "F \<in> explode (D (Arr \<sigma>1 (Arr \<sigma>2 \<tau>)) ?W)"
    by (rule ev_value[OF ll arrow origin typed la])
  have am: "a1 \<in> explode (D \<sigma>1 ?W)" by (rule ev_member[OF al arrow origin typed aa ae])
  have bm: "a2 \<in> explode (D \<sigma>2 ?W)" by (rule ev_member[OF bl arrow origin typed ba be])
  have rt: "paper_R_type (Arr \<sigma>1 (Arr \<sigma>2 \<tau>))" by (rule paper_R_language_result_type[OF ll])
  have rt2: "paper_R_type (Arr \<sigma>2 \<tau>)" and r1: "paper_R_type \<sigma>1" using rt by simp_all
  have e1: "ev (NApp ?L A1) h g = Some (app F (Opair (identity ?W) a1))"
    by (rule ev_app[OF object rt fe fm ae am])
  have m1: "app F (Opair (identity ?W) a1) \<in> explode (D (Arr \<sigma>2 \<tau>) ?W)"
    by (rule app_type[OF object rt fm am])
  have an: "a1 \<in> explode (D (c211_G n) ?W)" using am by (simp only: nt)
  have l1: "Some (app F (Opair (identity ?W) a1)) = ev (NLam m B) h (g(n := Some a1))"
    by (rule ev_lam[OF arrow typed fe an])
  have t1: "env ?W (g(n := Some a1))" by (rule paper_ZF_action_env_update[OF typed nt r1 am])
  have bn: "a2 \<in> explode (D (c211_G m) ?W)" using bm by (simp only: mt)
  have l2: "Some (app (app F (Opair (identity ?W) a1)) (Opair (identity ?W) a2)) =
      ev B h (g(n := Some a1, m := Some a2))"
    by (rule ev_lam[OF arrow t1 l1[symmetric] bn])
  show ?thesis by (simp only: ev_app[OF object rt2 e1 m1 be bm] l2)
qed

lemma sat_ev_cong: "ev A h g = ev B h k \<Longrightarrow> sat h g A \<longleftrightarrow> sat h k B"
  by (simp only: paper_ZF_action_holds_def)

lemma sat_value: "ev A h g = Some p \<Longrightarrow> sat h g A \<longleftrightarrow> Elem (identity (target h)) p"
  by (simp add: paper_ZF_action_holds_def)

subsection \<open>Truth of the connectives, through the BBK model at h\<close>

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

lemma sat_and:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and bl: "lang B Prop"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "sat h g (named_paper_and A B) \<longleftrightarrow> sat h g A \<and> sat h g B"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have cl: "lang (named_paper_and A B) Prop" by (rule paper_R_named_and_language[OF al bl])
  have ca: "named_adequate g (named_paper_and A B)"
    using aa ba by (simp only: named_adequate_def named_paper_primitive_fv Un_subset_iff; rule conjI)
  show ?thesis
    by (simp only: sat_bbk[OF arrow origin typed cl ca] sat_bbk[OF arrow origin typed al aa]
      sat_bbk[OF arrow origin typed bl ba] M.paper_R_named_and_truth[OF al bl btyped[OF typed] aa ba])
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

lemma sat_iff:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A Prop" and bl: "lang B Prop"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
  shows "sat h g (c211_iff A B) \<longleftrightarrow> (sat h g A \<longleftrightarrow> sat h g B)"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have cl: "lang (c211_iff A B) Prop" by (rule c211_connective_language(4)[OF al bl])
  have ca: "named_adequate g (c211_iff A B)"
    using aa ba by (simp only: named_adequate_def named_paper_defined_fv Un_subset_iff; rule conjI)
  show ?thesis
    by (simp only: sat_bbk[OF arrow origin typed cl ca] sat_bbk[OF arrow origin typed al aa]
      sat_bbk[OF arrow origin typed bl ba] M.paper_R_named_paper_iff_truth[OF al bl btyped[OF typed] aa ba])
qed

lemma sat_eq:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and al: "lang A \<sigma>" and bl: "lang B \<sigma>"
    and aa: "named_adequate g A" and ba: "named_adequate g B"
    and ae: "ev A h g = Some a" and be: "ev B h g = Some b"
  shows "sat h g (named_paper_eq \<sigma> A B) \<longleftrightarrow> a = b"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have el: "lang (named_paper_eq \<sigma> A B) Prop" by (rule paper_R_named_eq_language[OF al bl])
  have ea: "named_adequate g (named_paper_eq \<sigma> A B)"
    using aa ba by (simp only: named_adequate_def named_paper_primitive_fv Un_subset_iff; rule conjI)
  have "sat h g (named_paper_eq \<sigma> A B) \<longleftrightarrow> val h (den h g (named_paper_eq \<sigma> A B))"
    by (rule sat_bbk[OF arrow origin typed el ea])
  also have "\<dots> \<longleftrightarrow> den h g A = den h g B"
    unfolding named_paper_eq_def by (rule M.valuation_identity[OF al bl btyped[OF typed] aa ba])
  finally show ?thesis by (simp only: den_value[OF ae] den_value[OF be])
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

lemma sat_ex:
  assumes arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and body: "lang A Prop" and nt: "c211_G n = \<sigma>" and rt: "paper_R_type \<sigma>"
    and adequate: "named_adequate g (NLam n A)"
  shows "sat h g (named_paper_ex \<sigma> (NLam n A)) \<longleftrightarrow>
    (\<exists>a\<in>explode (D \<sigma> (target h)). sat h (g(n := Some a)) A)"
proof -
  interpret M: paper_R_bbk_model \<Sigma> c211_G "bdom h" "den h" "val h" by (rule bbk[OF arrow origin])
  have nr: "paper_R_type (c211_G n)" by (simp only: nt; rule rt)
  have ql: "lang (named_paper_ex \<sigma> (NLam n A)) Prop"
    using paper_R_named_ex_language[OF paper_R_binder_formula_language[OF body nr]] by (simp only: nt)
  have qa: "named_adequate g (named_paper_ex \<sigma> (NLam n A))"
    using adequate by (simp add: named_adequate_def named_paper_ex_def)
  have inst: "val h (den h (g(n := Some a)) A) \<longleftrightarrow> sat h (g(n := Some a)) A"
    if am: "a \<in> explode (D \<sigma> (target h))" for a
  proof -
    have ut: "env (target h) (g(n := Some a))" by (rule paper_ZF_action_env_update[OF typed nt rt am])
    have ua: "named_adequate (g(n := Some a)) A"
      by (rule iffD2[OF named_binder_update_adequate_iff adequate])
    show ?thesis by (rule sym, rule sat_bbk[OF arrow origin ut body ua])
  qed
  have "sat h g (named_paper_ex \<sigma> (NLam n A)) \<longleftrightarrow> val h (den h g (named_paper_ex \<sigma> (NLam n A)))"
    by (rule sat_bbk[OF arrow origin typed ql qa])
  also have "\<dots> \<longleftrightarrow> (\<exists>a\<in>bdom h \<sigma>. val h (den h (g(n := Some a)) A))"
    by (rule M.paper_R_exists_binder_truth[OF body nt rt btyped[OF typed] adequate])
  also have "\<dots> \<longleftrightarrow> (\<exists>a\<in>explode (D \<sigma> (target h)). sat h (g(n := Some a)) A)"
    by (rule bex_cong[OF paper_ZF_action_bbk_domain_R[OF rt] inst])
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

subsection \<open>S1: necessity quantifies over outgoing arrows\<close>

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

subsection \<open>S2: values of the closed lifted operators\<close>

text \<open>
  A closed in-language constant has an assignment-independent value
  at each root arrow (locality). The lifted ∨τ and ¬τ are applied
  semantically at the identity pair. Their values at a function type
  are computed pointwise along every outgoing pair ⟨i,x⟩, at the
  composite root arrow i∘h.
\<close>

definition cval :: "'c paper_named_term \<Rightarrow> ZF \<Rightarrow> ZF" where
  "cval K h = the (ev K h Map.empty)"

definition orv :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "orv \<tau> h a b = app (app (cval (c211_or \<tau>) h) (Opair (identity (target h)) a))
    (Opair (identity (target h)) b)"

definition notv :: "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "notv \<tau> h a = app (cval (c211_not \<tau>) h) (Opair (identity (target h)) a)"

lemma cval_ev:
  assumes kl: "lang K \<rho>" and closed: "named_fv K = {}"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root"
  shows "ev K h g = Some (cval K h)" and "cval K h \<in> explode (D \<rho> (target h))"
proof -
  have local: "ev K h g = ev K h Map.empty"
    by (rule paper_ZF_action_eval_locality) (simp add: closed)
  have ea: "named_adequate Map.empty K" by (simp add: named_adequate_def closed)
  obtain v where ve: "ev K h Map.empty = Some v" and vm: "v \<in> explode (D \<rho> (target h))"
    by (rule ev_value[OF kl arrow origin paper_ZF_action_env_empty ea])
  have cv: "cval K h = v" by (simp only: cval_def ve option.sel)
  show "ev K h g = Some (cval K h)" by (simp only: local ve cv)
  show "cval K h \<in> explode (D \<rho> (target h))" by (simp only: cv vm)
qed

lemma orv_value:
  assumes rel: "paper_R_relational \<tau>" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and am: "a \<in> explode (D \<tau> (target h))" and bm: "b \<in> explode (D \<tau> (target h))"
  shows "orv \<tau> h a b \<in> explode (D \<tau> (target h))"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have om: "cval (c211_or \<tau>) h \<in> explode (D (Arr \<tau> (Arr \<tau> \<tau>)) (target h))"
    by (rule cval_ev(2)[OF c211_or_language[OF rel] c211_or_closed arrow origin])
  have o1: "app (cval (c211_or \<tau>) h) (Opair (identity (target h)) a) \<in> explode (D (Arr \<tau> \<tau>) (target h))"
    by (rule app_type[OF object c211_relational_facts(3)[OF rel] om am])
  show ?thesis unfolding orv_def by (rule app_type[OF object c211_relational_facts(2)[OF rel] o1 bm])
qed

lemma orv_ev:
  assumes rel: "paper_R_relational \<tau>" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and ae: "ev A h g = Some a" and am: "a \<in> explode (D \<tau> (target h))"
    and be: "ev B h g = Some b" and bm: "b \<in> explode (D \<tau> (target h))"
  shows "ev (NApp (NApp (c211_or \<tau>) A) B) h g = Some (orv \<tau> h a b)"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  note oc = cval_ev[OF c211_or_language[OF rel] c211_or_closed arrow origin]
  have e1: "ev (NApp (c211_or \<tau>) A) h g =
      Some (app (cval (c211_or \<tau>) h) (Opair (identity (target h)) a))"
    by (rule ev_app[OF object c211_relational_facts(3)[OF rel] oc(1) oc(2) ae am])
  have m1: "app (cval (c211_or \<tau>) h) (Opair (identity (target h)) a) \<in> explode (D (Arr \<tau> \<tau>) (target h))"
    by (rule app_type[OF object c211_relational_facts(3)[OF rel] oc(2) am])
  show ?thesis unfolding orv_def by (rule ev_app[OF object c211_relational_facts(2)[OF rel] e1 m1 be bm])
qed

lemma notv_value:
  assumes rel: "paper_R_relational \<tau>" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and am: "a \<in> explode (D \<tau> (target h))"
  shows "notv \<tau> h a \<in> explode (D \<tau> (target h))"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have nm: "cval (c211_not \<tau>) h \<in> explode (D (Arr \<tau> \<tau>) (target h))"
    by (rule cval_ev(2)[OF c211_not_language[OF rel] c211_not_closed arrow origin])
  show ?thesis unfolding notv_def by (rule app_type[OF object c211_relational_facts(2)[OF rel] nm am])
qed

lemma notv_ev:
  assumes rel: "paper_R_relational \<tau>" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and ae: "ev A h g = Some a" and am: "a \<in> explode (D \<tau> (target h))"
  shows "ev (NApp (c211_not \<tau>) A) h g = Some (notv \<tau> h a)"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  note nc = cval_ev[OF c211_not_language[OF rel] c211_not_closed arrow origin]
  show ?thesis unfolding notv_def by (rule ev_app[OF object c211_relational_facts(2)[OF rel] nc(1) nc(2) ae am])
qed

lemma action_Prop: "paper_action Obj (explode Ar) source target compose identity (\<lambda>W. explode (D Prop W)) (T Prop)"
  by (rule action) simp

lemma orv_Prop:
  assumes arrow: "h \<in> explode Ar"
    and am: "a \<in> explode (D Prop (target h))" and bm: "b \<in> explode (D Prop (target h))"
  shows "orv Prop h a b = union a b"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have cv: "cval (c211_or Prop) h =
      paper_ZF_logical_value Ar source target compose identity D T (target h) SOr"
    by (simp only: cval_def c211_or.simps paper_ZF_action_eval.simps option.sel)
  have first: "Elem (Opair (identity (target h)) a) (paper_ZF_pair_code Ar source target (D Prop) (target h))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object am])
  have second: "Elem (Opair (identity (target h)) b)
      (paper_ZF_pair_code Ar source target (D Prop) (target (identity (target h))))"
    by (simp only: C.identity_target[OF object]; rule paper_ZF_premodel_identity_pair[OF premodel object bm])
  have unchanged: "T Prop (identity (target h)) a = a"
    by (rule paper_action.transport_identity[OF action_Prop object am])
  show ?thesis
    by (simp only: orv_def cv paper_ZF_logical_or_apply[where D=D and W="target h", OF first second] unchanged)
qed

lemma notv_Prop_member:
  assumes arrow: "h \<in> explode Ar" and am: "a \<in> explode (D Prop (target h))"
  shows "Elem j (notv Prop h a) \<longleftrightarrow> j \<in> explode Ar \<and> source j = target h \<and> \<not> Elem j a"
proof -
  have object: "target h \<in> Obj" by (rule C.target_object[OF arrow])
  have cv: "cval (c211_not Prop) h =
      paper_ZF_logical_value Ar source target compose identity D T (target h) SNot"
    by (simp only: cval_def c211_not.simps paper_ZF_action_eval.simps option.sel)
  have first: "Elem (Opair (identity (target h)) a) (paper_ZF_pair_code Ar source target (D Prop) (target h))"
    by (rule paper_ZF_premodel_identity_pair[OF premodel object am])
  show ?thesis
    by (simp only: notv_def cv paper_ZF_logical_not_member[where D=D and W="target h", OF first]
      C.identity_target[OF object])
qed

lemma orv_Arr:
  assumes rel: "paper_R_relational (Arr \<sigma> \<rho>)" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) (target h))" and bm: "b \<in> explode (D (Arr \<sigma> \<rho>) (target h))"
    and ia: "i \<in> explode Ar" and meet: "source i = target h" and xm: "x \<in> explode (D \<sigma> (target i))"
  shows "app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x) =
    orv \<rho> (compose i h) (app a (Opair i x)) (app b (Opair i x))"
proof -
  note facts = c211_relational_Arr[OF rel]
  have rt: "paper_R_type (Arr \<sigma> \<rho>)" by (rule c211_relational_type[OF rel])
  let ?f = "c211_v (Arr \<sigma> \<rho>) 0" and ?k = "c211_v (Arr \<sigma> \<rho>) 1" and ?z = "c211_v \<sigma> 2"
  let ?B = "NApp (NApp (c211_or \<rho>) (NApp (NVar ?f) (NVar ?z))) (NApp (NVar ?k) (NVar ?z))
    :: 'c paper_named_term"
  let ?W = "target h" and ?O = "cval (c211_or (Arr \<sigma> \<rho>)) h" and ?c = "compose i h"
  have object: "?W \<in> Obj" by (rule C.target_object[OF arrow])
  note c = composite[OF arrow origin ia meet]
  have cobj: "target ?c \<in> Obj" by (rule C.target_object[OF c(1)])
  have oe: "ev (NLam ?f (NLam ?k (NLam ?z ?B))) h Map.empty = Some ?O"
    using cval_ev(1)[OF c211_or_language[OF rel] c211_or_closed arrow origin, where g=Map.empty]
    by (simp only: c211_or.simps)
  have af: "a \<in> explode (D (c211_G ?f) ?W)" using am by (simp only: c211_v_type)
  have bk: "b \<in> explode (D (c211_G ?k) ?W)" using bm by (simp only: c211_v_type)
  have g1: "env ?W (Map.empty(?f := Some a))"
    by (rule paper_ZF_action_env_update[where D=D and G=c211_G and n="c211_v (Arr \<sigma> \<rho>) 0", OF paper_ZF_action_env_empty c211_v_type rt am])
  have s1: "Some (app ?O (Opair (identity ?W) a)) = ev (NLam ?k (NLam ?z ?B)) h (Map.empty(?f := Some a))"
    by (rule ev_lam[OF arrow paper_ZF_action_env_empty oe af])
  have s2: "Some (app (app ?O (Opair (identity ?W) a)) (Opair (identity ?W) b)) =
      ev (NLam ?z ?B) h (Map.empty(?f := Some a, ?k := Some b))"
    by (rule ev_lam[OF arrow g1 s1[symmetric] bk])
  have pair: "Elem (Opair i x) (paper_ZF_pair_code Ar source target (D (c211_G ?z)) ?W)"
    unfolding c211_v_type paper_ZF_pair_code_member using ia meet xm by blast
  have s3: "Some (app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x)) =
      ev ?B ?c ((tr i (Map.empty(?f := Some a, ?k := Some b)))(?z := Some x))"
    unfolding orv_def by (rule paper_ZF_action_eval_abstraction_apply[OF s2[symmetric] pair])
  have trq: "tr i (Map.empty(?f := Some a, ?k := Some b)) =
      Map.empty(?f := Some (T (Arr \<sigma> \<rho>) i a), ?k := Some (T (Arr \<sigma> \<rho>) i b))"
    by (simp only: paper_ZF_action_transport_update tr_empty c211_v_type)
  let ?u = "Map.empty(?f := Some (T (Arr \<sigma> \<rho>) i a), ?k := Some (T (Arr \<sigma> \<rho>) i b), ?z := Some x)"
  have ef: "ev (NVar ?f) ?c ?u = Some (T (Arr \<sigma> \<rho>) i a)" by simp
  have ek: "ev (NVar ?k) ?c ?u = Some (T (Arr \<sigma> \<rho>) i b)" by simp
  have ez: "ev (NVar ?z) ?c ?u = Some x" by simp
  have a_src: "a \<in> explode (D (Arr \<sigma> \<rho>) (source i))" using am by (simp only: meet)
  have b_src: "b \<in> explode (D (Arr \<sigma> \<rho>) (source i))" using bm by (simp only: meet)
  have ta: "T (Arr \<sigma> \<rho>) i a \<in> explode (D (Arr \<sigma> \<rho>) (target ?c))"
    by (simp only: c(3); rule paper_action.transport_type[OF action[OF rt] ia a_src])
  have tb: "T (Arr \<sigma> \<rho>) i b \<in> explode (D (Arr \<sigma> \<rho>) (target ?c))"
    by (simp only: c(3); rule paper_action.transport_type[OF action[OF rt] ia b_src])
  have xc: "x \<in> explode (D \<sigma> (target ?c))" by (simp only: c(3); rule xm)
  have ea: "ev (NApp (NVar ?f) (NVar ?z)) ?c ?u = Some (app a (Opair i x))"
    by (simp only: ev_app[OF cobj rt ef ta ez xc] c(3) exp_transport_app[OF rt ia a_src xm])
  have eb: "ev (NApp (NVar ?k) (NVar ?z)) ?c ?u = Some (app b (Opair i x))"
    by (simp only: ev_app[OF cobj rt ek tb ez xc] c(3) exp_transport_app[OF rt ia b_src xm])
  have a'm: "app a (Opair i x) \<in> explode (D \<rho> (target ?c))"
    by (simp only: c(3); rule fun_value[OF object rt am ia meet xm])
  have b'm: "app b (Opair i x) \<in> explode (D \<rho> (target ?c))"
    by (simp only: c(3); rule fun_value[OF object rt bm ia meet xm])
  have body: "ev ?B ?c ?u = Some (orv \<rho> ?c (app a (Opair i x)) (app b (Opair i x)))"
    by (rule orv_ev[OF facts(2) c(1) c(2) ea a'm eb b'm])
  have "Some (app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x)) =
      Some (orv \<rho> ?c (app a (Opair i x)) (app b (Opair i x)))"
    by (simp only: s3 trq body)
  then show ?thesis by (simp only: option.inject)
qed

lemma notv_Arr:
  assumes rel: "paper_R_relational (Arr \<sigma> \<rho>)" and arrow: "h \<in> explode Ar" and origin: "source h = Root"
    and am: "a \<in> explode (D (Arr \<sigma> \<rho>) (target h))"
    and ia: "i \<in> explode Ar" and meet: "source i = target h" and xm: "x \<in> explode (D \<sigma> (target i))"
  shows "app (notv (Arr \<sigma> \<rho>) h a) (Opair i x) = notv \<rho> (compose i h) (app a (Opair i x))"
proof -
  note facts = c211_relational_Arr[OF rel]
  have rt: "paper_R_type (Arr \<sigma> \<rho>)" by (rule c211_relational_type[OF rel])
  let ?f = "c211_v (Arr \<sigma> \<rho>) 0" and ?z = "c211_v \<sigma> 2"
  let ?B = "NApp (c211_not \<rho>) (NApp (NVar ?f) (NVar ?z)) :: 'c paper_named_term"
  let ?W = "target h" and ?N = "cval (c211_not (Arr \<sigma> \<rho>)) h" and ?c = "compose i h"
  have object: "?W \<in> Obj" by (rule C.target_object[OF arrow])
  note c = composite[OF arrow origin ia meet]
  have cobj: "target ?c \<in> Obj" by (rule C.target_object[OF c(1)])
  have ne: "ev (NLam ?f (NLam ?z ?B)) h Map.empty = Some ?N"
    using cval_ev(1)[OF c211_not_language[OF rel] c211_not_closed arrow origin, where g=Map.empty]
    by (simp only: c211_not.simps)
  have af: "a \<in> explode (D (c211_G ?f) ?W)" using am by (simp only: c211_v_type)
  have s1: "Some (app ?N (Opair (identity ?W) a)) = ev (NLam ?z ?B) h (Map.empty(?f := Some a))"
    by (rule ev_lam[OF arrow paper_ZF_action_env_empty ne af])
  have pair: "Elem (Opair i x) (paper_ZF_pair_code Ar source target (D (c211_G ?z)) ?W)"
    unfolding c211_v_type paper_ZF_pair_code_member using ia meet xm by blast
  have s2: "Some (app (notv (Arr \<sigma> \<rho>) h a) (Opair i x)) =
      ev ?B ?c ((tr i (Map.empty(?f := Some a)))(?z := Some x))"
    unfolding notv_def by (rule paper_ZF_action_eval_abstraction_apply[OF s1[symmetric] pair])
  have trq: "tr i (Map.empty(?f := Some a)) = Map.empty(?f := Some (T (Arr \<sigma> \<rho>) i a))"
    by (simp only: paper_ZF_action_transport_update tr_empty c211_v_type)
  let ?u = "Map.empty(?f := Some (T (Arr \<sigma> \<rho>) i a), ?z := Some x)"
  have ef: "ev (NVar ?f) ?c ?u = Some (T (Arr \<sigma> \<rho>) i a)" by simp
  have ez: "ev (NVar ?z) ?c ?u = Some x" by simp
  have a_src: "a \<in> explode (D (Arr \<sigma> \<rho>) (source i))" using am by (simp only: meet)
  have ta: "T (Arr \<sigma> \<rho>) i a \<in> explode (D (Arr \<sigma> \<rho>) (target ?c))"
    by (simp only: c(3); rule paper_action.transport_type[OF action[OF rt] ia a_src])
  have xc: "x \<in> explode (D \<sigma> (target ?c))" by (simp only: c(3); rule xm)
  have ea: "ev (NApp (NVar ?f) (NVar ?z)) ?c ?u = Some (app a (Opair i x))"
    by (simp only: ev_app[OF cobj rt ef ta ez xc] c(3) exp_transport_app[OF rt ia a_src xm])
  have a'm: "app a (Opair i x) \<in> explode (D \<rho> (target ?c))"
    by (simp only: c(3); rule fun_value[OF object rt am ia meet xm])
  have body: "ev ?B ?c ?u = Some (notv \<rho> ?c (app a (Opair i x)))"
    by (rule notv_ev[OF facts(2) c(1) c(2) ea a'm])
  have "Some (app (notv (Arr \<sigma> \<rho>) h a) (Opair i x)) = Some (notv \<rho> ?c (app a (Opair i x)))"
    by (simp only: s2 trq body)
  then show ?thesis by (simp only: option.inject)
qed

subsection \<open>The lifted order and emptiness, semantically\<close>

lemma orv_leq:
  assumes "paper_R_relational \<tau>" "h \<in> explode Ar" "source h = Root"
    "a \<in> explode (D \<tau> (target h))" "b \<in> explode (D \<tau> (target h))"
  shows "b = orv \<tau> h a b \<longleftrightarrow> ple \<tau> (target h) a b"
  using assms
proof (induction \<tau> arbitrary: h a b)
  case Ind
  then show ?case by (simp add: paper_R_relational_def)
next
  case Prop
  have "b = union a b \<longleftrightarrow> (\<forall>j. Elem j a \<longrightarrow> Elem j b)" by (simp only: Ext union) blast
  then show ?case by (simp only: orv_Prop[OF Prop.prems(2,4,5)] c211_pleq.simps)
next
  case (Arr \<sigma> \<rho>)
  note facts = c211_relational_Arr[OF Arr.prems(1)]
  have rt: "paper_R_type (Arr \<sigma> \<rho>)" by (rule c211_relational_type[OF Arr.prems(1)])
  have object: "target h \<in> Obj" by (rule C.target_object[OF Arr.prems(2)])
  have om: "orv (Arr \<sigma> \<rho>) h a b \<in> explode (D (Arr \<sigma> \<rho>) (target h))"
    by (rule orv_value[OF Arr.prems])
  have point: "app b (Opair i x) = app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x) \<longleftrightarrow>
      ple \<rho> (target i) (app a (Opair i x)) (app b (Opair i x))"
    if ia: "i \<in> explode Ar" and meet: "source i = target h" and xm: "x \<in> explode (D \<sigma> (target i))"
    for i x
  proof -
    note c = composite[OF Arr.prems(2,3) ia meet]
    have a'm: "app a (Opair i x) \<in> explode (D \<rho> (target (compose i h)))"
      by (simp only: c(3); rule fun_value[OF object rt Arr.prems(4) ia meet xm])
    have b'm: "app b (Opair i x) \<in> explode (D \<rho> (target (compose i h)))"
      by (simp only: c(3); rule fun_value[OF object rt Arr.prems(5) ia meet xm])
    have "app b (Opair i x) = app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x) \<longleftrightarrow>
        app b (Opair i x) = orv \<rho> (compose i h) (app a (Opair i x)) (app b (Opair i x))"
      by (simp only: orv_Arr[OF Arr.prems(1,2,3,4,5) ia meet xm])
    also have "\<dots> \<longleftrightarrow> ple \<rho> (target (compose i h)) (app a (Opair i x)) (app b (Opair i x))"
      by (rule Arr.IH(2)[OF facts(2) c(1) c(2) a'm b'm])
    finally show ?thesis by (simp only: c(3))
  qed
  have "b = orv (Arr \<sigma> \<rho>) h a b \<longleftrightarrow>
      (\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> x \<in> explode (D \<sigma> (target i)) \<longrightarrow>
        app b (Opair i x) = app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x))"
  proof
    assume eq: "b = orv (Arr \<sigma> \<rho>) h a b"
    show "\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> x \<in> explode (D \<sigma> (target i)) \<longrightarrow>
        app b (Opair i x) = app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x)"
      by (simp only: eq[symmetric]; blast)
  next
    assume pw: "\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> x \<in> explode (D \<sigma> (target i)) \<longrightarrow>
        app b (Opair i x) = app (orv (Arr \<sigma> \<rho>) h a b) (Opair i x)"
    show "b = orv (Arr \<sigma> \<rho>) h a b"
      by (rule fun_ext[OF object rt Arr.prems(5) om]) (use pw in blast)
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>i x. i \<in> explode Ar \<longrightarrow> source i = target h \<longrightarrow> x \<in> explode (D \<sigma> (target i)) \<longrightarrow>
      ple \<rho> (target i) (app a (Opair i x)) (app b (Opair i x)))"
    using point by blast
  also have "\<dots> \<longleftrightarrow> ple (Arr \<sigma> \<rho>) (target h) a b" by (simp only: c211_pleq.simps explode_Elem)
  finally show ?case .
qed

lemma notv_pempty:
  assumes "paper_R_relational \<tau>" "h \<in> explode Ar" "source h = Root" "a \<in> explode (D \<tau> (target h))"
  shows "ple \<tau> (target h) a (notv \<tau> h a) \<longleftrightarrow> pem \<tau> (target h) a"
  using assms
proof (induction \<tau> arbitrary: h a)
  case Ind
  then show ?case by (simp add: paper_R_relational_def)
next
  case Prop
  show ?case by (simp only: c211_pleq.simps c211_pempty.simps notv_Prop_member[OF Prop.prems(2,4)]) blast
next
  case (Arr \<sigma> \<rho>)
  note facts = c211_relational_Arr[OF Arr.prems(1)]
  have rt: "paper_R_type (Arr \<sigma> \<rho>)" by (rule c211_relational_type[OF Arr.prems(1)])
  have object: "target h \<in> Obj" by (rule C.target_object[OF Arr.prems(2)])
  have point: "ple \<rho> (target i) (app a (Opair i x)) (app (notv (Arr \<sigma> \<rho>) h a) (Opair i x)) \<longleftrightarrow>
      pem \<rho> (target i) (app a (Opair i x))"
    if ia: "i \<in> explode Ar" and meet: "source i = target h" and xm: "x \<in> explode (D \<sigma> (target i))"
    for i x
  proof -
    note c = composite[OF Arr.prems(2,3) ia meet]
    have a'm: "app a (Opair i x) \<in> explode (D \<rho> (target (compose i h)))"
      by (simp only: c(3); rule fun_value[OF object rt Arr.prems(4) ia meet xm])
    have "ple \<rho> (target (compose i h)) (app a (Opair i x)) (notv \<rho> (compose i h) (app a (Opair i x))) \<longleftrightarrow>
        pem \<rho> (target (compose i h)) (app a (Opair i x))"
      by (rule Arr.IH(2)[OF facts(2) c(1) c(2) a'm])
    then show ?thesis by (simp only: notv_Arr[OF Arr.prems(1,2,3,4) ia meet xm] c(3))
  qed
  show ?case unfolding c211_pleq.simps c211_pempty.simps explode_Elem[symmetric]
    using point by blast
qed

subsection \<open>S5: c211_pleq is a partial order on each carrier\<close>

lemma pleq_antisym:
  assumes "paper_R_type \<tau>" "W \<in> Obj" "a \<in> explode (D \<tau> W)" "b \<in> explode (D \<tau> W)"
    "ple \<tau> W a b" "ple \<tau> W b a"
  shows "a = b"
  using assms
proof (induction \<tau> arbitrary: W a b)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case by (simp only: c211_pleq.simps Ext) blast
next
  case (Arr \<sigma> \<rho>)
  have r2: "paper_R_type \<rho>" using Arr.prems(1) by simp
  show ?case
  proof (rule fun_ext[OF Arr.prems(2,1,3,4)])
    fix i x
    assume ia: "i \<in> explode Ar" and si: "source i = W" and xm: "x \<in> explode (D \<sigma> (target i))"
    have xe: "Elem x (D \<sigma> (target i))" using xm by (simp only: explode_Elem)
    have tobj: "target i \<in> Obj" by (rule C.target_object[OF ia])
    have a'm: "app a (Opair i x) \<in> explode (D \<rho> (target i))"
      by (rule fun_value[OF Arr.prems(2,1,3) ia si xm])
    have b'm: "app b (Opair i x) \<in> explode (D \<rho> (target i))"
      by (rule fun_value[OF Arr.prems(2,1,4) ia si xm])
    have ab: "ple \<rho> (target i) (app a (Opair i x)) (app b (Opair i x))"
      using Arr.prems(5) ia si xe by (simp only: c211_pleq.simps)
    have ba: "ple \<rho> (target i) (app b (Opair i x)) (app a (Opair i x))"
      using Arr.prems(6) ia si xe by (simp only: c211_pleq.simps)
    show "app a (Opair i x) = app b (Opair i x)" by (rule Arr.IH(2)[OF r2 tobj a'm b'm ab ba])
  qed
qed

subsection \<open>S3, S4: the object-language ≤ and x ≤ ¬x\<close>

theorem le_holds:
  assumes rel: "paper_R_relational \<tau>" and al: "lang A \<tau>" and bl: "lang B \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and adequate: "named_adequate g (c211_le \<tau> A B)"
    and ae: "ev A h g = Some a" and be: "ev B h g = Some b"
  shows "sat h g (c211_le \<tau> A B) \<longleftrightarrow> ple \<tau> (target h) a b"
proof -
  let ?x = "c211_v \<tau> 3" and ?y = "c211_v \<tau> 4"
  let ?O = "NApp (NApp (c211_or \<tau>) (NVar ?x)) (NVar ?y) :: 'c paper_named_term"
  let ?E = "named_paper_eq \<tau> (NVar ?y) ?O"
  let ?k = "g(?x := Some a, ?y := Some b)"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  have aa: "named_adequate g A" and ba: "named_adequate g B"
    using adequate by (simp_all only: named_adequate_def c211_le_fv Un_subset_iff)
  have ll: "lang (NLam ?x (NLam ?y ?E)) (Arr \<tau> (Arr \<tau> Prop))"
    using c211_leq_language[OF rel] by (simp only: c211_leq_def)
  have la: "named_adequate g (NLam ?x (NLam ?y ?E))"
    using c211_leq_closed[of \<tau>, where 'a='c] by (simp only: named_adequate_def c211_leq_def empty_subsetI)
  have am: "a \<in> explode (D \<tau> (target h))" by (rule ev_member[OF al arrow origin typed aa ae])
  have bm: "b \<in> explode (D \<tau> (target h))" by (rule ev_member[OF bl arrow origin typed ba be])
  have red: "ev (c211_le \<tau> A B) h g = ev ?E h ?k"
    unfolding c211_le_def c211_leq_def
    by (rule ev_beta2[OF arrow origin typed ll c211_v_type c211_v_type al bl la aa ba ae be])
  have kt: "env (target h) ?k"
    by (rule paper_ZF_action_env_update[OF paper_ZF_action_env_update[OF typed c211_v_type tt am]
      c211_v_type tt bm])
  have ex: "ev (NVar ?x) h ?k = Some a" by simp
  have ey: "ev (NVar ?y) h ?k = Some b" by simp
  have eo: "ev ?O h ?k = Some (orv \<tau> h a b)" by (rule orv_ev[OF rel arrow origin ex am ey bm])
  have yl: "lang (NVar ?y) \<tau>" by (rule c211_lang_Var[OF tt])
  have ol: "lang ?O \<tau>"
    by (rule paper_R_language_App[OF paper_R_language_App[OF c211_or_language[OF rel]
      c211_lang_Var[OF tt]] yl])
  have ya: "named_adequate ?k (NVar ?y)" by (simp add: named_adequate_def)
  have oa: "named_adequate ?k ?O" by (simp add: named_adequate_def c211_or_closed)
  have "sat h g (c211_le \<tau> A B) \<longleftrightarrow> sat h ?k ?E" by (rule sat_ev_cong[OF red])
  also have "\<dots> \<longleftrightarrow> b = orv \<tau> h a b" by (rule sat_eq[OF arrow origin kt yl ol ya oa ey eo])
  also have "\<dots> \<longleftrightarrow> ple \<tau> (target h) a b" by (rule orv_leq[OF rel arrow origin am bm])
  finally show ?thesis .
qed

theorem le_neg_holds:
  assumes rel: "paper_R_relational \<tau>" and al: "lang A \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and adequate: "named_adequate g (c211_le \<tau> A (c211_neg \<tau> A))"
    and ae: "ev A h g = Some a"
  shows "sat h g (c211_le \<tau> A (c211_neg \<tau> A)) \<longleftrightarrow> pem \<tau> (target h) a"
proof -
  have aa: "named_adequate g A"
    using adequate by (simp only: named_adequate_def c211_le_fv c211_neg_fv Un_absorb)
  have am: "a \<in> explode (D \<tau> (target h))" by (rule ev_member[OF al arrow origin typed aa ae])
  have ne: "ev (c211_neg \<tau> A) h g = Some (notv \<tau> h a)"
    unfolding c211_neg_def by (rule notv_ev[OF rel arrow origin ae am])
  have "sat h g (c211_le \<tau> A (c211_neg \<tau> A)) \<longleftrightarrow> ple \<tau> (target h) a (notv \<tau> h a)"
    by (rule le_holds[OF rel al c211_neg_language[OF rel al] arrow origin typed adequate ae ne])
  also have "\<dots> \<longleftrightarrow> pem \<tau> (target h) a" by (rule notv_pempty[OF rel arrow origin am])
  finally show ?thesis .
qed

subsection \<open>S6, S7: Atom and Atomicity\<close>

theorem atom_holds:
  assumes rel: "paper_R_relational \<tau>" and yl: "lang Y \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and adequate: "named_adequate g (NApp (c211_atom \<tau>) Y)" and ye: "ev Y h g = Some y"
  shows "sat h g (NApp (c211_atom \<tau>) Y) \<longleftrightarrow> c211_patom Ar source target D \<tau> (target h) y"
proof -
  let ?a = "c211_v \<tau> 5" and ?b = "c211_v \<tau> 6"
  let ?La = "c211_le \<tau> (NVar ?b) (NVar ?a) :: 'c paper_named_term"
  let ?Na = "c211_neq \<tau> (NVar ?b) (NVar ?a) :: 'c paper_named_term"
  let ?Lb = "c211_le \<tau> (NVar ?b) (c211_neg \<tau> (NVar ?b)) :: 'c paper_named_term"
  let ?Bd = "c211_iff (named_paper_and ?La ?Na) ?Lb"
  let ?A = "named_paper_all \<tau> (NLam ?b ?Bd)"
  let ?W = "target h"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  note v = c211_lang_Var[OF tt]
  have l1: "lang ?La Prop" by (rule c211_le_language[OF rel v v])
  have n1: "lang ?Na Prop" by (rule c211_neq_language[OF tt v v])
  have l2: "lang ?Lb Prop" by (rule c211_le_language[OF rel v c211_neg_language[OF rel v]])
  have c1: "lang (named_paper_and ?La ?Na) Prop" by (rule paper_R_named_and_language[OF l1 n1])
  have bdl: "lang ?Bd Prop" by (rule c211_connective_language(4)[OF c1 l2])
  have ll: "lang (NLam ?a ?A) (Arr \<tau> Prop)" using c211_atom_language[OF rel] by (simp only: c211_atom_def)
  have la: "named_adequate g (NLam ?a ?A)"
    using c211_atom_closed[of \<tau>, where 'a='c] by (simp only: named_adequate_def c211_atom_def empty_subsetI)
  have ya: "named_adequate g Y" using adequate by (simp add: named_adequate_def)
  have ym: "y \<in> explode (D \<tau> ?W)" by (rule ev_member[OF yl arrow origin typed ya ye])
  have red: "ev (NApp (c211_atom \<tau>) Y) h g = ev ?A h (g(?a := Some y))"
    unfolding c211_atom_def by (rule ev_beta[OF arrow origin typed ll c211_v_type yl la ya ye])
  have gt: "env ?W (g(?a := Some y))" by (rule paper_ZF_action_env_update[OF typed c211_v_type tt ym])
  have ba: "named_adequate (g(?a := Some y)) (NLam ?b ?Bd)"
    by (auto simp: named_adequate_def c211_fv_simps)
  have point: "sat h (g(?a := Some y, ?b := Some z)) ?Bd \<longleftrightarrow>
      ((ple \<tau> ?W z y \<and> z \<noteq> y) \<longleftrightarrow> pem \<tau> ?W z)"
    if zm: "z \<in> explode (D \<tau> ?W)" for z
  proof -
    let ?k = "g(?a := Some y, ?b := Some z)"
    have kt: "env ?W ?k" by (rule paper_ZF_action_env_update[OF gt c211_v_type tt zm])
    have ea: "ev (NVar ?a) h ?k = Some y" by simp
    have eb: "ev (NVar ?b) h ?k = Some z" by simp
    have aa: "named_adequate ?k (NVar ?a)" and bb: "named_adequate ?k (NVar ?b)"
      by (simp_all add: named_adequate_def)
    have l1a: "named_adequate ?k ?La" and n1a: "named_adequate ?k ?Na" and l2a: "named_adequate ?k ?Lb"
      and c1a: "named_adequate ?k (named_paper_and ?La ?Na)"
      by (simp_all add: named_adequate_def c211_fv_simps)
    have eqa: "named_adequate ?k (named_paper_eq \<tau> (NVar ?b) (NVar ?a))"
      by (simp add: named_adequate_def c211_fv_simps)
    have s1: "sat h ?k ?La \<longleftrightarrow> ple \<tau> ?W z y" by (rule le_holds[OF rel v v arrow origin kt l1a eb ea])
    have s2: "sat h ?k ?Na \<longleftrightarrow> z \<noteq> y"
      unfolding c211_neq_def
      by (simp only: sat_not[OF arrow origin kt paper_R_named_eq_language[OF v v] eqa]
        sat_eq[OF arrow origin kt v v bb aa eb ea])
    have s3: "sat h ?k ?Lb \<longleftrightarrow> pem \<tau> ?W z" by (rule le_neg_holds[OF rel v arrow origin kt l2a eb])
    show ?thesis
      by (simp only: sat_iff[OF arrow origin kt c1 l2 c1a l2a] sat_and[OF arrow origin kt l1 n1 l1a n1a]
        s1 s2 s3)
  qed
  have "sat h g (NApp (c211_atom \<tau>) Y) \<longleftrightarrow> sat h (g(?a := Some y)) ?A" by (rule sat_ev_cong[OF red])
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D \<tau> ?W). sat h (g(?a := Some y, ?b := Some z)) ?Bd)"
    by (rule sat_all[OF arrow origin gt bdl c211_v_type tt ba])
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D \<tau> ?W). (ple \<tau> ?W z y \<and> z \<noteq> y) \<longleftrightarrow> pem \<tau> ?W z)"
    by (rule ball_cong[OF refl point])
  also have "\<dots> \<longleftrightarrow> c211_patom Ar source target D \<tau> ?W y"
    by (simp only: c211_patom_def Ball_def explode_Elem)
  finally show ?thesis .
qed

theorem atomicity_holds:
  assumes rel: "paper_R_relational \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
  shows "sat h g (c211_atomicity \<tau>) \<longleftrightarrow> c211_patomic Ar source target D \<tau> (target h)"
proof -
  let ?x = "c211_v \<tau> 7" and ?y = "c211_v \<tau> 8"
  let ?L = "c211_le \<tau> (NVar ?x) (c211_neg \<tau> (NVar ?x)) :: 'c paper_named_term"
  let ?At = "NApp (c211_atom \<tau>) (NVar ?y) :: 'c paper_named_term"
  let ?Ly = "c211_le \<tau> (NVar ?y) (NVar ?x) :: 'c paper_named_term"
  let ?Rb = "named_paper_and ?At ?Ly"
  let ?R = "named_paper_ex \<tau> (NLam ?y ?Rb)"
  let ?Bd = "named_paper_or ?L ?R"
  let ?W = "target h"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  note v = c211_lang_Var[OF tt]
  have ll: "lang ?L Prop" by (rule c211_le_language[OF rel v c211_neg_language[OF rel v]])
  have atl: "lang ?At Prop" by (rule paper_R_language_App[OF c211_atom_language[OF rel] v])
  have lyl: "lang ?Ly Prop" by (rule c211_le_language[OF rel v v])
  have r0l: "lang ?Rb Prop" by (rule paper_R_named_and_language[OF atl lyl])
  have rl: "lang ?R Prop" by (rule c211_ex_language[OF tt r0l])
  have bdl: "lang ?Bd Prop" by (rule paper_R_named_or_language[OF ll rl])
  have ba: "named_adequate g (NLam ?x ?Bd)"
    by (auto simp: named_adequate_def c211_fv_simps c211_atom_closed)
  have point: "sat h (g(?x := Some x)) ?Bd \<longleftrightarrow>
      (pem \<tau> ?W x \<or> (\<exists>y\<in>explode (D \<tau> ?W). c211_patom Ar source target D \<tau> ?W y \<and> ple \<tau> ?W y x))"
    if xm: "x \<in> explode (D \<tau> ?W)" for x
  proof -
    let ?k = "g(?x := Some x)"
    have kt: "env ?W ?k" by (rule paper_ZF_action_env_update[OF typed c211_v_type tt xm])
    have ex: "ev (NVar ?x) h ?k = Some x" by simp
    have la: "named_adequate ?k ?L" and ra: "named_adequate ?k ?R"
      by (auto simp: named_adequate_def c211_fv_simps c211_atom_closed)
    have r0a: "named_adequate ?k (NLam ?y ?Rb)"
      by (auto simp: named_adequate_def c211_fv_simps c211_atom_closed)
    have inner: "sat h (?k(?y := Some y)) ?Rb \<longleftrightarrow>
        c211_patom Ar source target D \<tau> ?W y \<and> ple \<tau> ?W y x"
      if ym: "y \<in> explode (D \<tau> ?W)" for y
    proof -
      let ?n = "?k(?y := Some y)"
      have nt: "env ?W ?n" by (rule paper_ZF_action_env_update[OF kt c211_v_type tt ym])
      have ey: "ev (NVar ?y) h ?n = Some y" by simp
      have ex': "ev (NVar ?x) h ?n = Some x" by simp
      have ata: "named_adequate ?n ?At" and lya: "named_adequate ?n ?Ly"
        by (auto simp: named_adequate_def c211_fv_simps c211_atom_closed)
      show ?thesis
        by (simp only: sat_and[OF arrow origin nt atl lyl ata lya]
          atom_holds[OF rel v arrow origin nt ata ey] le_holds[OF rel v v arrow origin nt lya ey ex'])
    qed
    have "sat h ?k ?Bd \<longleftrightarrow> sat h ?k ?L \<or> sat h ?k ?R" by (rule sat_or[OF arrow origin kt ll rl la ra])
    also have "\<dots> \<longleftrightarrow> pem \<tau> ?W x \<or> (\<exists>y\<in>explode (D \<tau> ?W). sat h (?k(?y := Some y)) ?Rb)"
      by (simp only: le_neg_holds[OF rel v arrow origin kt la ex] sat_ex[OF arrow origin kt r0l c211_v_type tt r0a])
    also have "\<dots> \<longleftrightarrow> pem \<tau> ?W x \<or>
        (\<exists>y\<in>explode (D \<tau> ?W). c211_patom Ar source target D \<tau> ?W y \<and> ple \<tau> ?W y x)"
      using inner by blast
    finally show ?thesis .
  qed
  have "sat h g (c211_atomicity \<tau>) \<longleftrightarrow> (\<forall>x\<in>explode (D \<tau> ?W). sat h (g(?x := Some x)) ?Bd)"
    unfolding c211_atomicity_def by (rule sat_all[OF arrow origin typed bdl c211_v_type tt ba])
  also have "\<dots> \<longleftrightarrow> (\<forall>x\<in>explode (D \<tau> ?W). pem \<tau> ?W x \<or>
      (\<exists>y\<in>explode (D \<tau> ?W). c211_patom Ar source target D \<tau> ?W y \<and> ple \<tau> ?W y x))"
    by (rule ball_cong[OF refl point])
  also have "\<dots> \<longleftrightarrow> c211_patomic Ar source target D \<tau> ?W"
    by (simp only: c211_patomic_def Ball_def Bex_def explode_Elem)
  finally show ?thesis .
qed

subsection \<open>S8: □Atomicity at the root\<close>

lemma compose_root_identity:
  "i \<in> explode Ar \<Longrightarrow> source i = Root \<Longrightarrow> compose i (identity Root) = i"
  using C.identity_right by metis

theorem box_atomicity_valid:
  assumes rel: "paper_R_relational \<tau>"
    and atomic: "\<forall>h. h \<in> explode Ar \<longrightarrow> source h = Root \<longrightarrow> c211_patomic Ar source target D \<tau> (target h)"
  shows "c211_valid \<Sigma> c211_G Ar source target compose identity Root D T I (c211_box_atomicity \<tau>)"
  unfolding c211_valid_def
proof (intro conjI allI impI)
  note r = c211_root_identity[OF model]
  show "lang (c211_box_atomicity \<tau>) Prop" by (rule c211_box_atomicity_language[OF rel])
  fix g
  assume typed: "env (target (identity Root)) g" and adequate: "named_adequate g (c211_box_atomicity \<tau>)"
  have al: "lang (c211_atomicity \<tau>) Prop" by (rule c211_atomicity_language[OF rel])
  have aa: "named_adequate g (c211_atomicity \<tau>)" by (simp add: named_adequate_def c211_atomicity_closed)
  have pointwise: "sat (compose i (identity Root)) (tr i g) (c211_atomicity \<tau>)"
    if ia: "i \<in> explode Ar" and meet: "source i = target (identity Root)" for i
  proof -
    have si: "source i = Root" using meet by (simp only: r(3))
    have st: "env (source i) g" using typed by (simp only: r(3) si)
    have ut: "env (target i) (tr i g)" by (rule transported_env[OF ia st])
    have "sat i (tr i g) (c211_atomicity \<tau>)"
      by (simp only: atomicity_holds[OF rel ia si ut]; rule atomic[rule_format, OF ia si])
    then show ?thesis by (simp only: compose_root_identity[OF ia si])
  qed
  show "sat (identity Root) g (c211_box_atomicity \<tau>)"
    unfolding c211_box_atomicity_def
    by (simp only: sat_box[OF r(1) r(2) typed al aa]; intro allI impI; rule pointwise)
qed

subsection \<open>S9: c211_pcomplete suffices for Boolean Completeness\<close>

lemma lb_holds:
  assumes rel: "paper_R_relational \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) k"
    and zl: "lang Z \<tau>" and xl: "lang Xt (Arr \<tau> Prop)"
    and za: "named_adequate k Z" and xa: "named_adequate k Xt"
    and ze: "ev Z h k = Some z" and xe: "ev Xt h k = Some X"
  shows "sat h k (NApp (NApp (c211_LB \<tau>) Z) Xt) \<longleftrightarrow>
    (\<forall>w\<in>explode (D \<tau> (target h)).
      Elem (identity (target h)) (app X (Opair (identity (target h)) w)) \<longrightarrow> ple \<tau> (target h) z w)"
proof -
  let ?z = "c211_v \<tau> 9" and ?X = "c211_v (Arr \<tau> Prop) 0" and ?w = "c211_v \<tau> 10"
  let ?P = "NApp (NVar ?X) (NVar ?w) :: 'c paper_named_term"
  let ?Q = "c211_le \<tau> (NVar ?z) (NVar ?w) :: 'c paper_named_term"
  let ?Bd = "c211_imp ?P ?Q"
  let ?A = "named_paper_all \<tau> (NLam ?w ?Bd)"
  let ?W = "target h"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rel])
  have object: "?W \<in> Obj" by (rule C.target_object[OF arrow])
  have Pl: "lang ?P Prop" by (rule paper_R_language_App[OF c211_lang_Var[OF pt] c211_lang_Var[OF tt]])
  have Ql: "lang ?Q Prop" by (rule c211_le_language[OF rel c211_lang_Var[OF tt] c211_lang_Var[OF tt]])
  have bdl: "lang ?Bd Prop" by (rule c211_connective_language(3)[OF Pl Ql])
  have ll: "lang (NLam ?z (NLam ?X ?A)) (Arr \<tau> (Arr (Arr \<tau> Prop) Prop))"
    using c211_LB_language[OF rel] by (simp only: c211_LB_def)
  have la: "named_adequate k (NLam ?z (NLam ?X ?A))"
    using c211_LB_closed[of \<tau>, where 'a='c] by (simp only: named_adequate_def c211_LB_def empty_subsetI)
  have zm: "z \<in> explode (D \<tau> ?W)" by (rule ev_member[OF zl arrow origin typed za ze])
  have Xm: "X \<in> explode (D (Arr \<tau> Prop) ?W)" by (rule ev_member[OF xl arrow origin typed xa xe])
  have red: "ev (NApp (NApp (c211_LB \<tau>) Z) Xt) h k = ev ?A h (k(?z := Some z, ?X := Some X))"
    unfolding c211_LB_def by (rule ev_beta2[OF arrow origin typed ll c211_v_type c211_v_type zl xl la za xa ze xe])
  let ?m = "k(?z := Some z, ?X := Some X)"
  have mt: "env ?W ?m"
    by (rule paper_ZF_action_env_update[OF paper_ZF_action_env_update[OF typed c211_v_type tt zm]
      c211_v_type pt Xm])
  have ma: "named_adequate ?m (NLam ?w ?Bd)" by (auto simp: named_adequate_def c211_fv_simps)
  have point: "sat h (?m(?w := Some w)) ?Bd \<longleftrightarrow>
      (Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow> ple \<tau> ?W z w)"
    if wm: "w \<in> explode (D \<tau> ?W)" for w
  proof -
    let ?n = "?m(?w := Some w)"
    have nt: "env ?W ?n" by (rule paper_ZF_action_env_update[OF mt c211_v_type tt wm])
    have eX: "ev (NVar ?X) h ?n = Some X" by simp
    have ew: "ev (NVar ?w) h ?n = Some w" by simp
    have ez: "ev (NVar ?z) h ?n = Some z" by simp
    have Pa: "named_adequate ?n ?P" and Qa: "named_adequate ?n ?Q"
      by (auto simp: named_adequate_def c211_fv_simps)
    have eP: "ev ?P h ?n = Some (app X (Opair (identity ?W) w))" by (rule ev_app[OF object pt eX Xm ew wm])
    show ?thesis
      by (simp only: sat_imp[OF arrow origin nt Pl Ql Pa Qa] sat_value[OF eP]
        le_holds[OF rel c211_lang_Var[OF tt] c211_lang_Var[OF tt] arrow origin nt Qa ez ew])
  qed
  have "sat h k (NApp (NApp (c211_LB \<tau>) Z) Xt) \<longleftrightarrow> sat h ?m ?A" by (rule sat_ev_cong[OF red])
  also have "\<dots> \<longleftrightarrow> (\<forall>w\<in>explode (D \<tau> ?W). sat h (?m(?w := Some w)) ?Bd)"
    by (rule sat_all[OF arrow origin mt bdl c211_v_type tt ma])
  also have "\<dots> \<longleftrightarrow> (\<forall>w\<in>explode (D \<tau> ?W).
      Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow> ple \<tau> ?W z w)"
    by (rule ball_cong[OF refl point])
  finally show ?thesis .
qed

lemma glb_holds:
  assumes rel: "paper_R_relational \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) k"
    and yl: "lang Yt \<tau>" and xl: "lang Xt (Arr \<tau> Prop)"
    and ya: "named_adequate k Yt" and xa: "named_adequate k Xt"
    and ye: "ev Yt h k = Some y" and xe: "ev Xt h k = Some X"
  shows "sat h k (NApp (NApp (c211_GLB \<tau>) Yt) Xt) \<longleftrightarrow>
    (\<forall>z\<in>explode (D \<tau> (target h)).
      (\<forall>w\<in>explode (D \<tau> (target h)).
        Elem (identity (target h)) (app X (Opair (identity (target h)) w)) \<longrightarrow> ple \<tau> (target h) z w)
      \<longleftrightarrow> ple \<tau> (target h) z y)"
proof -
  let ?y = "c211_v \<tau> 11" and ?X = "c211_v (Arr \<tau> Prop) 1" and ?z = "c211_v \<tau> 12"
  let ?P = "NApp (NApp (c211_LB \<tau>) (NVar ?z)) (NVar ?X) :: 'c paper_named_term"
  let ?Q = "c211_le \<tau> (NVar ?z) (NVar ?y) :: 'c paper_named_term"
  let ?Bd = "c211_iff ?P ?Q"
  let ?A = "named_paper_all \<tau> (NLam ?z ?Bd)"
  let ?W = "target h"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rel])
  have Pl: "lang ?P Prop"
    by (rule paper_R_language_App[OF paper_R_language_App[OF c211_LB_language[OF rel]
      c211_lang_Var[OF tt]] c211_lang_Var[OF pt]])
  have Ql: "lang ?Q Prop" by (rule c211_le_language[OF rel c211_lang_Var[OF tt] c211_lang_Var[OF tt]])
  have bdl: "lang ?Bd Prop" by (rule c211_connective_language(4)[OF Pl Ql])
  have ll: "lang (NLam ?y (NLam ?X ?A)) (Arr \<tau> (Arr (Arr \<tau> Prop) Prop))"
    using c211_GLB_language[OF rel] by (simp only: c211_GLB_def)
  have la: "named_adequate k (NLam ?y (NLam ?X ?A))"
    using c211_GLB_closed[of \<tau>, where 'a='c] by (simp only: named_adequate_def c211_GLB_def empty_subsetI)
  have ym: "y \<in> explode (D \<tau> ?W)" by (rule ev_member[OF yl arrow origin typed ya ye])
  have Xm: "X \<in> explode (D (Arr \<tau> Prop) ?W)" by (rule ev_member[OF xl arrow origin typed xa xe])
  have red: "ev (NApp (NApp (c211_GLB \<tau>) Yt) Xt) h k = ev ?A h (k(?y := Some y, ?X := Some X))"
    unfolding c211_GLB_def by (rule ev_beta2[OF arrow origin typed ll c211_v_type c211_v_type yl xl la ya xa ye xe])
  let ?m = "k(?y := Some y, ?X := Some X)"
  have mt: "env ?W ?m"
    by (rule paper_ZF_action_env_update[OF paper_ZF_action_env_update[OF typed c211_v_type tt ym]
      c211_v_type pt Xm])
  have ma: "named_adequate ?m (NLam ?z ?Bd)" by (auto simp: named_adequate_def c211_fv_simps c211_LB_closed)
  have point: "sat h (?m(?z := Some z)) ?Bd \<longleftrightarrow>
      ((\<forall>w\<in>explode (D \<tau> ?W). Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow> ple \<tau> ?W z w)
        \<longleftrightarrow> ple \<tau> ?W z y)"
    if zm: "z \<in> explode (D \<tau> ?W)" for z
  proof -
    let ?n = "?m(?z := Some z)"
    have nt: "env ?W ?n" by (rule paper_ZF_action_env_update[OF mt c211_v_type tt zm])
    have eX: "ev (NVar ?X) h ?n = Some X" by simp
    have ey: "ev (NVar ?y) h ?n = Some y" by simp
    have ez: "ev (NVar ?z) h ?n = Some z" by simp
    have Pa: "named_adequate ?n ?P" and Qa: "named_adequate ?n ?Q"
      by (auto simp: named_adequate_def c211_fv_simps c211_LB_closed)
    have za: "named_adequate ?n (NVar ?z)" and Xa: "named_adequate ?n (NVar ?X)"
      by (simp_all add: named_adequate_def)
    show ?thesis
      by (simp only: sat_iff[OF arrow origin nt Pl Ql Pa Qa]
        lb_holds[OF rel arrow origin nt c211_lang_Var[OF tt] c211_lang_Var[OF pt] za Xa ez eX]
        le_holds[OF rel c211_lang_Var[OF tt] c211_lang_Var[OF tt] arrow origin nt Qa ez ey])
  qed
  have "sat h k (NApp (NApp (c211_GLB \<tau>) Yt) Xt) \<longleftrightarrow> sat h ?m ?A" by (rule sat_ev_cong[OF red])
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D \<tau> ?W). sat h (?m(?z := Some z)) ?Bd)"
    by (rule sat_all[OF arrow origin mt bdl c211_v_type tt ma])
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>explode (D \<tau> ?W).
      (\<forall>w\<in>explode (D \<tau> ?W). Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow> ple \<tau> ?W z w)
        \<longleftrightarrow> ple \<tau> ?W z y)"
    by (rule ball_cong[OF refl point])
  finally show ?thesis .
qed

theorem BC_holds:
  assumes rel: "paper_R_relational \<tau>"
    and arrow: "h \<in> explode Ar" and origin: "source h = Root" and typed: "env (target h) g"
    and complete: "c211_pcomplete Ar source target D \<tau> (target h)"
  shows "sat h g (c211_BC \<tau>)"
proof -
  let ?X = "c211_v (Arr \<tau> Prop) 2" and ?y = "c211_v \<tau> 13"
  let ?Gb = "NApp (NApp (c211_GLB \<tau>) (NVar ?y)) (NVar ?X) :: 'c paper_named_term"
  let ?E = "named_paper_ex \<tau> (NLam ?y ?Gb)"
  let ?W = "target h"
  have tt: "paper_R_type \<tau>" by (rule c211_relational_type[OF rel])
  have pt: "paper_R_type (Arr \<tau> Prop)" by (rule c211_pred_type[OF rel])
  have g0l: "lang ?Gb Prop"
    by (rule paper_R_language_App[OF paper_R_language_App[OF c211_GLB_language[OF rel]
      c211_lang_Var[OF tt]] c211_lang_Var[OF pt]])
  have el: "lang ?E Prop" by (rule c211_ex_language[OF tt g0l])
  have ea: "named_adequate g (NLam ?X ?E)"
    by (auto simp: named_adequate_def c211_fv_simps c211_GLB_closed)
  have each: "sat h (g(?X := Some X)) ?E" if Xm: "X \<in> explode (D (Arr \<tau> Prop) ?W)" for X
  proof -
    let ?m = "g(?X := Some X)"
    let ?S = "{w \<in> explode (D \<tau> ?W). Elem (identity ?W) (app X (Opair (identity ?W) w))}"
    have mt: "env ?W ?m" by (rule paper_ZF_action_env_update[OF typed c211_v_type pt Xm])
    have ma: "named_adequate ?m (NLam ?y ?Gb)"
      by (auto simp: named_adequate_def c211_fv_simps c211_GLB_closed)
    have sub: "?S \<subseteq> explode (D \<tau> ?W)" by blast
    obtain m where mm: "Elem m (D \<tau> ?W)"
      and glb: "\<forall>z. Elem z (D \<tau> ?W) \<longrightarrow> ((\<forall>w\<in>?S. ple \<tau> ?W z w) \<longleftrightarrow> ple \<tau> ?W z m)"
      using complete[unfolded c211_pcomplete_def, rule_format, OF sub] by blast
    have mx: "m \<in> explode (D \<tau> ?W)" using mm by (simp only: explode_Elem)
    let ?n = "?m(?y := Some m)"
    have nt: "env ?W ?n" by (rule paper_ZF_action_env_update[OF mt c211_v_type tt mx])
    have ey: "ev (NVar ?y) h ?n = Some m" by simp
    have eX: "ev (NVar ?X) h ?n = Some X" by simp
    have ya: "named_adequate ?n (NVar ?y)" and Xa: "named_adequate ?n (NVar ?X)"
      by (simp_all add: named_adequate_def)
    have witness: "\<forall>z\<in>explode (D \<tau> ?W).
        (\<forall>w\<in>explode (D \<tau> ?W). Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow> ple \<tau> ?W z w)
        \<longleftrightarrow> ple \<tau> ?W z m"
    proof
      fix z
      assume zm: "z \<in> explode (D \<tau> ?W)"
      have ze: "Elem z (D \<tau> ?W)" using zm by (simp only: explode_Elem)
      have "(\<forall>w\<in>?S. ple \<tau> ?W z w) \<longleftrightarrow> ple \<tau> ?W z m" using glb ze by blast
      then show "(\<forall>w\<in>explode (D \<tau> ?W). Elem (identity ?W) (app X (Opair (identity ?W) w)) \<longrightarrow>
          ple \<tau> ?W z w) \<longleftrightarrow> ple \<tau> ?W z m" by blast
    qed
    have g0: "sat h ?n ?Gb"
      by (simp only: glb_holds[OF rel arrow origin nt c211_lang_Var[OF tt] c211_lang_Var[OF pt] ya Xa ey eX];
        rule witness)
    show ?thesis
      using g0 mx by (simp only: sat_ex[OF arrow origin mt g0l c211_v_type tt ma]) blast
  qed
  show ?thesis unfolding c211_BC_def
    by (simp only: sat_all[OF arrow origin typed el c211_v_type pt ea]; rule ballI; rule each)
qed

theorem BC_valid:
  assumes rel: "paper_R_relational \<tau>" and complete: "c211_pcomplete Ar source target D \<tau> Root"
  shows "c211_valid \<Sigma> c211_G Ar source target compose identity Root D T I (c211_BC \<tau>)"
  unfolding c211_valid_def
proof (intro conjI allI impI)
  note r = c211_root_identity[OF model]
  show "lang (c211_BC \<tau>) Prop" by (rule c211_BC_language[OF rel])
  fix g
  assume typed: "env (target (identity Root)) g"
  have rc: "c211_pcomplete Ar source target D \<tau> (target (identity Root))"
    by (simp only: r(3); rule complete)
  show "sat (identity Root) g (c211_BC \<tau>)" by (rule BC_holds[OF rel r(1) r(2) typed rc])
qed

end

subsection \<open>Exported endpoints (the locale assumption is the model condition)\<close>

lemmas c211_box_holds = c211_sem.sat_box[unfolded c211_sem_def]
lemmas c211_or_value_type = c211_sem.orv_value[unfolded c211_sem_def]
lemmas c211_or_eval = c211_sem.orv_ev[unfolded c211_sem_def]
lemmas c211_or_Prop = c211_sem.orv_Prop[unfolded c211_sem_def]
lemmas c211_or_Arr = c211_sem.orv_Arr[unfolded c211_sem_def]
lemmas c211_not_value_type = c211_sem.notv_value[unfolded c211_sem_def]
lemmas c211_not_eval = c211_sem.notv_ev[unfolded c211_sem_def]
lemmas c211_not_Prop_member = c211_sem.notv_Prop_member[unfolded c211_sem_def]
lemmas c211_not_Arr = c211_sem.notv_Arr[unfolded c211_sem_def]
lemmas c211_le_holds = c211_sem.le_holds[unfolded c211_sem_def]
lemmas c211_le_neg_holds = c211_sem.le_neg_holds[unfolded c211_sem_def]
lemmas c211_pleq_antisym = c211_sem.pleq_antisym[unfolded c211_sem_def]
lemmas c211_atom_holds = c211_sem.atom_holds[unfolded c211_sem_def]
lemmas c211_atomicity_holds = c211_sem.atomicity_holds[unfolded c211_sem_def]
lemmas c211_box_atomicity_valid = c211_sem.box_atomicity_valid[unfolded c211_sem_def]
lemmas c211_BC_holds = c211_sem.BC_holds[unfolded c211_sem_def]
lemmas c211_BC_valid = c211_sem.BC_valid[unfolded c211_sem_def]

text \<open>
  Sources: Figure 1, p.6 (lifted ∨, ¬, ≤ and □); Boolean Completeness,
  GLB and LB, pp.23–24; Atom and Atomicity, p.24;
  Definitions 3.18–3.20, pp.55–56. Every endpoint is generic: it holds
  in every action model over the standard stock. c211_pcomplete is only
  a sufficient condition for Boolean Completeness. None of these
  endpoints instantiates the concrete Proposition 2.11 model.
\<close>

ML \<open>
  val c211_order_semantics_names = ["c211_pleq_refl", "c211_pleq_trans", "c211_pempty_pleq",
    "c211_box_holds", "c211_or_value_type", "c211_or_eval", "c211_or_Prop", "c211_or_Arr",
    "c211_not_value_type", "c211_not_eval", "c211_not_Prop_member", "c211_not_Arr",
    "c211_le_holds", "c211_le_neg_holds", "c211_pleq_antisym", "c211_atom_holds",
    "c211_atomicity_holds", "c211_box_atomicity_valid", "c211_BC_holds", "c211_BC_valid",
    "c211_sem.sat_not", "c211_sem.sat_and", "c211_sem.sat_or", "c211_sem.sat_imp",
    "c211_sem.sat_iff", "c211_sem.sat_eq", "c211_sem.sat_all", "c211_sem.sat_ex",
    "c211_sem.ev_beta", "c211_sem.ev_beta2", "c211_sem.ev_app", "c211_sem.ev_lam",
    "c211_sem.fun_ext", "c211_sem.orv_leq", "c211_sem.notv_pempty"];
  val facts = map (Proof_Context.get_thm \<^context>) c211_order_semantics_names;
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln ("C211-ORDER-SEMANTICS: " ^ string_of_int (length facts) ^
    " clean generic endpoints (□, lifted ∨/¬, ≤, x≤¬x, order, Atom, Atomicity, □Atomicity, BC)");
\<close>

end
