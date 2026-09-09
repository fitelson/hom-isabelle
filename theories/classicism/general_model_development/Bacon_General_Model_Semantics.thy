theory Bacon_General_Model_Semantics
  imports Bacon_BBK_Semantics_Development.Bacon_BBK_One_Binder
begin

section \<open>General models and Leibniz equivalence\<close>

text \<open>
  a ≈ₗₑ b ⇔ ∀F ∈ Dσ→t, v(Fa) = v(Fb); Leibnizianity is a ≈ₗₑ b ⇒ a = b. Bacon,
  Definitions 15.1, 15.5, and 15.6, pp. 314–315 and 321–322.

  Isabelle representation: The separate locale uses a typed application operation and
  interprets object identity through Leibniz equivalence. It retains full-F syntax,
  typed-string signatures, and explicit de Bruijn coherence.

  Status: General-model interface and a Leibnizian specialization, not a quotient or
  completeness construction. Named-variable and primitive-signature translations
  remain separate.
\<close>

definition bacon_leibniz_equiv ::
    "(otype \<Rightarrow> 'v set) \<Rightarrow>
     (otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
     ('v \<Rightarrow> bool) \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "bacon_leibniz_equiv D papp v \<sigma> a b \<longleftrightarrow>
    (\<forall>f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop). v (papp \<sigma> f a) = v (papp \<sigma> f b))"

definition bacon_leibnizian ::
    "(otype \<Rightarrow> 'v set) \<Rightarrow>
     (otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow>
     ('v \<Rightarrow> bool) \<Rightarrow> bool" where
  "bacon_leibnizian D papp v \<longleftrightarrow>
    (\<forall>\<sigma> a b. a \<in> D \<sigma> \<longrightarrow> b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b)"

lemma bacon_leibniz_equiv_refl:
  "bacon_leibniz_equiv D papp v \<sigma> a a"
  by (simp add: bacon_leibniz_equiv_def)

lemma bacon_leibniz_equivD:
  assumes le: "bacon_leibniz_equiv D papp v \<sigma> a b"
    and f: "f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop)"
  shows "v (papp \<sigma> f a) = v (papp \<sigma> f b)"
proof -
  have all: "\<forall>f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop).
      v (papp \<sigma> f a) = v (papp \<sigma> f b)"
    using le unfolding bacon_leibniz_equiv_def .
  show ?thesis by (rule bspec[where x=f, OF all f])
qed

lemma bacon_leibniz_equiv_sym:
  assumes "bacon_leibniz_equiv D papp v \<sigma> a b"
  shows "bacon_leibniz_equiv D papp v \<sigma> b a"
proof (unfold bacon_leibniz_equiv_def, intro ballI)
  fix f
  assume f: "f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop)"
  have "v (papp \<sigma> f a) = v (papp \<sigma> f b)"
    by (rule bacon_leibniz_equivD[where f=f, OF assms f])
  then show "v (papp \<sigma> f b) = v (papp \<sigma> f a)" by (rule sym)
qed

lemma bacon_leibniz_equiv_trans:
  assumes "bacon_leibniz_equiv D papp v \<sigma> a b"
    and "bacon_leibniz_equiv D papp v \<sigma> b c"
  shows "bacon_leibniz_equiv D papp v \<sigma> a c"
proof (unfold bacon_leibniz_equiv_def, intro ballI)
  fix f
  assume f: "f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop)"
  have ab: "v (papp \<sigma> f a) = v (papp \<sigma> f b)"
    by (rule bacon_leibniz_equivD[where f=f, OF assms(1) f])
  have bc: "v (papp \<sigma> f b) = v (papp \<sigma> f c)"
    by (rule bacon_leibniz_equivD[where f=f, OF assms(2) f])
  show "v (papp \<sigma> f a) = v (papp \<sigma> f c)"
    by (rule trans[OF ab bc])
qed

lemma bacon_leibnizianD:
  assumes model: "bacon_leibnizian D papp v"
    and a: "a \<in> D \<sigma>" and b: "b \<in> D \<sigma>"
    and le: "bacon_leibniz_equiv D papp v \<sigma> a b"
  shows "a = b"
proof -
  have all: "\<forall>\<sigma> a b. a \<in> D \<sigma> \<longrightarrow> b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    using model unfolding bacon_leibnizian_def .
  have at_type: "\<forall>a b. a \<in> D \<sigma> \<longrightarrow> b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    by (rule spec[where x=\<sigma>, OF all])
  have at_left: "\<forall>b. a \<in> D \<sigma> \<longrightarrow> b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    by (rule spec[where x=a, OF at_type])
  have at_pair: "a \<in> D \<sigma> \<longrightarrow> b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    by (rule spec[where x=b, OF at_left])
  have left: "b \<in> D \<sigma> \<longrightarrow>
      bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    by (rule mp[OF at_pair a])
  have pair: "bacon_leibniz_equiv D papp v \<sigma> a b \<longrightarrow> a = b"
    by (rule mp[OF left b])
  show ?thesis by (rule mp[OF pair le])
qed

lemma bacon_leibnizian_iff_identity:
  assumes "bacon_leibnizian D papp v" and "a \<in> D \<sigma>" and "b \<in> D \<sigma>"
  shows "bacon_leibniz_equiv D papp v \<sigma> a b \<longleftrightarrow> a = b"
proof
  assume le: "bacon_leibniz_equiv D papp v \<sigma> a b"
  show "a = b" by (rule bacon_leibnizianD[OF assms le])
next
  assume eq: "a = b"
  have "bacon_leibniz_equiv D papp v \<sigma> a a"
    by (rule bacon_leibniz_equiv_refl)
  then show "bacon_leibniz_equiv D papp v \<sigma> a b"
    by (simp only: eq)
qed

section \<open>The separate general-model interface\<close>

text \<open>
  𝔐,g ⊨ M =σ N ⇔ ⟦M⟧g ≈ₗₑ ⟦N⟧g. Bacon, Definition 15.1, pp. 314–315; Definition 15.6,
  p. 322.

  Isabelle representation: bacon_general_model fixes typed application, whole-term
  interpretation, and logical truth conditions independently of bbk_model.

  Status: Actual equality is obtained only under the separately stated Leibnizian
  condition.
\<close>

locale bacon_general_model =
  fixes signature :: bbk_signature
    and domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool"
  assumes domain_nonempty: "domain \<sigma> \<noteq> {}"
    and app_type:
      "f \<in> domain (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow> a \<in> domain \<sigma> \<Longrightarrow>
       app \<sigma> \<tau> f a \<in> domain \<tau>"
    and denote_type:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> bbk_in_signature signature M \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g M \<in> domain \<sigma>"
    and denote_var:
      "lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       denote g (Var n) = g n"
    and denote_app:
      "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<Longrightarrow> \<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow>
       bbk_in_signature signature F \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       denote g (App F A) = app \<sigma> \<tau> (denote g F) (denote g A)"
    and denote_locality:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Delta> \<turnstile> M : \<sigma> \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> bbk_env_typed domain \<Delta> h \<Longrightarrow>
       (\<And>n. n \<in> bbk_fv M \<Longrightarrow> g n = h n) \<Longrightarrow>
       denote g M = denote h M"
    and denote_rename:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> bbk_in_signature signature M \<Longrightarrow>
       inj r \<Longrightarrow> bbk_env_typed domain \<Delta> g \<Longrightarrow>
       (\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Delta> (r n) = Some \<tau>) \<Longrightarrow>
       denote g (rename r M) = denote (\<lambda>n. g (r n)) M"
    and denote_beta_eta:
      "beta_eta_equiv \<Gamma> \<sigma> M N \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow> bbk_in_signature signature N \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow> denote g M = denote g N"
    and valuation_neg:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Neg A)) = (\<not> valuation (denote g A))"
    and valuation_conj:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Conj A B)) =
         (valuation (denote g A) \<and> valuation (denote g B))"
    and valuation_disj:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Disj A B)) =
         (valuation (denote g A) \<or> valuation (denote g B))"
    and valuation_imp:
      "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
       bbk_in_signature signature A \<Longrightarrow> bbk_in_signature signature B \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Imp A B)) =
         (valuation (denote g A) \<longrightarrow> valuation (denote g B))"
    and valuation_forall:
      "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Forall \<sigma> A)) =
         (\<forall>a \<in> domain \<sigma>. valuation (denote (bbk_extend a g) A))"
    and valuation_exists:
      "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Exists \<sigma> A)) =
         (\<exists>a \<in> domain \<sigma>. valuation (denote (bbk_extend a g) A))"
    and valuation_identity:
      "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow>
       bbk_in_signature signature M \<Longrightarrow> bbk_in_signature signature N \<Longrightarrow>
       bbk_env_typed domain \<Gamma> g \<Longrightarrow>
       valuation (denote g (Eq \<sigma> M N)) =
         bacon_leibniz_equiv domain (\<lambda>\<rho>. app \<rho> Prop) valuation \<sigma> (denote g M) (denote g N)"
begin

lemma general_identity_reflexive:
  assumes "\<Gamma> \<turnstile> M : \<sigma>" and "bbk_in_signature signature M"
    and "bbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (Eq \<sigma> M M))"
proof -
  have le: "bacon_leibniz_equiv domain (\<lambda>\<rho>. app \<rho> Prop) valuation \<sigma>
      (denote g M) (denote g M)"
    by (rule bacon_leibniz_equiv_refl)
  show ?thesis
    using le by (simp only: valuation_identity[OF assms(1,1,2,2,3)])
qed

lemma leibnizian_identity_actual:
  assumes model: "bacon_leibnizian domain (\<lambda>\<rho>. app \<rho> Prop) valuation"
    and M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>"
    and sigM: "bbk_in_signature signature M" and sigN: "bbk_in_signature signature N"
    and env: "bbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (Eq \<sigma> M N)) = (denote g M = denote g N)"
proof -
  have dm: "denote g M \<in> domain \<sigma>" using M sigM env by (rule denote_type)
  have dn: "denote g N \<in> domain \<sigma>" using N sigN env by (rule denote_type)
  have le: "bacon_leibniz_equiv domain (\<lambda>\<rho>. app \<rho> Prop) valuation \<sigma>
      (denote g M) (denote g N) \<longleftrightarrow> denote g M = denote g N"
    using model dm dn by (rule bacon_leibnizian_iff_identity)
  show ?thesis
    by (simp only: valuation_identity[OF M N sigM sigN env] le)
qed

end

section \<open>BBK models with represented predicate application are Leibnizian\<close>

text \<open>
  Fₐ = λxσ. x =σ a satisfies v(Fₐb) = 1 ⇔ b = a. Bacon–Dorr, Definition 3.1, pp.
  43–44. Bacon, Definition 15.6, p. 322.

  Isabelle representation: bbk_predicate_representation explicitly connects the
  predicate-application operation to whole-term evaluation. β conversion and BBK's
  actual-equality clause verify this test predicate.

  Status: Predicate separation and Leibnizianity are proved under that representation;
  no quotient or completeness theorem is assumed.
\<close>

locale bbk_predicate_representation =
  bbk_model signature domain denote valuation
  for signature :: bbk_signature
    and domain :: "otype \<Rightarrow> 'v set"
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> oterm \<Rightarrow> 'v"
    and valuation :: "'v \<Rightarrow> bool" +
  fixes papp :: "otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes papp_type:
    "f \<in> domain (\<sigma> \<rightarrow>\<^sub>o Prop) \<Longrightarrow> a \<in> domain \<sigma> \<Longrightarrow>
      papp \<sigma> f a \<in> domain Prop"
    and papp_represents:
    "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop \<Longrightarrow> \<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow>
      bbk_in_signature signature F \<Longrightarrow> bbk_in_signature signature A \<Longrightarrow>
      bbk_env_typed domain \<Gamma> g \<Longrightarrow>
      denote g (App F A) = papp \<sigma> (denote g F) (denote g A)"
begin

lemma bbk_equality_test_predicate:
  assumes a: "a \<in> domain \<sigma>" and b: "b \<in> domain \<sigma>"
  obtains f where "f \<in> domain (\<sigma> \<rightarrow>\<^sub>o Prop)"
    and "valuation (papp \<sigma> f a)"
    and "valuation (papp \<sigma> f b) = (b = a)"
proof -
  let ?g = "bbk_extend a (bbk_extend b (\<lambda>_. undefined))"
  let ?B = "Eq \<sigma> (Var 0) (Var 1)"
  let ?F = "Lam \<sigma> ?B"
  have env0: "bbk_env_typed domain [] (\<lambda>_. undefined)"
    by (rule bbk_env_empty)
  have env1: "bbk_env_typed domain [\<sigma>] (bbk_extend b (\<lambda>_. undefined))"
    by (rule bbk_env_extend[OF env0 b])
  have env: "bbk_env_typed domain [\<sigma>, \<sigma>] ?g"
    using env1 a by (rule bbk_env_extend)
  have x: "[\<sigma>, \<sigma>] \<turnstile> Var 0 : \<sigma>" by simp
  have y: "[\<sigma>, \<sigma>] \<turnstile> Var 1 : \<sigma>"
    by (simp add: lookup_def)
  have B: "\<sigma> # [\<sigma>, \<sigma>] \<turnstile> ?B : Prop"
    by (intro has_type.Eq has_type.Var) (simp_all add: lookup_def)
  have F: "[\<sigma>, \<sigma>] \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using B by (rule has_type.Lam)
  have sigF: "bbk_in_signature signature ?F" by simp
  have sigx: "bbk_in_signature signature (Var 0)" by simp
  have sigy: "bbk_in_signature signature (Var 1)" by simp
  have fa: "denote ?g (Var 0) = a"
  proof -
    have look: "lookup [\<sigma>, \<sigma>] 0 = Some \<sigma>" by simp
    have den: "denote ?g (Var 0) = ?g 0" by (rule denote_var[OF look env])
    show ?thesis by (simp only: den bbk_extend_zero)
  qed
  have fb: "denote ?g (Var 1) = b"
  proof -
    have look: "lookup [\<sigma>, \<sigma>] (Suc 0) = Some \<sigma>"
      by (simp only: lookup_Cons_Suc lookup_Cons_0)
    have den: "denote ?g (Var (Suc 0)) = ?g (Suc 0)"
      by (rule denote_var[OF look env])
    have g_value: "?g (Suc 0) = b"
      by (simp only: bbk_extend_Suc bbk_extend_zero)
    have result: "denote ?g (Var (Suc 0)) = b"
      by (rule trans[OF den g_value])
    show ?thesis using result by (simp only: One_nat_def)
  qed
  have fdom: "denote ?g ?F \<in> domain (\<sigma> \<rightarrow>\<^sub>o Prop)"
    using F sigF env by (rule denote_type)
  have appa: "denote ?g (App ?F (Var 0)) = papp \<sigma> (denote ?g ?F) a"
    by (simp only: papp_represents[OF F x sigF sigx env] fa)
  have appb: "denote ?g (App ?F (Var 1)) = papp \<sigma> (denote ?g ?F) b"
    by (simp only: papp_represents[OF F y sigF sigy env] fb)
  have sig_red_a: "bbk_in_signature signature (App ?F (Var 0))" by simp
  have sig_red_b: "bbk_in_signature signature (App ?F (Var 1))" by simp
  have sig_con_a: "bbk_in_signature signature (subst0 (Var 0) ?B)"
    by (simp add: subst0_def)
  have sig_con_b: "bbk_in_signature signature (subst0 (Var 1) ?B)"
    by (simp add: subst0_def)
  have beta_a: "denote ?g (App ?F (Var 0)) = denote ?g (Eq \<sigma> (Var 0) (Var 0))"
    using bbk_denote_beta[OF B x sig_red_a sig_con_a env] by (simp add: subst0_def)
  have beta_b: "denote ?g (App ?F (Var 1)) = denote ?g (Eq \<sigma> (Var 1) (Var 0))"
    using bbk_denote_beta[OF B y sig_red_b sig_con_b env] by (simp add: subst0_def)
  have true_a: "valuation (papp \<sigma> (denote ?g ?F) a)"
  proof -
    have same: "papp \<sigma> (denote ?g ?F) a = denote ?g (Eq \<sigma> (Var 0) (Var 0))"
      by (rule trans[OF appa[symmetric] beta_a])
    show ?thesis by (simp only: same valuation_identity[OF x x sigx sigx env])
  qed
  have test_b: "valuation (papp \<sigma> (denote ?g ?F) b) = (b = a)"
  proof -
    have same: "papp \<sigma> (denote ?g ?F) b = denote ?g (Eq \<sigma> (Var 1) (Var 0))"
      by (rule trans[OF appb[symmetric] beta_b])
    show ?thesis by (simp only: same valuation_identity[OF y x sigy sigx env] fa fb)
  qed
  show thesis using that[OF fdom true_a test_b] .
qed

theorem represented_BBK_is_leibnizian:
  "bacon_leibnizian domain papp valuation"
proof (unfold bacon_leibnizian_def, intro allI impI)
  fix \<sigma> a b
  assume a: "a \<in> domain \<sigma>" and b: "b \<in> domain \<sigma>"
    and le: "bacon_leibniz_equiv domain papp valuation \<sigma> a b"
  obtain f where f: "f \<in> domain (\<sigma> \<rightarrow>\<^sub>o Prop)"
    and ta: "valuation (papp \<sigma> f a)"
    and tb: "valuation (papp \<sigma> f b) = (b = a)"
    by (rule bbk_equality_test_predicate[where \<sigma>=\<sigma> and a=a and b=b, OF a b])
  have same: "valuation (papp \<sigma> f a) = valuation (papp \<sigma> f b)"
    by (rule bacon_leibniz_equivD[where f=f, OF le f])
  have true_b: "valuation (papp \<sigma> f b)"
    using ta by (simp only: same)
  have "b = a" using true_b by (simp only: tb)
  then show "a = b" by (rule sym)
qed

end

end
