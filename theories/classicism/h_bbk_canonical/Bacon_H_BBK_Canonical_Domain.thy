theory Bacon_H_BBK_Canonical_Domain
  imports Bacon_H_Henkin_Substitution_Development.Bacon_H_Henkin_Substitution
begin

section \<open>Tagged domains and interpretation by closed representatives\<close>

text \<open>
  Dσ = {[M]ₜ : M is closed of type σ}, and ⟦M⟧g = [M[s]]ₜ when s chooses
  representatives of g. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp.
  320–321.

  Isabelle representation: Each HOL value is a pair consisting of an object type and a
  class of closed terms. The type tag separates domains; H_BBK_den substitutes
  representatives into the whole term.

  Status: Domain and application construction only in this file; later files supply
  truth and the BBK interpretation.
\<close>

type_synonym h_bbk_value = "otype \<times> oterm set"

context H_closed_Henkin
begin

definition H_BBK_class :: "otype \<Rightarrow> oterm \<Rightarrow> h_bbk_value" where
  "H_BBK_class \<sigma> M = (\<sigma>, H_term_class \<sigma> M)"

definition H_BBK_domain :: "otype \<Rightarrow> h_bbk_value set" where
  "H_BBK_domain \<sigma> = {H_BBK_class \<sigma> M |M. [] \<turnstile> M : \<sigma>}"

definition H_BBK_rep :: "h_bbk_value \<Rightarrow> oterm" where
  "H_BBK_rep v = (SOME M. M \<in> snd v)"

lemma H_BBK_class_in_domain:
  "[] \<turnstile> M : \<sigma> \<Longrightarrow> H_BBK_class \<sigma> M \<in> H_BBK_domain \<sigma>"
  unfolding H_BBK_domain_def by blast

lemma H_BBK_domain_representation:
  assumes "v \<in> H_BBK_domain \<sigma>"
  obtains M where "[] \<turnstile> M : \<sigma>" and "v = H_BBK_class \<sigma> M"
  using assms unfolding H_BBK_domain_def by blast

lemma H_BBK_domain_tag:
  "v \<in> H_BBK_domain \<sigma> \<Longrightarrow> fst v = \<sigma>"
  unfolding H_BBK_domain_def H_BBK_class_def by auto

lemma H_BBK_domain_disjoint:
  assumes "\<sigma> \<noteq> \<tau>"
  shows "H_BBK_domain \<sigma> \<inter> H_BBK_domain \<tau> = {}"
  using assms H_BBK_domain_tag by blast

lemma H_BBK_domain_nonempty:
  "H_BBK_domain \<sigma> \<noteq> {}"
proof -
  have typed: "[] \<turnstile> Const '''' \<sigma> : \<sigma>" by (rule has_type.Const)
  have "H_BBK_class \<sigma> (Const '''' \<sigma>) \<in> H_BBK_domain \<sigma>"
    by (rule H_BBK_class_in_domain[OF typed])
  then show ?thesis by blast
qed

lemma H_BBK_rep_member:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_rep v \<in> snd v"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>" and v: "v = H_BBK_class \<sigma> M"
    by (rule H_BBK_domain_representation[OF domain])
  have member: "M \<in> snd v"
    using H_term_class_self[OF typed] by (simp only: v H_BBK_class_def snd_conv)
  have inhabited: "\<exists>M. M \<in> snd v"
    by (rule exI[where x=M and P="\<lambda>N. N \<in> snd v"]) (rule member)
  show ?thesis unfolding H_BBK_rep_def by (rule someI_ex[OF inhabited])
qed

lemma H_BBK_rep_type:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "[] \<turnstile> H_BBK_rep v : \<sigma>"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>" and v: "v = H_BBK_class \<sigma> M"
    by (rule H_BBK_domain_representation[OF domain])
  have member: "H_BBK_rep v \<in> snd v" by (rule H_BBK_rep_member[OF domain])
  have eq: "H_term_eq \<sigma> M (H_BBK_rep v)"
    using member by (simp only: v H_BBK_class_def snd_conv H_term_class_def mem_Collect_eq)
  show ?thesis using H_term_eq_types[OF eq] by blast
qed

lemma H_BBK_class_eq_iff:
  assumes M_type: "[] \<turnstile> M : \<sigma>" and N_type: "[] \<turnstile> N : \<sigma>"
  shows "H_BBK_class \<sigma> M = H_BBK_class \<sigma> N \<longleftrightarrow> H_term_eq \<sigma> M N"
  by (simp add: H_BBK_class_def H_term_class_eq_iff[OF M_type N_type])

lemma H_BBK_rep_reconstruct:
  assumes domain: "v \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_class \<sigma> (H_BBK_rep v) = v"
proof -
  obtain M where typed: "[] \<turnstile> M : \<sigma>" and v: "v = H_BBK_class \<sigma> M"
    by (rule H_BBK_domain_representation[OF domain])
  have rep_type: "[] \<turnstile> H_BBK_rep v : \<sigma>" by (rule H_BBK_rep_type[OF domain])
  have member: "H_BBK_rep v \<in> snd v" by (rule H_BBK_rep_member[OF domain])
  have eq: "H_term_eq \<sigma> M (H_BBK_rep v)"
    using member by (simp only: v H_BBK_class_def snd_conv H_term_class_def mem_Collect_eq)
  have "H_BBK_class \<sigma> M = H_BBK_class \<sigma> (H_BBK_rep v)"
    using H_BBK_class_eq_iff[OF typed rep_type] eq by blast
  then show ?thesis using v by simp
qed

lemma H_BBK_rep_class_eq:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "H_term_eq \<sigma> (H_BBK_rep (H_BBK_class \<sigma> M)) M"
proof -
  have domain: "H_BBK_class \<sigma> M \<in> H_BBK_domain \<sigma>"
    by (rule H_BBK_class_in_domain[OF typed])
  have rep_type: "[] \<turnstile> H_BBK_rep (H_BBK_class \<sigma> M) : \<sigma>"
    by (rule H_BBK_rep_type[OF domain])
  show ?thesis
    using H_BBK_class_eq_iff[OF rep_type typed] H_BBK_rep_reconstruct[OF domain] by blast
qed

subsection \<open>Typed environments and substitution of representatives\<close>

text \<open>
  g(x) ∈ Dσ ⇒ rep(g(x)) : σ; thus a typed assignment yields a closed substitution.
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: H_BBK_env_typed records membership for context slots, and
  H_BBK_rep selects one representative from each typed class.

  Status: Representative choices remain guarded by domain membership; no claim is made
  about arbitrary ambient sets.
\<close>

definition H_BBK_env_typed :: "ctx \<Rightarrow> (nat \<Rightarrow> h_bbk_value) \<Rightarrow> bool" where
  "H_BBK_env_typed \<Gamma> \<rho> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow> \<rho> n \<in> H_BBK_domain \<sigma>)"

lemma H_BBK_env_lookup:
  assumes "H_BBK_env_typed \<Gamma> \<rho>" and "lookup \<Gamma> n = Some \<sigma>"
  shows "\<rho> n \<in> H_BBK_domain \<sigma>"
  using assms unfolding H_BBK_env_typed_def by blast

lemma H_BBK_rep_substitution_typed:
  assumes env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "term_subst_typed \<Gamma> [] (\<lambda>n. H_BBK_rep (\<rho> n))"
proof (unfold term_subst_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have domain: "\<rho> n \<in> H_BBK_domain \<sigma>" by (rule H_BBK_env_lookup[OF env lookup])
  show "[] \<turnstile> H_BBK_rep (\<rho> n) : \<sigma>" by (rule H_BBK_rep_type[OF domain])
qed

lemma H_BBK_substitution_independent:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and s_typed: "term_subst_typed \<Gamma> [] s"
    and r_typed: "term_subst_typed \<Gamma> [] r"
    and same: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_BBK_class \<sigma> (s n) = H_BBK_class \<sigma> (r n)"
  shows "H_BBK_class \<tau> (subst s M) = H_BBK_class \<tau> (subst r M)"
proof -
  have pointwise: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> H_term_eq \<sigma> (s n) (r n)"
  proof -
    fix n \<sigma>
    assume lookup: "lookup \<Gamma> n = Some \<sigma>"
    have left: "[] \<turnstile> s n : \<sigma>" by (rule term_subst_typedD[OF s_typed lookup])
    have right: "[] \<turnstile> r n : \<sigma>" by (rule term_subst_typedD[OF r_typed lookup])
    show "H_term_eq \<sigma> (s n) (r n)"
      using H_BBK_class_eq_iff[OF left right] same[OF lookup] by blast
  qed
  have classes: "H_term_class \<tau> (subst s M) = H_term_class \<tau> (subst r M)"
    by (rule H_term_class_subst_cong[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau>
          and s=s and r=r, OF typed s_typed r_typed pointwise])
  show ?thesis by (simp only: H_BBK_class_def classes)
qed

subsection \<open>Whole-term interpretation\<close>

text \<open>
  ⟦M⟧g = [M[rep ∘ g]]ₜ. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp.
  320–321.

  Isabelle representation: H_BBK_den uses infer_type to recover the class tag. For a
  typed term the next lemma replaces the partial selector the by its known type.

  Status: The total HOL function has intended meaning only on typed inputs.
\<close>

definition H_BBK_den :: "ctx \<Rightarrow> (nat \<Rightarrow> h_bbk_value) \<Rightarrow> oterm \<Rightarrow> h_bbk_value" where
  "H_BBK_den \<Gamma> \<rho> M =
    H_BBK_class (the (infer_type \<Gamma> M)) (subst (\<lambda>n. H_BBK_rep (\<rho> n)) M)"

text \<open>
  The total function has no intended meaning on ill-typed inputs.  On a
  term of type \<open>\<tau>\<close>, type inference returns precisely \<open>Some \<tau>\<close>.
  The lemma below therefore removes \<open>the\<close> from every typed use.
\<close>

lemma H_BBK_den_typed_form:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
  shows "H_BBK_den \<Gamma> \<rho> M = H_BBK_class \<tau> (subst (\<lambda>n. H_BBK_rep (\<rho> n)) M)"
  using infer_type_complete[OF typed] by (simp add: H_BBK_den_def)

lemma H_BBK_den_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_den \<Gamma> \<rho> M \<in> H_BBK_domain \<tau>"
proof -
  have st: "term_subst_typed \<Gamma> [] (\<lambda>n. H_BBK_rep (\<rho> n))"
    by (rule H_BBK_rep_substitution_typed[OF env])
  have result: "[] \<turnstile> subst (\<lambda>n. H_BBK_rep (\<rho> n)) M : \<tau>"
    by (rule term_subst_preserves_typing[OF typed st])
  show ?thesis
    using H_BBK_class_in_domain[OF result] by (simp only: H_BBK_den_typed_form[OF typed])
qed

lemma H_BBK_den_representatives:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>" and env: "H_BBK_env_typed \<Gamma> \<rho>"
    and s_typed: "term_subst_typed \<Gamma> [] s"
    and represents: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_BBK_class \<sigma> (s n) = \<rho> n"
  shows "H_BBK_den \<Gamma> \<rho> M = H_BBK_class \<tau> (subst s M)"
proof -
  let ?r = "\<lambda>n. H_BBK_rep (\<rho> n)"
  have r_typed: "term_subst_typed \<Gamma> [] ?r" by (rule H_BBK_rep_substitution_typed[OF env])
  have same: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_BBK_class \<sigma> (?r n) = H_BBK_class \<sigma> (s n)"
  proof -
    fix n \<sigma>
    assume lookup: "lookup \<Gamma> n = Some \<sigma>"
    have domain: "\<rho> n \<in> H_BBK_domain \<sigma>" by (rule H_BBK_env_lookup[OF env lookup])
    show "H_BBK_class \<sigma> (?r n) = H_BBK_class \<sigma> (s n)"
      using H_BBK_rep_reconstruct[OF domain] represents[OF lookup] by simp
  qed
  have eq: "H_BBK_class \<tau> (subst ?r M) = H_BBK_class \<tau> (subst s M)"
    by (rule H_BBK_substitution_independent[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau>
          and s="?r" and r=s, OF typed r_typed s_typed same])
  show ?thesis using eq by (simp only: H_BBK_den_typed_form[OF typed])
qed

lemma H_BBK_den_Var:
  assumes lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_den \<Gamma> \<rho> (Var n) = \<rho> n"
proof -
  have typed: "\<Gamma> \<turnstile> Var n : \<sigma>" by (rule has_type.Var[OF lookup])
  have domain: "\<rho> n \<in> H_BBK_domain \<sigma>" by (rule H_BBK_env_lookup[OF env lookup])
  show ?thesis by (simp only: H_BBK_den_typed_form[OF typed] subst.simps H_BBK_rep_reconstruct[OF domain])
qed

lemma H_BBK_den_closed:
  assumes typed: "[] \<turnstile> M : \<tau>"
  shows "H_BBK_den [] \<rho> M = H_BBK_class \<tau> M"
  by (simp only: H_BBK_den_typed_form[OF typed] H_closed_substitution_identity[OF typed])

lemma H_BBK_den_Const:
  "H_BBK_den \<Gamma> \<rho> (Const c \<sigma>) = H_BBK_class \<sigma> (Const c \<sigma>)"
proof -
  have typed: "\<Gamma> \<turnstile> Const c \<sigma> : \<sigma>" by (rule has_type.Const)
  show ?thesis by (simp only: H_BBK_den_typed_form[OF typed] subst.simps)
qed

lemma H_BBK_den_context_agreement:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and same: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow> \<rho> n = \<eta> n"
  shows "H_BBK_den \<Gamma> \<rho> M = H_BBK_den \<Gamma> \<eta> M"
proof -
  have reps: "\<And>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<Longrightarrow>
      H_BBK_rep (\<rho> n) = H_BBK_rep (\<eta> n)"
  proof -
    fix n \<sigma>
    assume lookup: "lookup \<Gamma> n = Some \<sigma>"
    show "H_BBK_rep (\<rho> n) = H_BBK_rep (\<eta> n)"
      by (simp only: same[OF lookup])
  qed
  have equal: "subst (\<lambda>n. H_BBK_rep (\<rho> n)) M = subst (\<lambda>n. H_BBK_rep (\<eta> n)) M"
    by (rule H_substitution_agreement[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau>
          and s="\<lambda>n. H_BBK_rep (\<rho> n)" and r="\<lambda>n. H_BBK_rep (\<eta> n)", OF typed reps])
  show ?thesis by (simp only: H_BBK_den_typed_form[OF typed] equal)
qed

subsection \<open>Application on the identity classes\<close>

text \<open>
  [F]ₜ · [A]ₜ = [FA]ₜ. Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp.
  320–321.

  Isabelle representation: H_BBK_app applies chosen closed representatives and returns
  their tagged result class; earlier congruence makes that choice immaterial.

  Status: Typed application is closed; no arbitrary-function abstraction operation is
  postulated.
\<close>

definition H_BBK_app :: "otype \<Rightarrow> otype \<Rightarrow> h_bbk_value \<Rightarrow> h_bbk_value \<Rightarrow> h_bbk_value" where
  "H_BBK_app \<sigma> \<tau> f x = H_BBK_class \<tau> (App (H_BBK_rep f) (H_BBK_rep x))"

lemma H_BBK_app_type:
  assumes f: "f \<in> H_BBK_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and x: "x \<in> H_BBK_domain \<sigma>"
  shows "H_BBK_app \<sigma> \<tau> f x \<in> H_BBK_domain \<tau>"
proof -
  have ft: "[] \<turnstile> H_BBK_rep f : \<sigma> \<rightarrow>\<^sub>o \<tau>" by (rule H_BBK_rep_type[OF f])
  have xt: "[] \<turnstile> H_BBK_rep x : \<sigma>" by (rule H_BBK_rep_type[OF x])
  have app_typed: "[] \<turnstile> App (H_BBK_rep f) (H_BBK_rep x) : \<tau>" by (rule has_type.App[OF ft xt])
  show ?thesis unfolding H_BBK_app_def by (rule H_BBK_class_in_domain[OF app_typed])
qed

lemma H_BBK_app_classes:
  assumes F: "[] \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and M: "[] \<turnstile> M : \<sigma>"
  shows "H_BBK_app \<sigma> \<tau> (H_BBK_class (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (H_BBK_class \<sigma> M) =
    H_BBK_class \<tau> (App F M)"
proof -
  let ?f = "H_BBK_rep (H_BBK_class (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)"
  let ?m = "H_BBK_rep (H_BBK_class \<sigma> M)"
  have fe: "H_term_eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) ?f F" by (rule H_BBK_rep_class_eq[OF F])
  have me: "H_term_eq \<sigma> ?m M" by (rule H_BBK_rep_class_eq[OF M])
  have ae: "H_term_eq \<tau> (App ?f ?m) (App F M)" by (rule H_term_eq_app_cong[OF fe me])
  have left: "[] \<turnstile> App ?f ?m : \<tau>" and right: "[] \<turnstile> App F M : \<tau>"
    using H_term_eq_types[OF ae] by blast+
  have "H_BBK_class \<tau> (App ?f ?m) = H_BBK_class \<tau> (App F M)"
    using H_BBK_class_eq_iff[OF left right] ae by blast
  then show ?thesis by (simp only: H_BBK_app_def)
qed

lemma H_BBK_den_App:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and M: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "H_BBK_env_typed \<Gamma> \<rho>"
  shows "H_BBK_den \<Gamma> \<rho> (App F M) = H_BBK_app \<sigma> \<tau> (H_BBK_den \<Gamma> \<rho> F) (H_BBK_den \<Gamma> \<rho> M)"
proof -
  let ?s = "\<lambda>n. H_BBK_rep (\<rho> n)"
  have st: "term_subst_typed \<Gamma> [] ?s" by (rule H_BBK_rep_substitution_typed[OF env])
  have ft: "[] \<turnstile> subst ?s F : \<sigma> \<rightarrow>\<^sub>o \<tau>" by (rule term_subst_preserves_typing[OF F st])
  have mt: "[] \<turnstile> subst ?s M : \<sigma>" by (rule term_subst_preserves_typing[OF M st])
  have app_typed: "\<Gamma> \<turnstile> App F M : \<tau>" by (rule has_type.App[OF F M])
  show ?thesis
    by (simp only: H_BBK_den_typed_form[OF app_typed] H_BBK_den_typed_form[OF F]
          H_BBK_den_typed_form[OF M] subst.simps H_BBK_app_classes[OF ft mt])
qed

text \<open>
  Domain nonemptiness uses the existing unrestricted typed constant stock.
  Nothing here supplies fresh constants for an arbitrary initial theory in
  a specified smaller signature.  That language-extension obligation and
  the remaining BBK truth conditions are not consequences of this domain
  construction alone.
\<close>

end
end
