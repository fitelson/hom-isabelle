theory Bacon_Parametric_Canonical_Domain
  imports Bacon_Parametric_Canonical_Substitution
begin

section \<open>Canonical domains over an arbitrary name carrier\<close>

text \<open>
  Dσ consists of the identity classes [M]ₜ of closed terms M:σ in ℒ(Σ).
  Since ⊢H ∃x:σ.(x =σ x), Henkin witness completeness supplies an
  in-signature closed representative of every type, even when Σ has no
  primitive constant at that type.  Source: Bacon–Dorr Theorem 3.2,
  p.45 n.64; Bacon, Theorem 15.3, pp.320–321.

  Isabelle representation.  Each class is tagged by σ, giving a common
  carrier of pairs of types and sets of parametric terms.  An assignment
  is interpreted by simultaneous substitution of chosen representatives.
  The construction is conditional on pH_closed_Henkin; it does not prove
  existence of a Henkin theory or a semantic model.  There is no name
  enumeration, assumed stock of denoting constants, or Functionality.
\<close>

type_synonym 'c pHc_value = "otype \<times> 'c pterm set"

lemma pHc_typing_unique:
  fixes M :: "'c pterm"
  assumes first: "has_ptype \<Gamma> M \<sigma>" and second: "has_ptype \<Gamma> M \<tau>"
  shows "\<sigma> = \<tau>"
proof -
  let ?erase = "\<lambda>_ :: 'c. ('''' :: string)"
  let ?M = "pterm_to_oterm (phenkin_map ?erase M)"
  have left: "\<Gamma> \<turnstile> ?M : \<sigma>"
    by (rule pterm_to_preserves_typing[OF phenkin_map_type[where k="?erase", OF first]])
  have right: "\<Gamma> \<turnstile> ?M : \<tau>"
    by (rule pterm_to_preserves_typing[OF phenkin_map_type[where k="?erase", OF second]])
  show ?thesis by (rule typing_unique[OF left right])
qed

text \<open>
  Type uniqueness above uses a name-erasing syntax map solely to reuse the
  existing type-uniqueness proof.  It does not identify constant denotations
  or encode the signature injectively into strings.  The semantic carrier
  below retains the original arbitrary names.
\<close>

definition pHc_type_of :: "'c pterm \<Rightarrow> otype" where
  "pHc_type_of M = (SOME \<sigma>. has_ptype [] M \<sigma>)"

lemma pHc_type_of_typed:
  assumes typed: "has_ptype [] M \<tau>"
  shows "pHc_type_of M = \<tau>"
proof -
  have inhabited: "\<exists>\<sigma>. has_ptype [] M \<sigma>" by (rule exI[where x=\<tau>]) (rule typed)
  have selected: "has_ptype [] M (pHc_type_of M)"
    unfolding pHc_type_of_def by (rule someI_ex[OF inhabited])
  show ?thesis by (rule pHc_typing_unique[OF selected typed])
qed

context pH_closed_Henkin
begin

lemma pHc_closed_inhabited:
  "\<exists>M. pterm_in_language signature [] M \<sigma>"
proof -
  let ?A = "PEq \<sigma> (PVar 0) (PVar 0)"
  have zero: "has_ptype [\<sigma>] (PVar 0) \<sigma>" by (rule has_ptype.PVar) simp
  have body_type: "has_ptype [\<sigma>] ?A Prop" by (rule has_ptype.PEq[OF zero zero])
  have body_sig: "pterm_in_signature signature ?A" by simp
  have body: "pterm_in_language signature [\<sigma>] ?A Prop"
    unfolding pterm_in_language_def by (rule conjI[OF body_type body_sig])
  have existence: "PExists \<sigma> ?A \<in> T" by (rule pH_theorem_member[OF pH_all_type_existence])
  have witnessed: "pH_Henkin_witnessed signature [] T"
    using henkin unfolding pH_Henkin_theory_def by (rule conjunct2)
  have clause: "pterm_in_language signature [\<sigma>] ?A Prop \<longrightarrow> PExists \<sigma> ?A \<in> T \<longrightarrow>
      (\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst0 W ?A \<in> T)"
    using witnessed unfolding pH_Henkin_witnessed_def by (elim allE) assumption
  have witnesses: "\<exists>W. pterm_in_language signature [] W \<sigma> \<and> psubst0 W ?A \<in> T"
    by (rule mp[OF mp[OF clause body] existence])
  show ?thesis using witnesses by blast
qed

definition pHc_class :: "otype \<Rightarrow> 'c pterm \<Rightarrow> 'c pHc_value" where
  "pHc_class \<sigma> M = (\<sigma>, pH_term_class \<sigma> M)"

definition pHc_domain :: "otype \<Rightarrow> 'c pHc_value set" where
  "pHc_domain \<sigma> = {pHc_class \<sigma> M |M. pterm_in_language signature [] M \<sigma>}"

definition pHc_rep :: "'c pHc_value \<Rightarrow> 'c pterm" where
  "pHc_rep v = (SOME M. M \<in> snd v)"

text \<open>
  The selectors are total HOL functions, but their off-domain values have
  no intended meaning.  Representative lemmas require membership in Dσ;
  interpretation lemmas require typing, signature membership, and a typed
  assignment.  These guards supply the necessary witnesses for each choice.
\<close>

lemma pHc_class_in_domain:
  "pterm_in_language signature [] M \<sigma> \<Longrightarrow> pHc_class \<sigma> M \<in> pHc_domain \<sigma>"
  unfolding pHc_domain_def by blast

lemma pHc_domain_representation:
  assumes "v \<in> pHc_domain \<sigma>"
  obtains M where "pterm_in_language signature [] M \<sigma>" and "v = pHc_class \<sigma> M"
  using assms unfolding pHc_domain_def by blast

lemma pHc_domain_nonempty:
  "pHc_domain \<sigma> \<noteq> {}"
proof -
  obtain M where lang: "pterm_in_language signature [] M \<sigma>" using pHc_closed_inhabited[of \<sigma>] by blast
  have "pHc_class \<sigma> M \<in> pHc_domain \<sigma>" by (rule pHc_class_in_domain[OF lang])
  then show ?thesis by blast
qed

lemma pHc_domain_tag:
  "v \<in> pHc_domain \<sigma> \<Longrightarrow> fst v = \<sigma>"
  unfolding pHc_domain_def pHc_class_def by auto

lemma pHc_domain_disjoint:
  "\<sigma> \<noteq> \<tau> \<Longrightarrow> pHc_domain \<sigma> \<inter> pHc_domain \<tau> = {}"
  using pHc_domain_tag by blast

lemma pHc_class_eq_iff:
  assumes M: "pterm_in_language signature [] M \<sigma>" and N: "pterm_in_language signature [] N \<sigma>"
  shows "pHc_class \<sigma> M = pHc_class \<sigma> N \<longleftrightarrow> pH_term_eq \<sigma> M N"
  by (simp add: pHc_class_def pH_term_class_eq_iff[OF M N])

lemma pHc_rep_member:
  assumes domain: "v \<in> pHc_domain \<sigma>"
  shows "pHc_rep v \<in> snd v"
proof -
  obtain M where lang: "pterm_in_language signature [] M \<sigma>" and v: "v = pHc_class \<sigma> M"
    by (rule pHc_domain_representation[OF domain])
  have self: "pH_term_eq \<sigma> M M" by (rule pH_term_eq_refl[OF lang])
  have member: "M \<in> snd v" using self by (simp add: v pHc_class_def pH_term_class_def)
  have inhabited: "\<exists>M. M \<in> snd v" by (rule exI[where x=M]) (rule member)
  show ?thesis unfolding pHc_rep_def by (rule someI_ex[OF inhabited])
qed

lemma pHc_rep_language:
  assumes domain: "v \<in> pHc_domain \<sigma>"
  shows "pterm_in_language signature [] (pHc_rep v) \<sigma>"
proof -
  obtain M where lang: "pterm_in_language signature [] M \<sigma>" and v: "v = pHc_class \<sigma> M"
    by (rule pHc_domain_representation[OF domain])
  have member: "pHc_rep v \<in> snd v" by (rule pHc_rep_member[OF domain])
  have eq: "pH_term_eq \<sigma> M (pHc_rep v)" using member
    by (simp only: v pHc_class_def snd_conv pH_term_class_def mem_Collect_eq)
  show ?thesis by (rule pH_term_eq_right[OF eq])
qed

lemma pHc_rep_reconstruct:
  assumes domain: "v \<in> pHc_domain \<sigma>"
  shows "pHc_class \<sigma> (pHc_rep v) = v"
proof -
  obtain M where lang: "pterm_in_language signature [] M \<sigma>" and v: "v = pHc_class \<sigma> M"
    by (rule pHc_domain_representation[OF domain])
  have rep_lang: "pterm_in_language signature [] (pHc_rep v) \<sigma>" by (rule pHc_rep_language[OF domain])
  have member: "pHc_rep v \<in> snd v" by (rule pHc_rep_member[OF domain])
  have eq: "pH_term_eq \<sigma> M (pHc_rep v)" using member
    by (simp only: v pHc_class_def snd_conv pH_term_class_def mem_Collect_eq)
  have classes: "pHc_class \<sigma> M = pHc_class \<sigma> (pHc_rep v)"
    by (rule iffD2[OF pHc_class_eq_iff[OF lang rep_lang] eq])
  show ?thesis using classes v by simp
qed

lemma pHc_rep_class_eq:
  assumes lang: "pterm_in_language signature [] M \<sigma>"
  shows "pH_term_eq \<sigma> (pHc_rep (pHc_class \<sigma> M)) M"
proof -
  have domain: "pHc_class \<sigma> M \<in> pHc_domain \<sigma>" by (rule pHc_class_in_domain[OF lang])
  have rep_lang: "pterm_in_language signature [] (pHc_rep (pHc_class \<sigma> M)) \<sigma>"
    by (rule pHc_rep_language[OF domain])
  show ?thesis by (rule iffD1[OF pHc_class_eq_iff[OF rep_lang lang] pHc_rep_reconstruct[OF domain]])
qed

subsection \<open>Simultaneous substitution and interpretation\<close>

text \<open>
  If g(x) = [s(x)]ₜ, then ⟦M⟧g = [M[s]]ₜ.  The value does not
  depend on the representative selected at each context slot.  The finite
  variable context does not restrict the cardinality of the signature.
  Source: Bacon–Dorr p.45 n.64, definition of the canonical interpretation.
\<close>

lemma pHc_env_rep:
  assumes env: "pbbk_env_typed pHc_domain \<Gamma> g" and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "pterm_in_language signature [] (pHc_rep (g n)) \<sigma>"
  by (rule pHc_rep_language[OF pbbk_env_lookup[OF env lookup]])

lemma pHc_closed_instance_language:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pterm_in_language signature [] (psubst (\<lambda>n. pHc_rep (g n)) M) \<tau>"
  by (rule pHcs_subst_language[OF typed sig]) (rule pHc_env_rep[OF env])

definition pHc_denote :: "(nat \<Rightarrow> 'c pHc_value) \<Rightarrow> 'c pterm \<Rightarrow> 'c pHc_value" where
  "pHc_denote g M = (let N = psubst (\<lambda>n. pHc_rep (g n)) M in pHc_class (pHc_type_of N) N)"

lemma pHc_denote_typed_form:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M = pHc_class \<tau> (psubst (\<lambda>n. pHc_rep (g n)) M)"
proof -
  have lang: "pterm_in_language signature [] (psubst (\<lambda>n. pHc_rep (g n)) M) \<tau>"
    by (rule pHc_closed_instance_language[OF typed sig env])
  have closed: "has_ptype [] (psubst (\<lambda>n. pHc_rep (g n)) M) \<tau>"
    using lang unfolding pterm_in_language_def by (rule conjunct1)
  show ?thesis by (simp add: pHc_denote_def pHc_type_of_typed[OF closed])
qed

lemma pHc_denote_type:
  assumes "has_ptype \<Gamma> M \<tau>" and "pterm_in_signature signature M" and "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g M \<in> pHc_domain \<tau>"
  using pHc_class_in_domain[OF pHc_closed_instance_language[OF assms]]
  by (simp only: pHc_denote_typed_form[OF assms])

lemma pHc_subst_class_eq:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and agree: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pH_term_eq \<rho> (s n) (r n)"
  shows "pHc_class \<tau> (psubst s M) = pHc_class \<tau> (psubst r M)"
proof -
  have classes: "pH_term_class \<tau> (psubst s M) = pH_term_class \<tau> (psubst r M)"
    by (rule pHcs_representative_independence[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau> and s=s and r=r,
          OF typed sig agree])
  show ?thesis unfolding pHc_class_def by (rule arg_cong[where f="\<lambda>C. (\<tau>, C)", OF classes])
qed

lemma pHc_denote_representatives:
  assumes typed: "has_ptype \<Gamma> M \<tau>" and sig: "pterm_in_signature signature M"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
    and sub: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pterm_in_language signature [] (s n) \<rho>"
    and represents: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> pHc_class \<rho> (s n) = g n"
  shows "pHc_denote g M = pHc_class \<tau> (psubst s M)"
proof -
  have agree: "pH_term_eq \<rho> (pHc_rep (g n)) (s n)"
    if lookup: "lookup \<Gamma> n = Some \<rho>" for n \<rho>
  proof -
    have domain: "g n \<in> pHc_domain \<rho>" by (rule pbbk_env_lookup[OF env lookup])
    have rep_lang: "pterm_in_language signature [] (pHc_rep (g n)) \<rho>" by (rule pHc_rep_language[OF domain])
    have equality: "pHc_class \<rho> (pHc_rep (g n)) = pHc_class \<rho> (s n)"
      using pHc_rep_reconstruct[OF domain] represents[OF lookup] by simp
    show ?thesis by (rule iffD1[OF pHc_class_eq_iff[OF rep_lang sub[OF lookup]] equality])
  qed
  have equality: "pHc_class \<tau> (psubst (\<lambda>n. pHc_rep (g n)) M) = pHc_class \<tau> (psubst s M)"
    by (rule pHc_subst_class_eq[where \<Gamma>=\<Gamma> and M=M and \<tau>=\<tau>
          and s="\<lambda>n. pHc_rep (g n)" and r=s, OF typed sig agree])
  show ?thesis by (simp only: pHc_denote_typed_form[OF typed sig env] equality)
qed

lemma pHc_denote_Var:
  assumes lookup: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g (PVar n) = g n"
proof -
  have typed: "has_ptype \<Gamma> (PVar n) \<sigma>" by (rule has_ptype.PVar[OF lookup])
  have sig: "pterm_in_signature signature (PVar n)" by simp
  have domain: "g n \<in> pHc_domain \<sigma>" by (rule pbbk_env_lookup[OF env lookup])
  show ?thesis by (simp only: pHc_denote_typed_form[OF typed sig env] psubst.simps pHc_rep_reconstruct[OF domain])
qed

lemma pHc_denote_closed:
  assumes typed: "has_ptype [] M \<tau>"
  shows "pHc_denote g M = pHc_class \<tau> M"
  by (simp add: pHc_denote_def pHcs_closed_subst[OF typed] pHc_type_of_typed[OF typed])

subsection \<open>Application is independent of representatives\<close>

definition pHc_application :: "otype \<Rightarrow> otype \<Rightarrow> 'c pHc_value \<Rightarrow> 'c pHc_value \<Rightarrow> 'c pHc_value" where
  "pHc_application \<sigma> \<tau> f a = pHc_class \<tau> (PApp (pHc_rep f) (pHc_rep a))"

lemma pHc_application_type:
  assumes f: "f \<in> pHc_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and a: "a \<in> pHc_domain \<sigma>"
  shows "pHc_application \<sigma> \<tau> f a \<in> pHc_domain \<tau>"
  unfolding pHc_application_def
  by (rule pHc_class_in_domain[OF pHcs_app_language[OF pHc_rep_language[OF f] pHc_rep_language[OF a]]])

lemma pHc_application_classes:
  assumes f: "pterm_in_language signature [] F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and a: "pterm_in_language signature [] A \<sigma>"
  shows "pHc_application \<sigma> \<tau> (pHc_class (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pHc_class \<sigma> A) = pHc_class \<tau> (PApp F A)"
proof -
  let ?F = "pHc_rep (pHc_class (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)"
  let ?A = "pHc_rep (pHc_class \<sigma> A)"
  have eq: "pH_term_eq \<tau> (PApp ?F ?A) (PApp F A)"
    by (rule pH_term_eq_app[OF pHc_rep_class_eq[OF f] pHc_rep_class_eq[OF a]])
  have result: "pHc_class \<tau> (PApp ?F ?A) = pHc_class \<tau> (PApp F A)"
    by (rule iffD2[OF pHc_class_eq_iff[OF pH_term_eq_left[OF eq] pH_term_eq_right[OF eq]] eq])
  show ?thesis using result by (simp only: pHc_application_def)
qed

lemma pHc_denote_App:
  assumes f: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and a: "has_ptype \<Gamma> A \<sigma>"
    and sf: "pterm_in_signature signature F" and sa: "pterm_in_signature signature A"
    and env: "pbbk_env_typed pHc_domain \<Gamma> g"
  shows "pHc_denote g (PApp F A) = pHc_application \<sigma> \<tau> (pHc_denote g F) (pHc_denote g A)"
proof -
  have app_type: "has_ptype \<Gamma> (PApp F A) \<tau>" by (rule has_ptype.PApp[OF f a])
  have app_sig: "pterm_in_signature signature (PApp F A)" using sf sa by simp
  have fl: "pterm_in_language signature [] (psubst (\<lambda>n. pHc_rep (g n)) F) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule pHc_closed_instance_language[OF f sf env])
  have al: "pterm_in_language signature [] (psubst (\<lambda>n. pHc_rep (g n)) A) \<sigma>"
    by (rule pHc_closed_instance_language[OF a sa env])
  show ?thesis by (simp only: pHc_denote_typed_form[OF app_type app_sig env] psubst.simps
    pHc_denote_typed_form[OF f sf env] pHc_denote_typed_form[OF a sa env] pHc_application_classes[OF fl al])
qed

end
end
