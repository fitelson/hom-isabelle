theory Bacon_PP_Goodman_T9
  imports 
    "Goodman_Legacy_T8_Growth.Bacon_PP_Goodman_T8_Growth"
begin

unbundle cardinal_syntax

text \<open>
  The absorption law for infinite cardinal products is stated in session
  \<open>HOL-Cardinals\<close> but not in \<open>Main\<close>; it is re-proved here from the
  \<open>Main\<close> Sigma bound so that this theory needs no extra session.
\<close>

lemma pp_T9_Times_ordLeq_infinite:
  assumes "\<not> finite C" and "|A| \<le>o |C|" and "|B| \<le>o |C|"
  shows "|A \<times> B| \<le>o |C|"
  using assms by (simp add: card_of_Sigma_ordLeq_infinite)

section \<open>Goodman T9: the abstract cardinal dichotomy\<close>

text \<open>
  This theory isolates the set-theoretic content of T9.  The set \<open>P\<close>
  represents the pure unary operators, \<open>K\<close> their kinds, and \<open>G\<close> the
  pure invertible operators.  Pure Completeness supplies an injection from
  \<open>Pow K\<close> into \<open>P\<close>.  A kind map together with an injective code of every
  kind-fibre into \<open>G\<close> supplies an injection from \<open>P\<close> into \<open>K \<times> G\<close>.
\<close>

definition pp_T9_kind_fibre ::
    "'p set \<Rightarrow> ('p \<Rightarrow> 'k) \<Rightarrow> 'k \<Rightarrow> 'p set" where
  "pp_T9_kind_fibre P kind k = {p \<in> P. kind p = k}"

section \<open>The two counting bridges\<close>

text \<open>
  Pure Completeness supplies, for every set of kinds, a pure property true
  of exactly the operators whose kind belongs to that set.  Provided every
  kind is represented, distinct sets of kinds therefore determine distinct
  properties.
\<close>

theorem pp_T9_PC_specification_injective:
  fixes pc :: "'k set \<Rightarrow> 'p"
    and holds :: "'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes represented:
      "\<And>k. k \<in> K \<Longrightarrow>
        \<exists>p \<in> P. kind p = k"
    and pc_spec:
      "\<And>S p. S \<in> Pow K \<Longrightarrow> p \<in> P \<Longrightarrow>
        holds (pc S) p \<longleftrightarrow> kind p \<in> S"
  shows "inj_on pc (Pow K)"
proof (rule inj_onI)
  fix S U
  assume S: "S \<in> Pow K"
    and U: "U \<in> Pow K"
    and same: "pc S = pc U"
  show "S = U"
  proof (rule set_eqI)
    fix k
    show "k \<in> S \<longleftrightarrow> k \<in> U"
    proof (cases "k \<in> K")
      case True
      then obtain p where p: "p \<in> P" and kp: "kind p = k"
        using represented by blast
      have "k \<in> S \<longleftrightarrow> holds (pc S) p"
        using pc_spec[OF S p] kp by simp
      also have "... \<longleftrightarrow> holds (pc U) p"
        using same by simp
      also have "... \<longleftrightarrow> k \<in> U"
        using pc_spec[OF U p] kp by simp
      finally show ?thesis .
    next
      case False
      have "k \<notin> S" using S False by auto
      moreover have "k \<notin> U" using U False by auto
      ultimately show ?thesis by simp
    qed
  qed
qed

text \<open>
  If a kind is an orbit under the pure invertibles, choose for each member
  of the orbit one invertible taking the representative to that member.
  Equality of chosen invertibles forces equality of their images, so this
  choice is injective.  No freeness of the action is required.
\<close>

definition pp_T9_orbit_code ::
    "'g set \<Rightarrow> ('g \<Rightarrow> 'p \<Rightarrow> 'p) \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'g"
where
  "pp_T9_orbit_code G act representative p =
    (SOME g. g \<in> G \<and> act g representative = p)"

theorem pp_T9_orbit_fibre_code:
  assumes orbit:
      "\<And>p. p \<in> pp_T9_kind_fibre P kind k \<Longrightarrow>
        \<exists>g \<in> G. act g representative = p"
  shows
    "inj_on (pp_T9_orbit_code G act representative)
      (pp_T9_kind_fibre P kind k)"
    "pp_T9_orbit_code G act representative `
      pp_T9_kind_fibre P kind k \<subseteq> G"
proof -
  have witness:
      "\<And>p. p \<in> pp_T9_kind_fibre P kind k \<Longrightarrow>
        pp_T9_orbit_code G act representative p \<in> G
        \<and>
        act (pp_T9_orbit_code G act representative p)
          representative = p"
  proof -
    fix p
    assume p: "p \<in> pp_T9_kind_fibre P kind k"
    obtain g where "g \<in> G" and "act g representative = p"
      using orbit[OF p] by blast
    then have ex:
        "\<exists>g. g \<in> G \<and> act g representative = p"
      by blast
    have chosen:
        "(SOME g. g \<in> G \<and> act g representative = p) \<in> G
          \<and>
         act (SOME g. g \<in> G \<and> act g representative = p)
           representative = p"
      using ex by (rule someI_ex)
    show
      "pp_T9_orbit_code G act representative p \<in> G
        \<and>
       act (pp_T9_orbit_code G act representative p)
         representative = p"
      unfolding pp_T9_orbit_code_def
      using chosen .
  qed
  show "inj_on (pp_T9_orbit_code G act representative)
      (pp_T9_kind_fibre P kind k)"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix p q
    assume p: "p \<in> pp_T9_kind_fibre P kind k"
      and q: "q \<in> pp_T9_kind_fibre P kind k"
      and same:
        "pp_T9_orbit_code G act representative p =
         pp_T9_orbit_code G act representative q"
    have p_image:
        "act (pp_T9_orbit_code G act representative p)
          representative = p"
      using witness[OF p] by blast
    have q_image:
        "act (pp_T9_orbit_code G act representative q)
          representative = q"
      using witness[OF q] by blast
    show "p = q"
      using p_image q_image same by metis
  qed
  show "pp_T9_orbit_code G act representative `
      pp_T9_kind_fibre P kind k \<subseteq> G"
    using witness by blast
qed

corollary pp_T9_orbit_local_code:
  assumes representatives:
      "\<And>k. k \<in> K \<Longrightarrow>
        rep k \<in> pp_T9_kind_fibre P kind k"
    and orbit_kinds:
      "\<And>k p. k \<in> K \<Longrightarrow>
        p \<in> pp_T9_kind_fibre P kind k \<Longrightarrow>
        \<exists>g \<in> G. act g (rep k) = p"
  shows
    "\<And>k. k \<in> K \<Longrightarrow>
      inj_on (pp_T9_orbit_code G act (rep k))
        (pp_T9_kind_fibre P kind k)
      \<and>
      pp_T9_orbit_code G act (rep k) `
        pp_T9_kind_fibre P kind k \<subseteq> G"
proof -
  fix k
  assume k: "k \<in> K"
  have orbit:
      "\<And>p. p \<in> pp_T9_kind_fibre P kind k \<Longrightarrow>
        \<exists>g \<in> G. act g (rep k) = p"
    using orbit_kinds[OF k] .
  have code_inj:
      "inj_on (pp_T9_orbit_code G act (rep k))
        (pp_T9_kind_fibre P kind k)"
    by (rule pp_T9_orbit_fibre_code(1)[
      where P=P and kind=kind and k=k and G=G and act=act
        and representative="rep k", OF orbit])
  have code_range:
      "pp_T9_orbit_code G act (rep k) `
        pp_T9_kind_fibre P kind k \<subseteq> G"
    by (rule pp_T9_orbit_fibre_code(2)[
      where P=P and kind=kind and k=k and G=G and act=act
        and representative="rep k", OF orbit])
  show
    "inj_on (pp_T9_orbit_code G act (rep k))
        (pp_T9_kind_fibre P kind k)
      \<and>
     pp_T9_orbit_code G act (rep k) `
        pp_T9_kind_fibre P kind k \<subseteq> G"
    using code_inj code_range by blast
qed

lemma pp_T9_global_orbit_code:
  assumes kind_closed: "kind ` P \<subseteq> K"
    and local_code:
      "\<And>k. k \<in> K \<Longrightarrow>
        inj_on (code k) (pp_T9_kind_fibre P kind k)
        \<and> code k ` pp_T9_kind_fibre P kind k \<subseteq> G"
  shows
    "inj_on (\<lambda>p. (kind p, code (kind p) p)) P"
    "(\<lambda>p. (kind p, code (kind p) p)) ` P \<subseteq> K \<times> G"
proof -
  show "inj_on (\<lambda>p. (kind p, code (kind p) p)) P"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix p q
    assume p: "p \<in> P" and q: "q \<in> P"
      and pair:
        "(kind p, code (kind p) p) =
         (kind q, code (kind q) q)"
    have kind_eq: "kind p = kind q"
      using pair by simp
    have kind_mem: "kind p \<in> K"
      using kind_closed p by blast
    have fibre_p: "p \<in> pp_T9_kind_fibre P kind (kind p)"
      using p by (simp add: pp_T9_kind_fibre_def)
    have fibre_q: "q \<in> pp_T9_kind_fibre P kind (kind p)"
      using q kind_eq by (simp add: pp_T9_kind_fibre_def)
    have code_eq: "code (kind p) p = code (kind p) q"
      using pair kind_eq by simp
    show "p = q"
      using local_code[OF kind_mem] fibre_p fibre_q code_eq
      unfolding inj_on_def by blast
  qed
  show "(\<lambda>p. (kind p, code (kind p) p)) ` P \<subseteq> K \<times> G"
  proof
    fix z
    assume "z \<in> (\<lambda>p. (kind p, code (kind p) p)) ` P"
    then obtain p where p: "p \<in> P"
      and z: "z = (kind p, code (kind p) p)" by blast
    have kind_mem: "kind p \<in> K"
      using kind_closed p by blast
    have fibre_p: "p \<in> pp_T9_kind_fibre P kind (kind p)"
      using p by (simp add: pp_T9_kind_fibre_def)
    have "code (kind p) p \<in> G"
      using local_code[OF kind_mem] fibre_p by blast
    then show "z \<in> K \<times> G"
      using kind_mem z by simp
  qed
qed

theorem pp_T9_counting_bound:
  assumes pc_injective: "inj_on pc (Pow K)"
    and pc_pure: "pc ` Pow K \<subseteq> P"
    and kind_closed: "kind ` P \<subseteq> K"
    and local_code:
      "\<And>k. k \<in> K \<Longrightarrow>
        inj_on (code k) (pp_T9_kind_fibre P kind k)
        \<and> code k ` pp_T9_kind_fibre P kind k \<subseteq> G"
  shows "|Pow K| \<le>o |K \<times> G|"
proof -
  have pow_le_pure: "|Pow K| \<le>o |P|"
    using pc_injective pc_pure card_of_ordLeq by blast
  have global:
      "inj_on (\<lambda>p. (kind p, code (kind p) p)) P
       \<and>
       (\<lambda>p. (kind p, code (kind p) p)) ` P \<subseteq> K \<times> G"
    using pp_T9_global_orbit_code[OF kind_closed local_code] by blast
  have pure_le_product: "|P| \<le>o |K \<times> G|"
    using global card_of_ordLeq by blast
  show ?thesis
    using pow_le_pure pure_le_product
    by (rule ordLeq_transitive)
qed

theorem pp_T9_cardinal_dichotomy:
  assumes counting: "|Pow K| \<le>o |K \<times> G|"
  shows "finite K \<or> |Pow K| \<le>o |G|"
proof (cases "finite K")
  case True
  then show ?thesis by blast
next
  case False
  have not_G_le_K: "\<not> |G| \<le>o |K|"
  proof
    assume G_le_K: "|G| \<le>o |K|"
    have product_le_K: "|K \<times> G| \<le>o |K|"
      using False ordLeq_refl[OF card_of_Card_order] G_le_K
      by (rule pp_T9_Times_ordLeq_infinite)
    have pow_le_K: "|Pow K| \<le>o |K|"
      using counting product_le_K by (rule ordLeq_transitive)
    have "|K| <o |Pow K|"
      by (rule card_of_Pow)
    then show False
      using pow_le_K not_ordLess_ordLeq by blast
  qed
  have K_le_G: "|K| \<le>o |G|"
  proof -
    have wK: "Well_order |K|" by (rule card_of_Well_order)
    have wG: "Well_order |G|" by (rule card_of_Well_order)
    have "|K| <o |G|"
      using not_G_le_K not_ordLeq_iff_ordLess[OF wK wG] by blast
    then show ?thesis by (rule ordLess_imp_ordLeq)
  qed
  have infinite_G: "\<not> finite G"
  proof
    assume fin: "finite G"
    have "finite K"
      using K_le_G fin by (rule card_of_ordLeq_finite)
    then show False
      using False by simp
  qed
  have product_le_G: "|K \<times> G| \<le>o |G|"
    using infinite_G K_le_G ordLeq_refl[OF card_of_Card_order]
    by (rule pp_T9_Times_ordLeq_infinite)
  have pow_le_G: "|Pow K| \<le>o |G|"
    using counting product_le_G
    by (rule ordLeq_transitive)
  show ?thesis
    using pow_le_G by blast
qed

corollary pp_T9_PC_cardinal_dichotomy:
  assumes pc_injective: "inj_on pc (Pow K)"
    and pc_pure: "pc ` Pow K \<subseteq> P"
    and kind_closed: "kind ` P \<subseteq> K"
    and local_code:
      "\<And>k. k \<in> K \<Longrightarrow>
        inj_on (code k) (pp_T9_kind_fibre P kind k)
        \<and> code k ` pp_T9_kind_fibre P kind k \<subseteq> G"
  shows "finite K \<or> |Pow K| \<le>o |G|"
  using pp_T9_counting_bound[OF assms]
  by (rule pp_T9_cardinal_dichotomy)

corollary pp_T9_advertised_PC_orbit_dichotomy:
  fixes pc :: "'k set \<Rightarrow> 'p"
    and holds :: "'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes represented:
      "\<And>k. k \<in> K \<Longrightarrow>
        \<exists>p \<in> P. kind p = k"
    and pc_specification:
      "\<And>S p. S \<in> Pow K \<Longrightarrow> p \<in> P \<Longrightarrow>
        holds (pc S) p \<longleftrightarrow> kind p \<in> S"
    and pc_pure: "pc ` Pow K \<subseteq> P"
    and kind_closed: "kind ` P \<subseteq> K"
    and representatives:
      "\<And>k. k \<in> K \<Longrightarrow>
        rep k \<in> pp_T9_kind_fibre P kind k"
    and orbit_kinds:
      "\<And>k p. k \<in> K \<Longrightarrow>
        p \<in> pp_T9_kind_fibre P kind k \<Longrightarrow>
        \<exists>g \<in> G. act g (rep k) = p"
  shows "finite K \<or> |Pow K| \<le>o |G|"
proof -
  have pc_injective: "inj_on pc (Pow K)"
    using represented pc_specification
    by (rule pp_T9_PC_specification_injective)
  have local:
      "\<And>k. k \<in> K \<Longrightarrow>
        inj_on
          ((\<lambda>k. pp_T9_orbit_code G act (rep k)) k)
          (pp_T9_kind_fibre P kind k)
        \<and>
        ((\<lambda>k. pp_T9_orbit_code G act (rep k)) k) `
          pp_T9_kind_fibre P kind k \<subseteq> G"
  proof -
    fix k
    assume k: "k \<in> K"
    show
      "inj_on
          ((\<lambda>k. pp_T9_orbit_code G act (rep k)) k)
          (pp_T9_kind_fibre P kind k)
        \<and>
       ((\<lambda>k. pp_T9_orbit_code G act (rep k)) k) `
          pp_T9_kind_fibre P kind k \<subseteq> G"
      using pp_T9_orbit_local_code[
        where P=P and kind=kind and K=K and rep=rep
          and G=G and act=act,
        OF representatives orbit_kinds k] .
  qed
  show ?thesis
    using pp_T9_PC_cardinal_dichotomy[
      OF pc_injective pc_pure kind_closed local] .
qed

text \<open>
  The use of infinite-cardinal multiplication in
  \<open>pp_T9_cardinal_dichotomy\<close> is the classical-choice step behind the prose
  inference from \<open>2\<^sup>\<kappa> \<le> \<kappa> \<cdot> |G|\<close> to the infinite horn
  \<open>2\<^sup>\<kappa> \<le> |G|\<close>.  In Isabelle/HOL, choice is part of the ambient logic.
\<close>

end
