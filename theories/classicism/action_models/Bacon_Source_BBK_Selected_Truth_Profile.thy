theory Bacon_Source_BBK_Selected_Truth_Profile
  imports Bacon_Source_BBK_Truth_Profile
begin

section \<open>Truth profiles for a selected collection of arrows\<close>

text \<open>
  val𝒞M(p)={h∈𝒞 | h:M→N and valN(hₜ(p))}.
  Source: Bacon–Dorr Definition 3.10, p.50, with the selected
  homomorphism collections of §3.3, p.49. The collection need not
  contain every homomorphism between its objects.

  Arrows below is an explicit set of model-record arrows on a common
  arbitrary HOL carrier. The profile and injectivity predicates are
  defined without presupposing that this set forms a BBK category.
  For semantic use, the separate selected-BBK-category certificate
  validates the objects, includes only genuine BBK arrows, and proves
  identity/composition closure. Naturality needs only its category
  certificate and the on-domain equation for the fixed composition.
  No valuation-preservation premise or proper-class representation is
  introduced. The previous all-arrows profile is a special case below.
\<close>

definition paper_bbk_truth_profile_on ::
  "('c,'v) paper_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> 'v \<Rightarrow> ('c,'v) paper_bbk_arrow set" where
  "paper_bbk_truth_profile_on Arrows M p =
    {h\<in>Arrows. paper_arrow_source h = M \<and>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p)}"

lemma paper_bbk_truth_profile_on_member:
  "h \<in> paper_bbk_truth_profile_on Arrows M p \<longleftrightarrow>
    h \<in> Arrows \<and> paper_arrow_source h = M \<and>
    paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p)"
  by (simp only: paper_bbk_truth_profile_on_def mem_Collect_eq)

lemma paper_bbk_truth_profile_on_outgoing:
  "paper_bbk_truth_profile_on Arrows M p \<subseteq>
    paper_outgoing Arrows paper_arrow_source M"
  by (auto simp only: paper_bbk_truth_profile_on_member paper_outgoing_member)

lemma paper_bbk_truth_profile_on_fiber:
  "paper_bbk_truth_profile_on Arrows M p \<in>
    paper_powerset_fiber Arrows paper_arrow_source M"
  by (rule iffD2[OF paper_powerset_fiber_member paper_bbk_truth_profile_on_outgoing])

section \<open>Transport of profiles is precomposition of outgoing arrows\<close>

text \<open>
  For f:M→N and p∈Mₜ,
  val𝒞N(fₜ(p))=fᴾ(val𝒞M(p)).
  Indeed, h:N→P belongs to either side precisely when
  valP(hₜ(fₜ(p))) holds. Source: Definition 3.10, p.50, and
  the powerset action of Example 3.15, p.54.

  The proof uses closure of arrows under composition and the
  on-domain equation (h∘f)ₜ(p)=hₜ(fₜ(p)). It never compares
  source and target truth values along a homomorphism.
\<close>

theorem paper_bbk_truth_profile_on_naturality:
  assumes category: "paper_category Obj Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain)"
    and arrow: "f \<in> Arrows"
    and member: "p \<in> paper_bbk_domain (paper_arrow_source f) Prop"
  shows "paper_bbk_truth_profile_on Arrows (paper_arrow_target f) (paper_arrow_map f Prop p) =
    paper_powerset_transport Arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) f
      (paper_bbk_truth_profile_on Arrows (paper_arrow_source f) p)"
proof -
  interpret Category: paper_category Obj Arrows
    paper_arrow_source paper_arrow_target "paper_typed_compose paper_bbk_domain"
    "paper_typed_identity paper_bbk_domain"
    by (rule category)
  show ?thesis
  proof (rule set_eqI)
    fix h
    show "(h \<in> paper_bbk_truth_profile_on Arrows (paper_arrow_target f) (paper_arrow_map f Prop p)) =
      (h \<in> paper_powerset_transport Arrows paper_arrow_source paper_arrow_target
        (paper_typed_compose paper_bbk_domain) f
        (paper_bbk_truth_profile_on Arrows (paper_arrow_source f) p))"
    proof (cases "h \<in> Arrows \<and> paper_arrow_source h = paper_arrow_target f")
      case True
      have ha: "h \<in> Arrows" and origin: "paper_arrow_source h = paper_arrow_target f"
        using True by blast+
      have meeting: "paper_arrow_target f = paper_arrow_source h" by (rule origin[symmetric])
      have composite: "paper_typed_compose paper_bbk_domain h f \<in> Arrows"
        by (rule Category.compose_arrow[OF arrow ha meeting])
      have mapped: "paper_arrow_map (paper_typed_compose paper_bbk_domain h f) Prop p =
        paper_arrow_map h Prop (paper_arrow_map f Prop p)"
        by (rule paper_typed_compose_map_on[where D=paper_bbk_domain and f=f and \<sigma>=Prop, OF member])
      show ?thesis
        by (simp only: paper_bbk_truth_profile_on_member paper_powerset_transport_member
          ha origin composite paper_typed_compose_endpoints mapped; simp)
    next
      case False
      show ?thesis using False
        by (auto simp only: paper_bbk_truth_profile_on_member paper_powerset_transport_member)
    qed
  qed
qed

section \<open>Quasi-Fregeanness is a separate injectivity condition\<close>

text \<open>
  A category is quasi-Fregean when val𝒞M is injective on Mₜ
  for each object M (Definition 3.11, p.50). For the present selected
  arrow collection we define that condition, then spell it out as separation
  by outgoing truth values. Neither quasi-Fregeanness nor existence
  of a category satisfying it is proved here.
\<close>

definition paper_bbk_quasi_fregean_on ::
  "('c,'v) paper_bbk_model_data set \<Rightarrow> ('c,'v) paper_bbk_arrow set \<Rightarrow> bool" where
  "paper_bbk_quasi_fregean_on Obj Arrows \<longleftrightarrow>
    (\<forall>M\<in>Obj. inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop))"

lemma paper_bbk_truth_profile_on_eq_iff:
  "paper_bbk_truth_profile_on Arrows M p = paper_bbk_truth_profile_on Arrows M q \<longleftrightarrow>
    (\<forall>h\<in>Arrows. paper_arrow_source h = M \<longrightarrow>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p) =
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop q))"
  by (auto simp only: set_eq_iff paper_bbk_truth_profile_on_member)

theorem paper_bbk_quasi_fregean_on_separates:
  assumes quasi: "paper_bbk_quasi_fregean_on Obj Arrows"
    and object: "M \<in> Obj"
    and pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop"
  shows "p = q \<longleftrightarrow>
    (\<forall>h\<in>Arrows. paper_arrow_source h = M \<longrightarrow>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p) =
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop q))"
proof
  assume equal: "p = q"
  show "\<forall>h\<in>Arrows. paper_arrow_source h = M \<longrightarrow>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p) =
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop q)"
    by (simp only: equal; simp)
next
  assume agree: "\<forall>h\<in>Arrows. paper_arrow_source h = M \<longrightarrow>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p) =
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop q)"
  have injective: "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
    using quasi object unfolding paper_bbk_quasi_fregean_on_def by blast
  have profiles: "paper_bbk_truth_profile_on Arrows M p = paper_bbk_truth_profile_on Arrows M q"
    by (rule iffD2[OF paper_bbk_truth_profile_on_eq_iff agree])
  show "p = q" by (rule inj_onD[OF injective profiles pm qm])
qed


section \<open>The all-homomorphisms collection is a special case\<close>

lemma paper_bbk_truth_profile_full_is_selected:
  "paper_bbk_truth_profile \<Sigma> G Obj M p =
    paper_bbk_truth_profile_on (paper_bbk_arrows \<Sigma> G Obj) M p"
  by (simp only: paper_bbk_truth_profile_def paper_bbk_truth_profile_on_def)

lemma paper_bbk_quasi_fregean_full_is_selected:
  "paper_bbk_quasi_fregean \<Sigma> G Obj \<longleftrightarrow>
    paper_bbk_quasi_fregean_on Obj (paper_bbk_arrows \<Sigma> G Obj)"
proof -
  have families: "paper_bbk_truth_profile \<Sigma> G Obj M =
    paper_bbk_truth_profile_on (paper_bbk_arrows \<Sigma> G Obj) M" for M
    by (rule ext; rule paper_bbk_truth_profile_full_is_selected)
  show ?thesis by (simp only: paper_bbk_quasi_fregean_def paper_bbk_quasi_fregean_on_def families)
qed

end
