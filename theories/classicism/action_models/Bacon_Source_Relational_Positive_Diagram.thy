theory Bacon_Source_Relational_Positive_Diagram
  imports Bacon_Source_Relational_Closed_Theory Bacon_Source_Relational_Validity_Basics
    Bacon_Source_Relational_Identity_Axiom_Truth
begin

section \<open>The positive closed identity diagram\<close>

text \<open>
  Δ(M) consists of all closed identities A=σB in the declared language
  whose operands have the same denotation in M. Closedness permits
  evaluation at the empty assignment. Only positive identities are
  included, not unequal-value assertions or the separating negation.
  Source: Bacon–Dorr, Theorem 3.12, p.51 n.73.

  The definition makes sense for an arbitrary interpretation J. The
  validity result below separately requires an actual R BBK model.
  In the naming language this becomes the diagram of M⁺; no naming
  construction or model-existence assumption is built into Δ itself.
\<close>

definition paper_R_positive_diagram ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    'c paper_named_term set" where
  "paper_R_positive_diagram \<Sigma> G J = {E. \<exists>\<sigma> A B.
    E = named_paper_eq \<sigma> A B \<and>
    paper_R_in_language \<Sigma> G A \<sigma> \<and> paper_R_in_language \<Sigma> G B \<sigma> \<and>
    named_fv A = {} \<and> named_fv B = {} \<and> J Map.empty A = J Map.empty B}"

lemma paper_R_positive_diagramI:
  assumes al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    and same: "J Map.empty A = J Map.empty B"
  shows "named_paper_eq \<sigma> A B \<in> paper_R_positive_diagram \<Sigma> G J"
  using al bl ac bc same unfolding paper_R_positive_diagram_def by blast

lemma paper_R_positive_diagramE:
  assumes member: "E \<in> paper_R_positive_diagram \<Sigma> G J"
  obtains \<sigma> A B where "E = named_paper_eq \<sigma> A B"
    "paper_R_in_language \<Sigma> G A \<sigma>" "paper_R_in_language \<Sigma> G B \<sigma>"
    "named_fv A = {}" "named_fv B = {}" "J Map.empty A = J Map.empty B"
  using member unfolding paper_R_positive_diagram_def by blast

lemma paper_R_positive_diagram_closed:
  "paper_R_closed_theory \<Sigma> G (paper_R_positive_diagram \<Sigma> G J)"
proof (unfold paper_R_closed_theory_def, intro ballI)
  fix E
  assume member: "E \<in> paper_R_positive_diagram \<Sigma> G J"
  obtain \<sigma> A B where shape: "E = named_paper_eq \<sigma> A B"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>" and bl: "paper_R_in_language \<Sigma> G B \<sigma>"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    using paper_R_positive_diagramE[OF member] by blast
  have language: "paper_R_in_language \<Sigma> G E Prop"
    by (simp only: shape; rule paper_R_named_eq_language[OF al bl])
  have closed: "named_fv E = {}" by (simp add: shape named_paper_primitive_fv ac bc)
  show "paper_R_sentence \<Sigma> G E" by (rule paper_R_sentenceI[OF language closed])
qed

context paper_R_bbk_model
begin

lemma paper_R_closed_denote_empty:
  assumes language: "paper_R_in_language signature stock A \<sigma>"
    and closed: "named_fv A = {}" and typed: "named_env_typed domain stock g"
  shows "denote g A = denote Map.empty A"
proof -
  have empty_typed: "named_env_typed domain stock Map.empty" by (simp add: named_env_typed_def)
  have ga: "named_adequate g A" and ea: "named_adequate Map.empty A"
    by (simp_all add: named_adequate_def closed)
  show ?thesis by (rule denote_locality[OF language typed empty_typed ga ea]; simp add: closed)
qed

theorem paper_R_positive_diagram_valid:
  assumes member: "E \<in> paper_R_positive_diagram signature stock denote"
  shows "paper_R_valid E"
proof -
  obtain \<sigma> A B where shape: "E = named_paper_eq \<sigma> A B"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and bl: "paper_R_in_language signature stock B \<sigma>"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    and same: "denote Map.empty A = denote Map.empty B"
    by (rule paper_R_positive_diagramE[OF member])
  have language: "paper_R_in_language signature stock E Prop"
    by (simp only: shape; rule paper_R_named_eq_language[OF al bl])
  show ?thesis
  proof (rule paper_R_validI[OF language])
    fix g
    assume typed: "named_env_typed domain stock g" and "named_adequate g E"
    have aa: "named_adequate g A" and ba: "named_adequate g B"
      by (simp_all add: named_adequate_def ac bc)
    have equality: "denote g A = denote g B"
      by (simp only: paper_R_closed_denote_empty[OF al ac typed]
        paper_R_closed_denote_empty[OF bl bc typed]; rule same)
    show "valuation (denote g E)"
      by (simp only: shape named_paper_eq_def valuation_identity[OF al bl typed aa ba]; rule equality)
  qed
qed

end

end
