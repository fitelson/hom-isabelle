theory Bacon_Source_Relational_Recoding_Assignments
  imports Bacon_Source_Relational_BBK_Interface
    Bacon_Source_Model_Development.Bacon_Source_Named_Recoding_Assignments
begin

section \<open>Recoding only the values that belong to actual domains\<close>

text \<open>
  Put D'σ=f[Dσ] and map each defined assignment entry through f.
  The inverse is inv_into(⋃σ.Dσ,f), not a global inverse of f.
  Injectivity is required only on that actual union. This permits
  recoding a countable domain union whose ambient HOL carrier is
  uncountable. Source role: the countable refinement of Theorem 3.2,
  pp.44–45, with the partial assignments of Definition 3.1.

  These are generic data facts, not model theorems. No R/F model,
  Henkin property, nonemptiness, countability or proof judgment is
  assumed. Undefined assignment entries stay undefined. Inverse laws
  are asserted only with the displayed domain/image membership guards.
\<close>

definition paper_R_recode_domain :: "('v \<Rightarrow> 'w) \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow> otype \<Rightarrow> 'w set" where
  "paper_R_recode_domain f D \<sigma> = image f (D \<sigma>)"

definition paper_R_recode_assignment :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v named_assignment \<Rightarrow> 'w named_assignment" where
  "paper_R_recode_assignment f g n = map_option f (g n)"

definition paper_R_recode_inverse :: "(otype \<Rightarrow> 'v set) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> 'w \<Rightarrow> 'v" where
  "paper_R_recode_inverse D f = inv_into (\<Union>\<sigma>. D \<sigma>) f"

lemma paper_R_recode_domain_eq_named:
  "paper_R_recode_domain f D = named_image_domain f D"
  by (rule ext; simp only: paper_R_recode_domain_def named_image_domain_def)

lemma paper_R_recode_assignment_eq_named:
  "paper_R_recode_assignment f g = named_map_assignment f g"
  by (rule ext; simp only: paper_R_recode_assignment_def named_map_assignment_def)

lemma paper_R_recode_domainI:
  "a \<in> D \<sigma> \<Longrightarrow> f a \<in> paper_R_recode_domain f D \<sigma>"
  unfolding paper_R_recode_domain_def by (rule imageI; assumption)

lemma paper_R_recode_domainE:
  assumes member: "b \<in> paper_R_recode_domain f D \<sigma>"
  obtains a where "a \<in> D \<sigma>" "b = f a"
  using member that unfolding paper_R_recode_domain_def by blast

lemma paper_R_recode_domain_nonempty:
  "paper_R_recode_domain f D \<sigma> \<noteq> {} \<longleftrightarrow> D \<sigma> \<noteq> {}"
  by (simp add: paper_R_recode_domain_def)

lemma paper_R_recode_domain_empty:
  "D \<sigma> = {} \<Longrightarrow> paper_R_recode_domain f D \<sigma> = {}"
  by (simp add: paper_R_recode_domain_def)

lemma paper_R_recode_domain_union:
  "(\<Union>\<sigma>. paper_R_recode_domain f D \<sigma>) = image f (\<Union>\<sigma>. D \<sigma>)"
  by (auto simp: paper_R_recode_domain_def)

lemma paper_R_recode_inverse_on:
  assumes injective: "inj_on f (\<Union>\<sigma>. D \<sigma>)" and member: "a \<in> D \<sigma>"
  shows "paper_R_recode_inverse D f (f a) = a"
proof -
  have in_union: "a \<in> (\<Union>\<sigma>. D \<sigma>)" using member by blast
  show ?thesis unfolding paper_R_recode_inverse_def
    by (rule inv_into_f_f[where A="\<Union>\<sigma>. D \<sigma>" and f=f and x=a, OF injective in_union])
qed

lemma paper_R_recode_inverse_type:
  assumes injective: "inj_on f (\<Union>\<sigma>. D \<sigma>)" and member: "b \<in> paper_R_recode_domain f D \<sigma>"
  shows "paper_R_recode_inverse D f b \<in> D \<sigma>"
proof -
  obtain a where original: "a \<in> D \<sigma>" and shape: "b = f a" by (rule paper_R_recode_domainE[OF member])
  show ?thesis by (simp only: shape paper_R_recode_inverse_on[where D=D and \<sigma>=\<sigma>, OF injective original]; rule original)
qed

lemma paper_R_recode_inverse_right:
  assumes member: "b \<in> paper_R_recode_domain f D \<sigma>"
  shows "f (paper_R_recode_inverse D f b) = b"
proof -
  have in_image: "b \<in> image f (\<Union>\<sigma>. D \<sigma>)" using member unfolding paper_R_recode_domain_def by blast
  show ?thesis unfolding paper_R_recode_inverse_def by (rule f_inv_into_f[OF in_image])
qed

section \<open>Domain, adequacy and update equations for partial assignments\<close>

lemma paper_R_recode_assignment_value:
  "g n = Some a \<Longrightarrow> paper_R_recode_assignment f g n = Some (f a)"
  by (simp add: paper_R_recode_assignment_def)

lemma paper_R_recode_assignment_valueE:
  assumes assigned: "paper_R_recode_assignment f g n = Some b"
  obtains a where "g n = Some a" "b = f a"
  using assigned that by (cases "g n") (auto simp: paper_R_recode_assignment_def)

lemma paper_R_recode_assignment_domain:
  "dom (paper_R_recode_assignment f g) = dom g"
  by (simp only: paper_R_recode_assignment_eq_named named_map_assignment_domain)

lemma paper_R_recode_assignment_adequate_iff:
  "named_adequate (paper_R_recode_assignment f g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: paper_R_recode_assignment_eq_named named_map_assignment_adequate)

lemma paper_R_recode_assignment_update:
  "paper_R_recode_assignment f (g(n := Some a)) = (paper_R_recode_assignment f g)(n := Some (f a))"
  by (simp only: paper_R_recode_assignment_eq_named named_map_assignment_update)

lemma paper_R_recode_assignment_delete:
  "paper_R_recode_assignment f (g(n := None)) = (paper_R_recode_assignment f g)(n := None)"
  by (rule ext; simp add: paper_R_recode_assignment_def)

lemma paper_R_recode_assignment_empty:
  "paper_R_recode_assignment f Map.empty = Map.empty"
  by (simp only: paper_R_recode_assignment_eq_named named_map_assignment_empty)

lemma paper_R_recode_assignment_comp:
  "paper_R_recode_assignment k (paper_R_recode_assignment f g) = paper_R_recode_assignment (k \<circ> f) g"
  by (simp only: paper_R_recode_assignment_eq_named named_map_assignment_comp)

theorem paper_R_recode_assignment_typed:
  assumes typed: "named_env_typed D G g"
  shows "named_env_typed (paper_R_recode_domain f D) G (paper_R_recode_assignment f g)"
  by (simp only: paper_R_recode_domain_eq_named paper_R_recode_assignment_eq_named;
    rule named_map_assignment_typed[OF typed])

theorem paper_R_recode_inverse_assignment_typed:
  assumes injective: "inj_on f (\<Union>\<sigma>. D \<sigma>)" and typed: "named_env_typed (paper_R_recode_domain f D) G g"
  shows "named_env_typed D G (paper_R_recode_assignment (paper_R_recode_inverse D f) g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "paper_R_recode_assignment (paper_R_recode_inverse D f) g n = Some a"
  obtain b where original: "g n = Some b" and decoded: "a = paper_R_recode_inverse D f b"
    by (rule paper_R_recode_assignment_valueE[OF assigned])
  have member: "b \<in> paper_R_recode_domain f D (G n)" by (rule named_env_value[OF typed original])
  show "a \<in> D (G n)" by (simp only: decoded; rule paper_R_recode_inverse_type[OF injective member])
qed

theorem paper_R_recode_assignment_inverse_left:
  assumes injective: "inj_on f (\<Union>\<sigma>. D \<sigma>)" and typed: "named_env_typed D G g"
  shows "paper_R_recode_assignment (paper_R_recode_inverse D f) (paper_R_recode_assignment f g) = g"
proof (rule ext)
  fix n
  show "paper_R_recode_assignment (paper_R_recode_inverse D f) (paper_R_recode_assignment f g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp add: paper_R_recode_assignment_def None)
  next
    case (Some a)
    have member: "a \<in> D (G n)" by (rule named_env_value[OF typed Some])
    have inverse: "paper_R_recode_inverse D f (f a) = a" by (rule paper_R_recode_inverse_on[OF injective member])
    show ?thesis by (simp add: paper_R_recode_assignment_def Some inverse)
  qed
qed

theorem paper_R_recode_assignment_inverse_right:
  assumes typed: "named_env_typed (paper_R_recode_domain f D) G g"
  shows "paper_R_recode_assignment f (paper_R_recode_assignment (paper_R_recode_inverse D f) g) = g"
proof (rule ext)
  fix n
  show "paper_R_recode_assignment f (paper_R_recode_assignment (paper_R_recode_inverse D f) g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp add: paper_R_recode_assignment_def None)
  next
    case (Some b)
    have member: "b \<in> paper_R_recode_domain f D (G n)" by (rule named_env_value[OF typed Some])
    have inverse: "f (paper_R_recode_inverse D f b) = b" by (rule paper_R_recode_inverse_right[OF member])
    show ?thesis by (simp add: paper_R_recode_assignment_def Some inverse)
  qed
qed

end
