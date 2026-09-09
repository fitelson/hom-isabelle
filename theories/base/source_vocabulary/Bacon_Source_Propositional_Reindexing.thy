theory Bacon_Source_Propositional_Reindexing
  imports Bacon_Source_Propositional
begin

section \<open>Finite schematic labels do not restrict source signatures\<close>

text \<open>
  PC substitutes formulas into a finite propositional template
  (Bacon–Dorr Figure 2, p.8). Its finitely many occurring schematic labels
  can be replaced by natural-number positions regardless of the size of
  the source's nonlogical-name carrier.

  Isabelle representation: map_sprop_template relabels only schematic atoms.
  A finite list enumerates the occurring labels; a chosen index recovers
  each label in that list. Off-list indices are never used for reconstruction.

  Status: tautology-preserving relabeling and literal instance reconstruction.
  No countability typeclass, model, or H theorem-reflection assumption.
\<close>

lemma sprop_atoms_finite:
  "finite (sprop_atoms P)"
  by (induction P) simp_all

lemma sprop_eval_map:
  "sprop_eval v (map_sprop_template f P) = sprop_eval (\<lambda>a. v (f a)) P"
  by (induction P) simp_all

lemma sprop_tautology_map:
  assumes taut: "sprop_tautology P"
  shows "sprop_tautology (map_sprop_template f P)"
proof (unfold sprop_tautology_def, rule allI)
  fix v
  have "sprop_eval (\<lambda>a. v (f a)) P"
    by (rule spec[where x="\<lambda>a. v (f a)", OF taut[unfolded sprop_tautology_def]])
  then show "sprop_eval v (map_sprop_template f P)" by (simp only: sprop_eval_map)
qed

lemma paper_prop_instance_map:
  "paper_prop_instance v (map_sprop_template f P) =
    paper_prop_instance (\<lambda>a. v (f a)) P"
  by (induction P) simp_all

lemma paper_prop_instance_cong:
  assumes agrees: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> v a = w a"
  shows "paper_prop_instance v P = paper_prop_instance w P"
  using agrees by (induction P) auto

definition sprop_list_index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "sprop_list_index xs a = (SOME n. n < length xs \<and> xs ! n = a)"

lemma sprop_list_index_property:
  assumes member: "a \<in> set xs"
  shows "sprop_list_index xs a < length xs \<and> xs ! sprop_list_index xs a = a"
proof -
  have exists: "\<exists>n. n < length xs \<and> xs ! n = a"
    using member by (simp only: in_set_conv_nth)
  show ?thesis unfolding sprop_list_index_def by (rule someI_ex[OF exists])
qed

theorem paper_prop_instance_nat_template:
  fixes P :: "'a sprop_template" and v :: "'a \<Rightarrow> 'c paper_term"
  assumes taut: "sprop_tautology P"
  obtains Q :: "nat sprop_template" and w where "sprop_tautology Q"
    and "paper_prop_instance w Q = paper_prop_instance v P"
proof -
  obtain xs :: "'a list" where stock: "set xs = sprop_atoms P"
    using finite_list[OF sprop_atoms_finite[where P=P]] by (elim exE)
  let ?f = "sprop_list_index xs"
  let ?Q = "map_sprop_template ?f P"
  let ?w = "\<lambda>n. v (xs ! n)"
  have target_taut: "sprop_tautology ?Q" by (rule sprop_tautology_map[OF taut])
  have agrees: "\<And>a. a \<in> sprop_atoms P \<Longrightarrow> ?w (?f a) = v a"
  proof -
    fix a
    assume member: "a \<in> sprop_atoms P"
    have in_list: "a \<in> set xs" using member by (simp only: stock)
    have recovers: "xs ! ?f a = a" by (rule conjunct2[OF sprop_list_index_property[OF in_list]])
    show "?w (?f a) = v a" by (simp only: recovers)
  qed
  have same_instance: "paper_prop_instance ?w ?Q = paper_prop_instance v P"
    unfolding paper_prop_instance_map by (rule paper_prop_instance_cong[OF agrees])
  show thesis by (rule that[OF target_taut same_instance])
qed

end
