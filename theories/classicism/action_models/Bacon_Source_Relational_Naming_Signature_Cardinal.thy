theory Bacon_Source_Relational_Naming_Signature_Cardinal
  imports Bacon_Source_Relational_Naming_Syntax
    "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>The naming expansion preserves an infinite cardinal bound\<close>

lemma paper_R_naming_signature_union:
  "(\<Union>\<sigma>. paper_R_naming_signature \<Sigma> D \<sigma>) =
    image Inl (\<Union>\<sigma>. \<Sigma> \<sigma>) \<union> image Inr (\<Union>\<sigma>. D \<sigma>)"
  by (auto simp: paper_R_naming_signature_def)

theorem paper_R_naming_signature_cardinal_bound:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature" and D :: "otype \<Rightarrow> 'v set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and parameters: "card_of (\<Union>\<sigma>. D \<sigma>) \<le>o card_of U"
  shows "card_of (\<Union>\<sigma>. paper_R_naming_signature \<Sigma> D \<sigma>) \<le>o card_of U"
proof -
  have old: "card_of (image (Inl :: 'c \<Rightarrow> 'c + 'v) (\<Union>\<sigma>. \<Sigma> \<sigma>)) \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image names])
  have added: "card_of (image (Inr :: 'v \<Rightarrow> 'c + 'v) (\<Union>\<sigma>. D \<sigma>)) \<le>o card_of U"
    by (rule ordLeq_transitive[OF card_of_image parameters])
  show ?thesis unfolding paper_R_naming_signature_union
    by (rule card_of_Un_ordLeq_infinite[OF infinite old added])
qed

corollary paper_R_naming_signature_cardinal_bound_subset:
  fixes U :: "'u set" and \<Sigma> :: "'c ssignature" and D :: "otype \<Rightarrow> 'u set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and subset: "(\<Union>\<sigma>. D \<sigma>) \<subseteq> U"
  shows "card_of (\<Union>\<sigma>. paper_R_naming_signature \<Sigma> D \<sigma>) \<le>o card_of U"
  by (rule paper_R_naming_signature_cardinal_bound[
    OF infinite names card_of_mono1[OF subset]])

text \<open>
  The exact declared union contains only the tagged old names and
  tagged parameters. For infinite U, the union of two sets of
  cardinal at most |U| still has cardinal at most |U|.
  Source role: the naming language in p.51 n.73 and the uniform
  carrier refinement on p.52.

  D is an arbitrary typed family. No R model, nonemptiness, richness,
  theory, or bound on an entire ambient HOL carrier is assumed.
  The same parameter may occur at several types; the displayed
  signature union counts declared names, as required by the
  existing bounded sentence-set model-existence theorem.
\<close>

end
