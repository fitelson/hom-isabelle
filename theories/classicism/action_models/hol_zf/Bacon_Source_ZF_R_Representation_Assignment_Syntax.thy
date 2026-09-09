theory Bacon_Source_ZF_R_Representation_Assignment_Syntax
  imports Bacon_Source_ZF_R_Type_Recursion
begin

section \<open>Forward and inverse maps act only on defined assignment entries\<close>

text \<open>
  At M, send each assigned variable n to fG(n),M(g(n)); the
  inverse uses the corresponding fiber inverse. Source role:
  the assignment translation in Proposition 3.22's construction,
  p.72, with the partial-assignment convention of Definition 3.1.

  Both operations are option maps. They keep None as None and
  preserve the assignment domain and term adequacy without any
  typing or model assumption. In particular neither operation
  completes an assignment. Their semantic typing and inverse
  laws are proved separately for the actual recursive family.
\<close>

definition paper_ZF_R_encode_assignment ::
  "sgcontext \<Rightarrow> (otype \<Rightarrow> 'o paper_ZF_type_representation) \<Rightarrow>
    'o \<Rightarrow> ZF named_assignment \<Rightarrow> ZF named_assignment" where
  "paper_ZF_R_encode_assignment G reps M g =
    paper_hom_assignment G (\<lambda>\<rho>. paper_ZF_rep_encode (reps \<rho>) M) g"

definition paper_ZF_R_decode_assignment ::
  "sgcontext \<Rightarrow> ('o \<Rightarrow> otype \<Rightarrow> ZF set) \<Rightarrow>
    (otype \<Rightarrow> 'o paper_ZF_type_representation) \<Rightarrow>
    'o \<Rightarrow> ZF named_assignment \<Rightarrow> ZF named_assignment" where
  "paper_ZF_R_decode_assignment G D reps M g =
    paper_hom_assignment G (\<lambda>\<rho>. paper_ZF_rep_inverse (\<lambda>N. D N \<rho>) (reps \<rho>) M) g"

lemma paper_ZF_R_encode_assignment_apply:
  "paper_ZF_R_encode_assignment G reps M g n = map_option (paper_ZF_rep_encode (reps (G n)) M) (g n)"
  by (simp only: paper_ZF_R_encode_assignment_def paper_hom_assignment_def)

lemma paper_ZF_R_decode_assignment_apply:
  "paper_ZF_R_decode_assignment G D reps M g n =
    map_option (paper_ZF_rep_inverse (\<lambda>N. D N (G n)) (reps (G n)) M) (g n)"
  by (simp only: paper_ZF_R_decode_assignment_def paper_hom_assignment_def)

lemma paper_ZF_R_encode_assignment_domain:
  "dom (paper_ZF_R_encode_assignment G reps M g) = dom g"
  by (simp only: paper_ZF_R_encode_assignment_def paper_hom_assignment_domain)

lemma paper_ZF_R_decode_assignment_domain:
  "dom (paper_ZF_R_decode_assignment G D reps M g) = dom g"
  by (simp only: paper_ZF_R_decode_assignment_def paper_hom_assignment_domain)

lemma paper_ZF_R_encode_assignment_adequate_iff:
  "named_adequate (paper_ZF_R_encode_assignment G reps M g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_ZF_R_encode_assignment_domain)

lemma paper_ZF_R_decode_assignment_adequate_iff:
  "named_adequate (paper_ZF_R_decode_assignment G D reps M g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def paper_ZF_R_decode_assignment_domain)

lemma paper_ZF_R_encode_assignment_update:
  "paper_ZF_R_encode_assignment G reps M (g(n := Some a)) =
    (paper_ZF_R_encode_assignment G reps M g)(n := Some (paper_ZF_rep_encode (reps (G n)) M a))"
  by (simp only: paper_ZF_R_encode_assignment_def paper_hom_assignment_update)

lemma paper_ZF_R_decode_assignment_update:
  "paper_ZF_R_decode_assignment G D reps M (g(n := Some z)) =
    (paper_ZF_R_decode_assignment G D reps M g)(n := Some (paper_ZF_rep_inverse (\<lambda>N. D N (G n)) (reps (G n)) M z))"
  by (simp only: paper_ZF_R_decode_assignment_def paper_hom_assignment_update)

section \<open>The raw recursion has no represented values outside R\<close>

lemma paper_ZF_R_type_representation_nonR:
  assumes outside: "\<not> paper_R_type \<rho>"
  shows "paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho> =
    paper_ZF_empty_type_representation"
proof (cases \<rho>)
  case Ind
  with outside show ?thesis by simp
next
  case Prop
  with outside show ?thesis by simp
next
  case (Arr \<sigma> \<tau>)
  have nonR: "\<not> paper_R_type (Arr \<sigma> \<tau>)" using outside by (simp add: Arr)
  show ?thesis by (simp only: Arr paper_ZF_R_type_representation.simps if_not_P[OF nonR])
qed

lemma paper_ZF_R_type_representation_domain_nonR:
  assumes outside: "\<not> paper_R_type \<rho>"
  shows "paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>) M = Empty"
  by (simp only: paper_ZF_R_type_representation_nonR[OF outside]
    paper_ZF_empty_type_representation_def paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_type_representation_member_R:
  assumes member: "z \<in> explode
    (paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>) M)"
  shows "paper_R_type \<rho>"
proof (rule ccontr)
  assume outside: "\<not> paper_R_type \<rho>"
  have impossible: "Elem z Empty"
    using member by (simp only: paper_ZF_R_type_representation_domain_nonR[OF outside] explode_Elem)
  show False using impossible Empty[where x=z] by contradiction
qed

end
