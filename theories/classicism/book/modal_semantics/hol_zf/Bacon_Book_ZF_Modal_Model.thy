theory Bacon_Book_ZF_Modal_Model
  imports Bacon_Book_ZF_Modal_Structure
begin

section \<open>Definition 18.1, independently of the canonical construction\<close>

locale book_ZF_modal_model = book_ZF_modal_structure W R root D i
  for W :: ZF and R :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" and root :: ZF
    and D :: book_ZF_domains and i :: book_ZF_counterparts +
  fixes signature :: "'c ssignature" and I :: "'c \<Rightarrow> otype \<Rightarrow> ZF"
  assumes k_member: "\<And>\<sigma> \<tau>. book_ZF_k W R D i root \<sigma> \<tau> \<in> explode (D (Arr \<sigma> (Arr \<tau> \<sigma>)) root)"
    and s_member: "\<And>\<sigma> \<tau> \<rho>. book_ZF_s W R D root \<sigma> \<tau> \<rho> \<in>
      explode (D (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>))) root)"
    and implication_member: "book_ZF_if_future W R D i root \<in> explode (D (Arr Prop (Arr Prop Prop)) root)"
    and universal_member: "\<And>\<sigma>. book_ZF_all W R D root \<sigma> \<in> explode (D (Arr (Arr \<sigma> Prop) Prop) root)"
    and identity_member: "\<And>\<sigma>. book_ZF_eq W R D i root \<sigma> \<in> explode (D (Arr \<sigma> (Arr \<sigma> Prop)) root)"
    and constants: "\<And>c \<sigma>. c \<in> signature \<sigma> \<Longrightarrow> I c \<sigma> \<in> explode (D \<sigma> root)"
begin

theorem logical_root_type:
  "book_ZF_logical_root W R D i root l \<in> explode (D (book_minimal_logical_type l) root)"
  by (cases l; simp only: book_ZF_logical_root.simps book_minimal_logical_type.simps;
    rule implication_member universal_member)

end

text \<open>
  The model's root operations are the explicitly defined function
  graphs, not freely chosen witnesses with an assumed behavior.
  The two primitive logical interpretations are prescribed by
  book_ZF_logical_root; I interprets only the nonlogical signature.
  Root k/s/connective/quantifier/identity membership is exactly the
  displayed form of Definition 18.1(3). Their counterparts and the
  all-world membership formulation will be derived separately.

  Implication retains the explicitly documented future-domain
  restriction. No canonical-world predicate, source proof judgment,
  name-cardinality condition or total interpreter occurs in this
  independent definition. No false-proposition or extra nonemptiness
  field is silently inserted. Generic interpretation and soundness
  require further proofs, not an appeal to this definition alone.
\<close>

end
