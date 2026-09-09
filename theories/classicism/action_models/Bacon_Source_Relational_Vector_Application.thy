theory Bacon_Source_Relational_Vector_Application
  imports Bacon_Source_Relational_Vector_Syntax
begin

section \<open>Every stage of an R application vector is typed\<close>

text \<open>
  For σ₁,…,σₙ∈R, d∈Dσ₁→⋯→σₙ→t and aᵢ∈Dσᵢ,
  successive application yields d a₁⋯aₙ∈Dₜ.
  Source: Bacon–Dorr Definition 3.3, pp.45–46. Each remaining
  type vector ends in t and belongs to R. This supplies the explicit
  R arrow guard at every application, including when the tail is empty.
  The model premise is the independent R interface, not an F reduct.
\<close>

theorem paper_R_apply_vector_type:
  assumes model: "paper_R_bbk_model \<Sigma> G D J V"
    and types: "list_all paper_R_type \<sigma>s"
    and head: "d \<in> D (paper_type_vector \<sigma>s Prop)"
    and args: "paper_R_vector_args D \<sigma>s xs"
  shows "paper_R_apply_vector \<Sigma> G D J \<sigma>s d xs \<in> D Prop"
proof -
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  show ?thesis using types head args
  proof (induction \<sigma>s arbitrary: d xs)
    case Nil
    have empty: "xs = []" using Nil.prems(3) by simp
    show ?case using Nil.prems(2) by (simp only: empty paper_R_apply_vector.simps paper_type_vector.simps)
  next
    case (Cons \<sigma> \<sigma>s)
    obtain a ys where shape: "xs = a#ys" and am: "a \<in> D \<sigma>" and tail: "paper_R_vector_args D \<sigma>s ys"
      using Cons.prems(3) by (cases xs) auto
    have tail_types: "list_all paper_R_type \<sigma>s" using Cons.prems(1) by simp
    have vector_type: "paper_R_type (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
      by (rule iffD2[OF paper_R_vector_to_Prop_iff Cons.prems(1)])
    have rt: "paper_R_type (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
      using vector_type by (simp only: paper_type_vector.simps)
    have dt: "d \<in> D (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
      using Cons.prems(2) by (simp only: paper_type_vector.simps)
    have applied: "paper_R_application \<Sigma> G D J \<sigma> (paper_type_vector \<sigma>s Prop) d a \<in>
        D (paper_type_vector \<sigma>s Prop)"
      by (rule Model.paper_R_application_type[OF rt dt am])
    have result: "paper_R_apply_vector \<Sigma> G D J \<sigma>s
        (paper_R_application \<Sigma> G D J \<sigma> (paper_type_vector \<sigma>s Prop) d a) ys \<in> D Prop"
      by (rule Cons.IH[OF tail_types applied tail])
    show ?case by (simp only: shape paper_R_apply_vector.simps; rule result)
  qed
qed

section \<open>Independent R morphisms preserve finite application vectors\<close>

text \<open>
  hₜ(d a₁⋯aₙ)=(hσ₁→⋯→σₙ→t(d)) hσ₁(a₁)⋯hσₙ(aₙ).
  Source: the homomorphism equation of §3.3, p.49, applied to
  Definition 3.3's reconstructed application. Induction uses only the
  independent R scalar preservation theorem and its R type guards.
  Source and target value carriers may differ. No valuation preservation,
  Functionality, intension property, fullness or injectivity is claimed.
\<close>

theorem paper_R_apply_vector_morphism:
  assumes morphism: "paper_R_bbk_model_morphism \<Sigma> G D J V E K W h"
    and types: "list_all paper_R_type \<sigma>s"
    and head: "d \<in> D (paper_type_vector \<sigma>s Prop)"
    and args: "paper_R_vector_args D \<sigma>s xs"
  shows "h Prop (paper_R_apply_vector \<Sigma> G D J \<sigma>s d xs) =
    paper_R_apply_vector \<Sigma> G E K \<sigma>s
      (h (paper_type_vector \<sigma>s Prop) d) (paper_R_map_vector_args h \<sigma>s xs)"
proof -
  interpret Source: paper_R_bbk_model \<Sigma> G D J V
    by (rule paper_R_bbk_model_morphism_source[OF morphism])
  show ?thesis using types head args
  proof (induction \<sigma>s arbitrary: d xs)
    case Nil
    have empty: "xs = []" using Nil.prems(3) by simp
    show ?case by (simp only: empty paper_type_vector.simps paper_R_apply_vector.simps paper_R_map_vector_args_Nil)
  next
    case (Cons \<sigma> \<sigma>s)
    obtain a ys where shape: "xs = a#ys" and am: "a \<in> D \<sigma>" and tail: "paper_R_vector_args D \<sigma>s ys"
      using Cons.prems(3) by (cases xs) auto
    have tail_types: "list_all paper_R_type \<sigma>s" using Cons.prems(1) by simp
    have vector_type: "paper_R_type (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
      by (rule iffD2[OF paper_R_vector_to_Prop_iff Cons.prems(1)])
    have rt: "paper_R_type (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
      using vector_type by (simp only: paper_type_vector.simps)
    have dt: "d \<in> D (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
      using Cons.prems(2) by (simp only: paper_type_vector.simps)
    let ?b = "paper_R_application \<Sigma> G D J \<sigma> (paper_type_vector \<sigma>s Prop) d a"
    have bt: "?b \<in> D (paper_type_vector \<sigma>s Prop)"
      by (rule Source.paper_R_application_type[OF rt dt am])
    have step: "h (paper_type_vector \<sigma>s Prop) ?b =
      paper_R_application \<Sigma> G E K \<sigma> (paper_type_vector \<sigma>s Prop)
        (h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d) (h \<sigma> a)"
      by (rule paper_R_application_morphism[OF morphism rt dt am])
    have induction_step: "h Prop (paper_R_apply_vector \<Sigma> G D J \<sigma>s ?b ys) =
      paper_R_apply_vector \<Sigma> G E K \<sigma>s
        (h (paper_type_vector \<sigma>s Prop) ?b) (paper_R_map_vector_args h \<sigma>s ys)"
      by (rule Cons.IH[OF tail_types bt tail])
    show ?case by (simp only: shape paper_R_apply_vector.simps paper_R_map_vector_args_Cons
      paper_type_vector.simps induction_step step)
  qed
qed

end
