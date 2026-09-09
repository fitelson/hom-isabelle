theory Bacon_Source_Relational_Intension_Tail
  imports Bacon_Source_Relational_Intension Bacon_Source_Relational_Subcategory
begin

section \<open>Later evaluation transports the first argument as well\<close>

text \<open>
  Let h:M→N, a∈Nσ, and k:N→P. Evaluating the remaining
  relation after applying h(d) to a agrees with evaluating d along
  k∘h at the tuple ⟨kσ(a),x₁,…,xₙ⟩.
  Source: Bacon–Dorr Definitions 3.3 and 3.10, pp.45–46 and
  p.50, using the homomorphism equation on p.49.

  The argument a is an arbitrary element of the target domain, not
  necessarily the image of an M-element. A subsequent arrow transports
  it; it is not kept fixed across worlds. Only the independent R
  model and morphism laws are used.
\<close>

lemma paper_R_transported_tail_application:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and types: "list_all paper_R_type (\<sigma>#\<sigma>s)"
    and dm: "d \<in> paper_bbk_domain M (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
    and first: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
    and second: "k \<in> Arrows" and meeting: "paper_arrow_target h = paper_arrow_source k"
  shows "paper_R_apply_vector \<Sigma> G (paper_bbk_domain (paper_arrow_target k))
      (paper_bbk_denote (paper_arrow_target k)) \<sigma>s
      (paper_arrow_map k (paper_type_vector \<sigma>s Prop)
        (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
          (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
          (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) d) a)) xs =
    paper_R_apply_vector \<Sigma> G (paper_bbk_domain (paper_arrow_target k))
      (paper_bbk_denote (paper_arrow_target k)) (\<sigma>#\<sigma>s)
      (paper_arrow_map (paper_typed_compose paper_bbk_domain k h)
        (paper_type_vector (\<sigma>#\<sigma>s) Prop) d) (paper_arrow_map k \<sigma> a # xs)"
proof -
  have selected: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    by (rule category)
  have hf: "h \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    by (rule paper_R_bbk_subcategory_arrow[OF selected first])
  have kf: "k \<in> paper_R_bbk_arrows \<Sigma> G Obj"
    by (rule paper_R_bbk_subcategory_arrow[OF selected second])
  have km: "paper_R_bbk_model_morphism \<Sigma> G
    (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
    (paper_bbk_valuation (paper_arrow_target h))
    (paper_bbk_domain (paper_arrow_target k)) (paper_bbk_denote (paper_arrow_target k))
    (paper_bbk_valuation (paper_arrow_target k)) (paper_arrow_map k)"
    using paper_R_bbk_arrows_morphism[OF kf]
    unfolding paper_R_bbk_data_morphism_def by (simp only: meeting)
  have vector_type: "paper_R_type (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
    by (rule iffD2[OF paper_R_vector_to_Prop_iff types])
  have rt: "paper_R_type (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using vector_type by (simp only: paper_type_vector.simps)
  have source_member: "d \<in> paper_bbk_domain (paper_arrow_source h) (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    using dm by (simp only: source paper_type_vector.simps)
  have head: "paper_arrow_map h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d \<in>
    paper_bbk_domain (paper_arrow_target h) (Arr \<sigma> (paper_type_vector \<sigma>s Prop))"
    by (rule paper_typed_arrows_map[OF paper_R_bbk_arrows_typed[OF hf] source_member])
  have application: "paper_arrow_map k (paper_type_vector \<sigma>s Prop)
      (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
        (paper_arrow_map h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d) a) =
    paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target k))
      (paper_bbk_denote (paper_arrow_target k)) \<sigma> (paper_type_vector \<sigma>s Prop)
      (paper_arrow_map k (Arr \<sigma> (paper_type_vector \<sigma>s Prop))
        (paper_arrow_map h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d)) (paper_arrow_map k \<sigma> a)"
    by (rule paper_R_application_morphism[OF km rt head argument])
  have composite_head: "paper_arrow_map (paper_typed_compose paper_bbk_domain k h)
      (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d =
    paper_arrow_map k (Arr \<sigma> (paper_type_vector \<sigma>s Prop))
      (paper_arrow_map h (Arr \<sigma> (paper_type_vector \<sigma>s Prop)) d)"
    by (rule paper_typed_compose_map_on[
      where D=paper_bbk_domain and f=h and \<sigma>="Arr \<sigma> (paper_type_vector \<sigma>s Prop)", OF source_member])
  show ?thesis
    by (simp only: paper_R_apply_vector.simps paper_type_vector.simps composite_head application)
qed

section \<open>Equal intensions give equal transported tail intensions\<close>

text \<open>
  If int𝒞M(d)=int𝒞M(e) at σ→σ₁→⋯→σₙ→t, then for
  each h:M→N and each a∈Nσ, the tail relations h(d)a and
  h(e)a have equal intensions at N. A test at k:N→P is converted
  into the original test at k∘h using ⟨kσ(a),x₁,…,xₙ⟩.
  Every later arrow and every typed tail tuple remains quantified.
  This is equality propagation, not an injectivity or fullness theorem.
\<close>

theorem paper_R_intension_transported_tail:
  fixes \<Sigma> :: "'c ssignature" and d :: 'v
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and types: "list_all paper_R_type (\<sigma>#\<sigma>s)"
    and dm: "d \<in> paper_bbk_domain M (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
    and em: "e \<in> paper_bbk_domain M (paper_type_vector (\<sigma>#\<sigma>s) Prop)"
    and equal: "paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<sigma>s) d =
      paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<sigma>s) e"
    and arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    and argument: "a \<in> paper_bbk_domain (paper_arrow_target h) \<sigma>"
  shows "paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s
      (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
        (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) d) a) =
    paper_R_intension_on \<Sigma> G Arrows (paper_arrow_target h) \<sigma>s
      (paper_R_application \<Sigma> G (paper_bbk_domain (paper_arrow_target h))
        (paper_bbk_denote (paper_arrow_target h)) \<sigma> (paper_type_vector \<sigma>s Prop)
        (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) e) a)"
proof -
  interpret Category: paper_category Obj Arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF category])
  let ?N = "paper_arrow_target h"
  let ?tail = "\<lambda>x. paper_R_application \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N)
    \<sigma> (paper_type_vector \<sigma>s Prop) (paper_arrow_map h (paper_type_vector (\<sigma>#\<sigma>s) Prop) x) a"
  show ?thesis
  proof (rule set_eqI)
    fix p :: "('c,'v) paper_bbk_arrow \<times> 'v list"
    obtain k xs where pair: "p = (k,xs)" by (cases p) auto
    show "(p \<in> paper_R_intension_on \<Sigma> G Arrows ?N \<sigma>s (?tail d)) =
      (p \<in> paper_R_intension_on \<Sigma> G Arrows ?N \<sigma>s (?tail e))"
    proof (cases "k \<in> Arrows \<and> paper_arrow_source k = ?N \<and>
      paper_R_vector_args (paper_bbk_domain (paper_arrow_target k)) \<sigma>s xs")
      case True
      have ka: "k \<in> Arrows" and origin: "paper_arrow_source k = ?N"
        and tuple: "paper_R_vector_args (paper_bbk_domain (paper_arrow_target k)) \<sigma>s xs"
        using True by blast+
      have meeting: "?N = paper_arrow_source k" by (rule origin[symmetric])
      have selected: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
        by (rule category)
      have ktyped: "k \<in> paper_typed_arrows Obj paper_bbk_domain"
        by (rule paper_R_bbk_arrows_typed[OF paper_R_bbk_subcategory_arrow[OF selected ka]])
      have a_source: "a \<in> paper_bbk_domain (paper_arrow_source k) \<sigma>"
        using argument by (simp only: origin)
      have a_target: "paper_arrow_map k \<sigma> a \<in> paper_bbk_domain (paper_arrow_target k) \<sigma>"
        by (rule paper_typed_arrows_map[OF ktyped a_source])
      let ?c = "paper_typed_compose paper_bbk_domain k h"
      have composite: "?c \<in> Arrows" by (rule Category.compose_arrow[OF arrow ka meeting])
      have big_tuple: "paper_R_vector_args (paper_bbk_domain (paper_arrow_target k))
        (\<sigma>#\<sigma>s) (paper_arrow_map k \<sigma> a # xs)"
        by (simp only: paper_R_vector_args_Cons; rule conjI[OF a_target tuple])
      have original_test: "((?c, paper_arrow_map k \<sigma> a # xs) \<in>
          paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<sigma>s) d) =
        ((?c, paper_arrow_map k \<sigma> a # xs) \<in>
          paper_R_intension_on \<Sigma> G Arrows M (\<sigma>#\<sigma>s) e)"
        by (simp only: equal)
      have full_truth: "paper_bbk_valuation (paper_arrow_target k)
          (paper_R_apply_vector \<Sigma> G (paper_bbk_domain (paper_arrow_target k))
            (paper_bbk_denote (paper_arrow_target k)) (\<sigma>#\<sigma>s)
            (paper_arrow_map ?c (paper_type_vector (\<sigma>#\<sigma>s) Prop) d)
            (paper_arrow_map k \<sigma> a # xs)) =
        paper_bbk_valuation (paper_arrow_target k)
          (paper_R_apply_vector \<Sigma> G (paper_bbk_domain (paper_arrow_target k))
            (paper_bbk_denote (paper_arrow_target k)) (\<sigma>#\<sigma>s)
            (paper_arrow_map ?c (paper_type_vector (\<sigma>#\<sigma>s) Prop) e)
            (paper_arrow_map k \<sigma> a # xs))"
        using original_test
        by (simp only: paper_R_intension_on_member composite paper_typed_compose_endpoints source big_tuple; simp)
      show ?thesis
        by (simp only: pair paper_R_intension_on_member ka origin tuple
          paper_R_transported_tail_application[OF category types dm arrow source argument ka meeting]
          paper_R_transported_tail_application[OF category types em arrow source argument ka meeting]
          full_truth; simp)
    next
      case False
      show ?thesis using False by (auto simp only: pair paper_R_intension_on_member)
    qed
  qed
qed

end
