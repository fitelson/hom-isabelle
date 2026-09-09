theory Bacon_Book_ZF_Primitive_Truth
  imports Bacon_Book_ZF_Logical_Values
begin

section \<open>All-domain truth clauses for the actual primitive values\<close>

context book_full_C_canonical_frame
begin

theorem full_ZF_implication_truth:
  assumes ww: "w \<in> worlds" and pm: "p \<in> explode (full_ZF_D Prop w)"
    and qm: "q \<in> explode (full_ZF_D Prop w)"
  shows "full_ZF_value_truth w
    (full_ZF_app w Prop Prop (full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p) q) =
    (full_ZF_value_truth w p \<longrightarrow> full_ZF_value_truth w q)"
proof -
  interpret T: book_C_identity_world "fst w" G "snd w"
    by (rule book_full_C_world_identity_algebra[OF rich book_full_C_rooted_world_data(1)[OF ww]])
  let ?P = "full_ZF_j Prop w p"
  let ?Q = "full_ZF_j Prop w q"
  let ?K = "book_C_term_logical_value (fst w) G (snd w) SImp"
  let ?app = "book_C_term_app (fst w) G (snd w)"
  let ?V = "book_C_term_valuation (snd w)"
  have pt: "?P \<in> book_C_identity_domain (fst w) G (snd w) Prop" by (rule full_ZF_j_type[OF pm])
  have qt: "?Q \<in> book_C_identity_domain (fst w) G (snd w) Prop" by (rule full_ZF_j_type[OF qm])
  have kt: "?K \<in> book_C_identity_domain (fst w) G (snd w) (Arr Prop (Arr Prop Prop))"
    using T.term_logical_value_typed[of SImp] by simp
  have partial: "?app Prop (Arr Prop Prop) ?K ?P \<in> book_C_identity_domain (fst w) G (snd w) (Arr Prop Prop)"
    by (rule T.term_app_typed[OF kt pt])
  have first: "full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p =
    full_ZF_h (Arr Prop Prop) w (?app Prop (Arr Prop Prop) ?K ?P)"
    using full_ZF_app_h[OF ww kt pt]
    by (simp only: full_ZF_logical_value_def book_minimal_logical_type.simps full_ZF_hj[OF pm])
  have second: "full_ZF_app w Prop Prop (full_ZF_app w Prop (Arr Prop Prop) (full_ZF_logical_value w SImp) p) q =
    full_ZF_h Prop w (?app Prop Prop (?app Prop (Arr Prop Prop) ?K ?P) ?Q)"
    using full_ZF_app_h[OF ww partial qt] by (simp only: first full_ZF_hj[OF qm])
  have ptruth: "full_ZF_value_truth w p = ?V ?P"
    using full_ZF_h_proposition_truth[OF ww, of ?P] by (simp only: full_ZF_hj[OF pm])
  have qtruth: "full_ZF_value_truth w q = ?V ?Q"
    using full_ZF_h_proposition_truth[OF ww, of ?Q] by (simp only: full_ZF_hj[OF qm])
  show ?thesis by (simp only: second full_ZF_h_proposition_truth[OF ww] ptruth qtruth;
    rule T.term_implication_truth[OF pt qt])
qed

theorem full_ZF_forall_truth:
  assumes ww: "w \<in> worlds" and fm: "f \<in> explode (full_ZF_D (Arr \<sigma> Prop) w)"
  shows "full_ZF_value_truth w
    (full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f) =
    (\<forall>a\<in>explode (full_ZF_D \<sigma> w). full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f a))"
proof -
  have wf: "w \<in> book_full_C_canonical_worlds \<Sigma> B G" by (rule book_full_C_rooted_world_data(1)[OF ww])
  interpret T: book_C_identity_world "fst w" G "snd w" by (rule book_full_C_world_identity_algebra[OF rich wf])
  let ?F = "full_ZF_j (Arr \<sigma> Prop) w f"
  let ?K = "book_C_term_logical_value (fst w) G (snd w) (SBAll \<sigma>)"
  let ?app = "book_C_term_app (fst w) G (snd w)"
  let ?V = "book_C_term_valuation (snd w)"
  let ?D = "book_C_identity_domain (fst w) G (snd w)"
  have ft: "?F \<in> ?D (Arr \<sigma> Prop)" by (rule full_ZF_j_type[OF fm])
  have kt: "?K \<in> ?D (Arr (Arr \<sigma> Prop) Prop)"
    using T.term_logical_value_typed[of "SBAll \<sigma>"] by simp
  have application: "full_ZF_app w (Arr \<sigma> Prop) Prop (full_ZF_logical_value w (SBAll \<sigma>)) f =
    full_ZF_h Prop w (?app (Arr \<sigma> Prop) Prop ?K ?F)"
    using full_ZF_app_h[OF ww kt ft]
    by (simp only: full_ZF_logical_value_def book_minimal_logical_type.simps full_ZF_hj[OF fm])
  have pointwise: "full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f (full_ZF_h \<sigma> w A)) =
    ?V (?app \<sigma> Prop ?F A)" if am: "A \<in> ?D \<sigma>" for A
  proof -
    have evaluated: "full_ZF_app w \<sigma> Prop f (full_ZF_h \<sigma> w A) = full_ZF_h Prop w (?app \<sigma> Prop ?F A)"
      using full_ZF_app_h[OF ww ft am] by (simp only: full_ZF_hj[OF fm])
    show ?thesis by (simp only: evaluated full_ZF_h_proposition_truth[OF ww])
  qed
  have all_values: "(\<forall>a\<in>explode (full_ZF_D \<sigma> w). full_ZF_value_truth w (full_ZF_app w \<sigma> Prop f a)) =
    (\<forall>A\<in>?D \<sigma>. ?V (?app \<sigma> Prop ?F A))"
    by (simp add: full_ZF_D_elements pointwise)
  have witnesses: "book_closed_constant_witness_complete (fst w) G (snd w)"
    by (rule book_full_C_canonical_world_data(5)[OF wf])
  show ?thesis by (simp only: application full_ZF_h_proposition_truth[OF ww] all_values;
    rule T.term_forall_truth[OF witnesses ft])
qed

end

text \<open>
  Implication and ∀σ have their required pointwise truth conditions
  on every represented domain value. The proof decodes inputs,
  uses the actual graph-application equations and source membership
  clauses, and then transports truth through hᵗ. Quantification
  uses the entire h-image Dσ, not a proper selected subset.
  No target model predicate or target truth clause is assumed.
\<close>

end
