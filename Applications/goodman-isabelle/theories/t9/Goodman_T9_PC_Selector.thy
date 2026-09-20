theory Goodman_T9_PC_Selector
  imports Goodman_T9_Native_Purity
begin

section \<open>Full external PC at the type of pure unary operators\<close>

definition gi_T9_full_unary_PC where
  "gi_T9_full_unary_PC C \<longleftrightarrow>
    (\<forall>A. A \<subseteq> gi_T9_root_pure C gb_unary \<longrightarrow>
      (\<exists>H\<in>gi_T9_root_pure C gi_T9_pred.
        \<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
          (pp_e_holds (H \<acute> X) [] \<longleftrightarrow> X \<in> A)))"

definition gi_T9_PC_witness where
  "gi_T9_PC_witness C A = (SOME H.
    H \<in> gi_T9_root_pure C gi_T9_pred \<and>
      (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
        (pp_e_holds (H \<acute> X) [] \<longleftrightarrow> X \<in> A)))"

definition gi_T9_PC_lowered where
  "gi_T9_PC_lowered C A = gi_T9_lower_value C (gi_T9_PC_witness C A)"

text \<open>
  PC here ranges over EVERY external HOL subset A of root-pure unary
  values, and its witness H has type (t→t)→t. It is one type instance
  of the source's full PC requirement, not comprehension over only
  Henkin-representable subsets. The lowered value has type t→t instead.
\<close>

lemma gi_T9_PC_witness_spec:
  assumes pc: "gi_T9_full_unary_PC C" and subset: "A \<subseteq> gi_T9_root_pure C gb_unary"
  shows "gi_T9_PC_witness C A \<in> gi_T9_root_pure C gi_T9_pred"
    and "Elem X (pp_e_domain gb_unary) \<Longrightarrow>
      (pp_e_holds (gi_T9_PC_witness C A \<acute> X) [] \<longleftrightarrow> X \<in> A)"
proof -
  have existence: "\<exists>H. H \<in> gi_T9_root_pure C gi_T9_pred \<and>
      (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
        (pp_e_holds (H \<acute> X) [] \<longleftrightarrow> X \<in> A))"
    using pc subset unfolding gi_T9_full_unary_PC_def by blast
  have chosen: "gi_T9_PC_witness C A \<in> gi_T9_root_pure C gi_T9_pred \<and>
      (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
        (pp_e_holds (gi_T9_PC_witness C A \<acute> X) [] \<longleftrightarrow> X \<in> A))"
    unfolding gi_T9_PC_witness_def by (rule someI_ex[OF existence])
  show "gi_T9_PC_witness C A \<in> gi_T9_root_pure C gi_T9_pred" using chosen by blast
  show "Elem X (pp_e_domain gb_unary) \<Longrightarrow>
      (pp_e_holds (gi_T9_PC_witness C A \<acute> X) [] \<longleftrightarrow> X \<in> A)"
    using chosen by blast
qed

context gi_T9_native_purity
begin

theorem gi_T9_PC_lowered_pure:
  assumes pc: "gi_T9_full_unary_PC C" and subset: "A \<subseteq> gi_T9_root_pure C gb_unary"
  shows "gi_T9_PC_lowered C A \<in> gi_T9_root_pure C gb_unary"
  unfolding gi_T9_PC_lowered_def
  by (rule gi_T9_lower_value_pure[OF gi_T9_PC_witness_spec(1)[OF pc subset]])

theorem gi_T9_PC_lowered_spec:
  assumes pc: "gi_T9_full_unary_PC C" and subset: "A \<subseteq> gi_T9_root_pure C gb_unary"
    and pm: "Elem p (pp_e_domain Prop)"
  shows "pp_e_holds (gi_T9_PC_lowered C A \<acute> p) [] \<longleftrightarrow>
    (\<exists>X\<in>A. \<exists>q. Elem q (pp_e_domain Prop) \<and>
      pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> p = X \<acute> q)"
proof -
  let ?H = "gi_T9_PC_witness C A"
  have hm: "Elem ?H (pp_e_domain gi_T9_pred)"
    using gi_T9_PC_witness_spec(1)[OF pc subset] unfolding gi_T9_root_pure_def by blast
  have calculation: "pp_e_holds (gi_T9_PC_lowered C A \<acute> p) [] \<longleftrightarrow>
    (\<exists>X. Elem X (pp_e_domain gb_unary) \<and>
      (\<exists>q. Elem q (pp_e_domain Prop) \<and>
        gi_M1_exact_Pure C gb_unary [] X \<and> pp_e_holds (?H \<acute> X) [] \<and>
        pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> pp_e_eqv Prop [] p (X \<acute> q)))"
    unfolding gi_T9_PC_lowered_def by (rule gi_T9_lower_value_holds[OF hm pm])
  show ?thesis
  proof
    assume true: "pp_e_holds (gi_T9_PC_lowered C A \<acute> p) []"
    obtain X q where xm: "Elem X (pp_e_domain gb_unary)" and qm: "Elem q (pp_e_domain Prop)"
      and selected: "pp_e_holds (?H \<acute> X) []" and fp: "pp_e_holds (gi_T9_J_value C \<acute> q) []"
      and related: "pp_e_eqv Prop [] p (X \<acute> q)" using true calculation by blast
    have xa: "X \<in> A" using selected gi_T9_PC_witness_spec(2)[OF pc subset xm] by blast
    have xq: "Elem (X \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm qm])
    have same: "p = X \<acute> q" using related by (simp only: gi_exact_root_eqv[OF pm xq])
    show "\<exists>X\<in>A. \<exists>q. Elem q (pp_e_domain Prop) \<and>
        pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> p = X \<acute> q"
      by (rule bexI[where x=X], rule exI[where x=q]) (use xa qm fp same in auto)
  next
    assume "\<exists>X\<in>A. \<exists>q. Elem q (pp_e_domain Prop) \<and>
        pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> p = X \<acute> q"
    then obtain X q where xa: "X \<in> A" and qm: "Elem q (pp_e_domain Prop)"
      and fp: "pp_e_holds (gi_T9_J_value C \<acute> q) []" and same: "p = X \<acute> q" by blast
    have pure: "X \<in> gi_T9_root_pure C gb_unary" by (rule subsetD[OF subset xa])
    have xm: "Elem X (pp_e_domain gb_unary)" and xp: "gi_M1_exact_Pure C gb_unary [] X"
      using pure unfolding gi_T9_root_pure_def by auto
    have selected: "pp_e_holds (?H \<acute> X) []" using xa gi_T9_PC_witness_spec(2)[OF pc subset xm] by blast
    have xq: "Elem (X \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm qm])
    have related: "pp_e_eqv Prop [] p (X \<acute> q)"
      by (simp only: gi_exact_root_eqv[OF pm xq]; rule same)
    have rhs: "\<exists>X. Elem X (pp_e_domain gb_unary) \<and>
      (\<exists>q. Elem q (pp_e_domain Prop) \<and>
        gi_M1_exact_Pure C gb_unary [] X \<and> pp_e_holds (?H \<acute> X) [] \<and>
        pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> pp_e_eqv Prop [] p (X \<acute> q))"
      by (rule exI[where x=X], rule conjI[OF xm], rule exI[where x=q])
        (use qm xp selected fp related in blast)
    show "pp_e_holds (gi_T9_PC_lowered C A \<acute> p) []" using calculation rhs by blast
  qed
qed

end

text \<open>
  This is the higher-order-to-unary PC bridge with actual purity and
  evaluation proved from native axioms. The next step takes A to be a
  union of kinds and uses L2 and a fun′ witness to derive the counting
  theorem's selector specification. No cardinal inequality, existence
  of a PP/PC model, or completeness of that later step is asserted here.
\<close>

end
