theory Bacon_PP_ZF_Exact_L2_Child_Variation_Semantics
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Immediate_Successor"
begin

lemma pp_e_HO_child_variation_raw:
  assumes P: "Elem P (pp_e_domain Prop)"
  shows "pp_e_holds
      ((pp_e_closed_den pp_e_HO_child_variation_term) \<acute> P) w
    \<longleftrightarrow>
      (\<exists>C. Elem C (pp_e_domain Prop) \<and>
        pp_e_holds
          ((pp_e_closed_den pp_e_HO_atom_term) \<acute> C) w \<and>
        pp_e_holds C w \<and>
        (\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> pp_e_holds P v)))) \<and>
        (\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> \<not> pp_e_holds P v)))))"
  using P
  by (simp add: pp_e_closed_den_def
      pp_e_HO_child_variation_term_def Lambda_app)

lemma pp_e_HO_child_positive_iff:
  assumes C: "Elem C (pp_e_domain Prop)"
    and P: "Elem P (pp_e_domain Prop)"
    and C_atom: "pp_e_atom_at w C"
    and C_true: "pp_e_holds C w"
  shows "(\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
      pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> pp_e_holds P v))))
    \<longleftrightarrow> (\<exists>b. pp_e_holds P (w @ [b]))"
proof
  assume left:
      "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
        pp_e_holds
          (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
            \<acute> Q) w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          (pp_e_holds Q v \<longleftrightarrow>
            (pp_e_holds Q v \<and> pp_e_holds P v)))"
  then obtain Q where Q: "Elem Q (pp_e_domain Prop)"
    and immediate:
      "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
    and included:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> pp_e_holds P v))"
    by blast
  have child: "pp_e_child_atom_at w Q"
    using pp_e_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] immediate by blast
  then obtain b where unique:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow> v = w @ [b])"
    unfolding pp_e_child_atom_at_def by blast
  have future: "prefix w (w @ [b])"
    by simp
  have Q_child: "pp_e_holds Q (w @ [b])"
    using unique future by simp
  have P_child: "pp_e_holds P (w @ [b])"
    using included future Q_child by blast
  show "\<exists>b. pp_e_holds P (w @ [b])"
    using P_child by blast
next
  assume right: "\<exists>b. pp_e_holds P (w @ [b])"
  then obtain b where P_child: "pp_e_holds P (w @ [b])"
    by blast
  let ?Q = "pp_n_prop (\<lambda>x. x = w @ [b])"
  have Q: "Elem ?Q (pp_e_domain Prop)"
    using pp_n_prop_in_power by simp
  have child: "pp_e_child_atom_at w ?Q"
    unfolding pp_e_child_atom_at_def
    by (intro exI[of _ b] allI impI) simp
  have immediate:
      "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> ?Q) w"
    using pp_e_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] child by blast
  have included:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds ?Q v \<longleftrightarrow>
          (pp_e_holds ?Q v \<and> pp_e_holds P v))"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    show "pp_e_holds ?Q v \<longleftrightarrow>
        (pp_e_holds ?Q v \<and> pp_e_holds P v)"
      using P_child by auto
  qed
  show "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
      pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> pp_e_holds P v)))"
    using Q immediate included by blast
qed

lemma pp_e_HO_child_negative_iff:
  assumes C: "Elem C (pp_e_domain Prop)"
    and P: "Elem P (pp_e_domain Prop)"
    and C_atom: "pp_e_atom_at w C"
    and C_true: "pp_e_holds C w"
  shows "(\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
      pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> \<not> pp_e_holds P v))))
    \<longleftrightarrow> (\<exists>b. \<not> pp_e_holds P (w @ [b]))"
proof
  assume left:
      "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
        pp_e_holds
          (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
            \<acute> Q) w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          (pp_e_holds Q v \<longleftrightarrow>
            (pp_e_holds Q v \<and> \<not> pp_e_holds P v)))"
  then obtain Q where Q: "Elem Q (pp_e_domain Prop)"
    and immediate:
      "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
    and excluded:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> \<not> pp_e_holds P v))"
    by blast
  have child: "pp_e_child_atom_at w Q"
    using pp_e_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] immediate by blast
  then obtain b where unique:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow> v = w @ [b])"
    unfolding pp_e_child_atom_at_def by blast
  have future: "prefix w (w @ [b])"
    by simp
  have Q_child: "pp_e_holds Q (w @ [b])"
    using unique future by simp
  have not_P_child: "\<not> pp_e_holds P (w @ [b])"
    using excluded future Q_child by blast
  show "\<exists>b. \<not> pp_e_holds P (w @ [b])"
    using not_P_child by blast
next
  assume right: "\<exists>b. \<not> pp_e_holds P (w @ [b])"
  then obtain b where not_P_child:
      "\<not> pp_e_holds P (w @ [b])"
    by blast
  let ?Q = "pp_n_prop (\<lambda>x. x = w @ [b])"
  have Q: "Elem ?Q (pp_e_domain Prop)"
    using pp_n_prop_in_power by simp
  have child: "pp_e_child_atom_at w ?Q"
    unfolding pp_e_child_atom_at_def
    by (intro exI[of _ b] allI impI) simp
  have immediate:
      "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> ?Q) w"
    using pp_e_HO_immediate_iff_child_atom[
      OF C Q C_atom C_true] child by blast
  have excluded:
      "\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds ?Q v \<longleftrightarrow>
          (pp_e_holds ?Q v \<and> \<not> pp_e_holds P v))"
  proof (intro allI impI)
    fix v
    assume "prefix w v"
    show "pp_e_holds ?Q v \<longleftrightarrow>
        (pp_e_holds ?Q v \<and> \<not> pp_e_holds P v)"
      using not_P_child by auto
  qed
  show "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
      pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        (pp_e_holds Q v \<longleftrightarrow>
          (pp_e_holds Q v \<and> \<not> pp_e_holds P v)))"
    using Q immediate excluded by blast
qed

theorem pp_e_HO_child_variation_holds:
  assumes P: "Elem P (pp_e_domain Prop)"
  shows "pp_e_holds
      ((pp_e_closed_den pp_e_HO_child_variation_term) \<acute> P) w
    \<longleftrightarrow>
      ((\<exists>n. pp_e_holds P (w @ [n])) \<and>
       (\<exists>n. \<not> pp_e_holds P (w @ [n])))"
proof -
  let ?C = "pp_n_prop (\<lambda>x. x = w)"
  have C: "Elem ?C (pp_e_domain Prop)"
    using pp_n_prop_in_power by simp
  have C_atom: "pp_e_atom_at w ?C"
    unfolding pp_e_atom_at_def
    by (intro exI[of _ w] conjI allI impI) simp_all
  have C_true: "pp_e_holds ?C w"
    by simp
  have atom_term:
      "pp_e_holds
        ((pp_e_closed_den pp_e_HO_atom_term) \<acute> ?C) w"
    using pp_e_HO_atom_holds[OF C, of w] C_atom by blast
  have existential:
      "pp_e_holds
        ((pp_e_closed_den pp_e_HO_child_variation_term) \<acute> P) w
      \<longleftrightarrow>
        ((\<exists>b. pp_e_holds P (w @ [b])) \<and>
         (\<exists>b. \<not> pp_e_holds P (w @ [b])))"
  proof
    assume term_holds:
        "pp_e_holds
          ((pp_e_closed_den pp_e_HO_child_variation_term) \<acute> P) w"
    obtain C' where C': "Elem C' (pp_e_domain Prop)"
      and C'_atom_term:
        "pp_e_holds
          ((pp_e_closed_den pp_e_HO_atom_term) \<acute> C') w"
      and C'_true: "pp_e_holds C' w"
      and positive:
        "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C')
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> pp_e_holds P v)))"
      and negative:
        "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C')
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> \<not> pp_e_holds P v)))"
      using pp_e_HO_child_variation_raw[OF P, of w] term_holds by blast
    have C'_atom: "pp_e_atom_at w C'"
      using pp_e_HO_atom_holds[OF C', of w] C'_atom_term by blast
    have pos: "\<exists>b. pp_e_holds P (w @ [b])"
      using pp_e_HO_child_positive_iff[
        OF C' P C'_atom C'_true] positive by blast
    have neg: "\<exists>b. \<not> pp_e_holds P (w @ [b])"
      using pp_e_HO_child_negative_iff[
        OF C' P C'_atom C'_true] negative by blast
    show "(\<exists>b. pp_e_holds P (w @ [b])) \<and>
        (\<exists>b. \<not> pp_e_holds P (w @ [b]))"
      using pos neg by blast
  next
    assume both:
        "(\<exists>b. pp_e_holds P (w @ [b])) \<and>
         (\<exists>b. \<not> pp_e_holds P (w @ [b]))"
    have positive:
        "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> ?C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> pp_e_holds P v)))"
      using pp_e_HO_child_positive_iff[
        OF C P C_atom C_true] both by blast
    have negative:
        "\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
          pp_e_holds
            (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> ?C)
              \<acute> Q) w \<and>
          (\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds Q v \<longleftrightarrow>
              (pp_e_holds Q v \<and> \<not> pp_e_holds P v)))"
      using pp_e_HO_child_negative_iff[
        OF C P C_atom C_true] both by blast
    have raw_right:
        "\<exists>C. Elem C (pp_e_domain Prop) \<and>
          pp_e_holds
            ((pp_e_closed_den pp_e_HO_atom_term) \<acute> C) w \<and>
          pp_e_holds C w \<and>
          (\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
            pp_e_holds
              (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
                \<acute> Q) w \<and>
            (\<forall>v. prefix w v \<longrightarrow>
              (pp_e_holds Q v \<longleftrightarrow>
                (pp_e_holds Q v \<and> pp_e_holds P v)))) \<and>
          (\<exists>Q. Elem Q (pp_e_domain Prop) \<and>
            pp_e_holds
              (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
                \<acute> Q) w \<and>
            (\<forall>v. prefix w v \<longrightarrow>
              (pp_e_holds Q v \<longleftrightarrow>
                (pp_e_holds Q v \<and> \<not> pp_e_holds P v))))"
      using C atom_term C_true positive negative by blast
    show "pp_e_holds
        ((pp_e_closed_den pp_e_HO_child_variation_term) \<acute> P) w"
      using pp_e_HO_child_variation_raw[OF P, of w] raw_right by blast
  qed
  show ?thesis
    by (rule existential)
qed

theorem pp_e_raw_operator_HO_child_variation:
  "pp_e_raw_operator
      (pp_e_closed_den pp_e_HO_child_variation_term) = pp_e_child_variation"
proof (rule ext, rule set_eqI)
  fix P i
  have P_domain: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain by simp
  show "i \<in> pp_e_raw_operator
        (pp_e_closed_den pp_e_HO_child_variation_term) P
      \<longleftrightarrow> i \<in> pp_e_child_variation P"
    unfolding pp_e_raw_operator_def
      pp_n_bacon_extract_def
      pp_e_child_variation_def
    using pp_e_HO_child_variation_holds[OF P_domain, of "rev i"]
    by simp
qed

theorem pp_e_child_variation_in_exact_stock:
  "pp_e_child_variation \<in> pp_e_exact_operator_stock"
proof -
  have denotation:
      "pp_e_raw_operator
        (pp_e_closed_den pp_e_HO_child_variation_term)
        \<in> pp_e_exact_operator_stock"
    using pp_e_HO_child_variation_terms_typed(3)
      pp_e_HO_child_variation_terms_logical(3)
    by (rule pp_e_exact_operator_stockI)
  show ?thesis
    using denotation pp_e_raw_operator_HO_child_variation by simp
qed

end
