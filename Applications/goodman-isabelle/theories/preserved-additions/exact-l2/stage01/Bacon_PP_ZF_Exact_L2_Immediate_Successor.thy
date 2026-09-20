theory Bacon_PP_ZF_Exact_L2_Immediate_Successor
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Child_Atom"
begin

lemma pp_e_shift_HO_immediate_term[simp]:
  "shift pp_e_HO_immediate_term = pp_e_HO_immediate_term"
  by (simp add: shift_def pp_e_HO_immediate_term_def
      ObjDiamond_def ObjBox_def ObjFalse_def ObjTrue_def)

lemma pp_e_eval_HO_immediate_term_extend[simp]:
  "pp_e_eval C (extend_env x \<rho>) pp_e_HO_immediate_term =
    pp_e_eval C \<rho> pp_e_HO_immediate_term"
  using pp_e_eval_shift[of C x \<rho> pp_e_HO_immediate_term]
  by simp

lemma pp_e_HO_immediate_holds:
  assumes C: "Elem C (pp_e_domain Prop)"
    and Q: "Elem Q (pp_e_domain Prop)"
  shows "pp_e_holds
      (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
        \<acute> Q) w
    \<longleftrightarrow>
      pp_e_atom_at w Q \<and>
      \<not> pp_e_holds Q w \<and>
      (\<forall>v. prefix w v \<longrightarrow>
        ((\<exists>u. prefix v u \<and> pp_e_holds Q u)
          \<longleftrightarrow>
         pp_e_holds C v \<or> pp_e_holds Q v))"
  using C Q pp_e_HO_atom_holds[OF Q, of w]
  by (simp add: pp_e_closed_den_def
      pp_e_HO_immediate_term_def ObjDiamond_def ObjBox_def
      ObjFalse_def ObjTrue_def Lambda_app
      pp_e_closed_den_def)

definition pp_e_child_atom_at :: "nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_e_child_atom_at w Q \<longleftrightarrow>
    (\<exists>b. \<forall>u. prefix w u \<longrightarrow>
      (pp_e_holds Q u \<longleftrightarrow> u = w @ [b]))"

lemma pp_e_atom_at_true_iff:
  assumes atom: "pp_e_atom_at w C"
    and true: "pp_e_holds C w"
  shows "\<forall>u. prefix w u \<longrightarrow>
    (pp_e_holds C u \<longleftrightarrow> u = w)"
proof -
  obtain v where v: "prefix w v"
    and unique: "\<forall>u. prefix w u \<longrightarrow>
      (pp_e_holds C u \<longleftrightarrow> u = v)"
    using atom unfolding pp_e_atom_at_def by blast
  have "w = v"
    using unique true by simp
  then show ?thesis
    using unique by simp
qed

lemma pp_e_child_atom_at_is_atom:
  assumes child: "pp_e_child_atom_at w Q"
  shows "pp_e_atom_at w Q"
proof -
  obtain b where unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_e_holds Q u \<longleftrightarrow> u = w @ [b])"
    using child unfolding pp_e_child_atom_at_def by blast
  show ?thesis
    unfolding pp_e_atom_at_def
  proof (intro exI[of _ "w @ [b]"] conjI)
    show "prefix w (w @ [b])"
      by simp
  next
    show "\<forall>u. prefix w u \<longrightarrow>
      (pp_e_holds Q u \<longleftrightarrow> u = w @ [b])"
      by (rule unique)
  qed
qed

theorem pp_e_HO_immediate_iff_child_atom:
  assumes C: "Elem C (pp_e_domain Prop)"
    and Q: "Elem Q (pp_e_domain Prop)"
    and C_atom: "pp_e_atom_at w C"
    and C_true: "pp_e_holds C w"
  shows "pp_e_holds
      (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
        \<acute> Q) w
    \<longleftrightarrow> pp_e_child_atom_at w Q"
proof -
  have C_unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_e_holds C u \<longleftrightarrow> u = w)"
    using pp_e_atom_at_true_iff[OF C_atom C_true] .
  have raw:
      "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w
      \<longleftrightarrow>
        pp_e_atom_at w Q \<and>
        \<not> pp_e_holds Q w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_e_holds Q u)
            \<longleftrightarrow>
           pp_e_holds C v \<or> pp_e_holds Q v))"
    using pp_e_HO_immediate_holds[OF C Q, of w] .
  show ?thesis
  proof
    assume immediate:
        "pp_e_holds
          (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
            \<acute> Q) w"
    have conjuncts:
        "pp_e_atom_at w Q \<and>
        \<not> pp_e_holds Q w \<and>
        (\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_e_holds Q u)
            \<longleftrightarrow>
           pp_e_holds C v \<or> pp_e_holds Q v))"
      using raw immediate by blast
    have Q_atom: "pp_e_atom_at w Q"
      using conjuncts by blast
    have Q_not_w: "\<not> pp_e_holds Q w"
      using conjuncts by blast
    have diamond:
        "\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_e_holds Q u)
            \<longleftrightarrow>
           pp_e_holds C v \<or> pp_e_holds Q v)"
      using conjuncts by blast
    obtain v where v_future: "prefix w v"
      and Q_unique:
        "\<forall>u. prefix w u \<longrightarrow>
          (pp_e_holds Q u \<longleftrightarrow> u = v)"
      using Q_atom unfolding pp_e_atom_at_def by blast
    have v_ne_w: "v \<noteq> w"
      using Q_unique v_future Q_not_w by blast
    have strict: "strict_prefix w v"
      using v_future v_ne_w
      unfolding strict_prefix_def by blast
    then obtain b zs where v_split: "v = w @ b # zs"
      by (rule strict_prefixE')
    let ?q = "w @ [b]"
    have q_future: "prefix w ?q"
      by simp
    have q_v: "prefix ?q v"
      using v_split by (simp add: prefix_def)
    have Q_v: "pp_e_holds Q v"
      using Q_unique v_future by simp
    have possible_at_q:
        "\<exists>u. prefix ?q u \<and> pp_e_holds Q u"
      using q_v Q_v by blast
    have C_or_Q_at_q:
        "pp_e_holds C ?q \<or> pp_e_holds Q ?q"
      using diamond q_future possible_at_q by blast
    have not_C_q: "\<not> pp_e_holds C ?q"
      using C_unique q_future by simp
    have Q_q: "pp_e_holds Q ?q"
      using C_or_Q_at_q not_C_q by blast
    have q_eq_v: "?q = v"
      using Q_unique q_future Q_q by blast
    show "pp_e_child_atom_at w Q"
      unfolding pp_e_child_atom_at_def
      using Q_unique q_eq_v by blast
  next
    assume child: "pp_e_child_atom_at w Q"
    obtain b where Q_unique:
        "\<forall>u. prefix w u \<longrightarrow>
          (pp_e_holds Q u \<longleftrightarrow> u = w @ [b])"
      using child unfolding pp_e_child_atom_at_def by blast
    have Q_atom: "pp_e_atom_at w Q"
      using child by (rule pp_e_child_atom_at_is_atom)
    have Q_not_w: "\<not> pp_e_holds Q w"
      using Q_unique by simp
    have diamond:
        "\<forall>v. prefix w v \<longrightarrow>
          ((\<exists>u. prefix v u \<and> pp_e_holds Q u)
            \<longleftrightarrow>
           pp_e_holds C v \<or> pp_e_holds Q v)"
    proof (intro allI impI)
      fix v
      assume v_future: "prefix w v"
      show "(\<exists>u. prefix v u \<and> pp_e_holds Q u)
          \<longleftrightarrow> pp_e_holds C v \<or> pp_e_holds Q v"
      proof
        assume possible: "\<exists>u. prefix v u \<and> pp_e_holds Q u"
        then obtain u where vu: "prefix v u" and Q_u: "pp_e_holds Q u"
          by blast
        have u_future: "prefix w u"
          using v_future vu by (rule prefix_order.trans)
        have u_child: "u = w @ [b]"
          using Q_unique u_future Q_u by blast
        obtain xs where v: "v = w @ xs"
          using v_future unfolding prefix_def by blast
        have xs_prefix: "prefix xs [b]"
          using vu unfolding v u_child prefix_def by simp
        have xs_length: "length xs \<le> 1"
          using prefix_length_le[OF xs_prefix] by simp
        have "xs = [] \<or> xs = [b]"
        proof (cases xs)
          case Nil
          then show ?thesis by simp
        next
          case (Cons c cs)
          then have "cs = []"
            using xs_length by simp
          moreover have "c = b"
            using xs_prefix Cons calculation
            unfolding prefix_def by auto
          ultimately show ?thesis
            using Cons by simp
        qed
        then have "v = w \<or> v = w @ [b]"
          unfolding v by auto
        then show "pp_e_holds C v \<or> pp_e_holds Q v"
          using C_unique Q_unique v_future by blast
      next
        assume "pp_e_holds C v \<or> pp_e_holds Q v"
        then have "v = w \<or> v = w @ [b]"
          using C_unique Q_unique v_future by blast
        then show "\<exists>u. prefix v u \<and> pp_e_holds Q u"
        proof
          assume "v = w"
          moreover have "prefix w (w @ [b])"
            by simp
          moreover have "pp_e_holds Q (w @ [b])"
            using Q_unique by simp
          ultimately show ?thesis by blast
        next
          assume "v = w @ [b]"
          moreover have "pp_e_holds Q v"
            using Q_unique v_future calculation by simp
          ultimately show ?thesis by blast
        qed
      qed
    qed
    show "pp_e_holds
        (((pp_e_closed_den pp_e_HO_immediate_term) \<acute> C)
          \<acute> Q) w"
      using raw Q_atom Q_not_w diamond by blast
  qed
qed

end
