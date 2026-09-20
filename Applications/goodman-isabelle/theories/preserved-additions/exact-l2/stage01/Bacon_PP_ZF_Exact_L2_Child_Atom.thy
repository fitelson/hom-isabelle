theory Bacon_PP_ZF_Exact_L2_Child_Atom
  imports 
    "Goodman_Exact_Stock_Legacy_01.Bacon_PP_ZF_Exact_L2_Refutation"
begin

section \<open>A quantified immediate-successor operator\<close>

text \<open>
  At a world, the atoms of the Boolean algebra of propositions modulo
  world-relative equality are exactly the singleton propositions in the
  current cone.  This lets the object language characterize all immediate
  successors without naming a particular branch.
\<close>

definition pp_e_HO_atom_term :: oterm where
  "pp_e_HO_atom_term =
    Lam Prop
      (Conj
        (Neg (Eq Prop (Var 0) ObjFalse))
        (Forall Prop
          (Imp
            (Eq Prop (Var 0) (Conj (Var 0) (Var 1)))
            (Disj
              (Eq Prop (Var 0) ObjFalse)
              (Eq Prop (Var 0) (Var 1))))))"

definition pp_e_HO_immediate_term :: oterm where
  "pp_e_HO_immediate_term =
    Lam Prop
      (Lam Prop
        (Conj
          (App pp_e_HO_atom_term (Var 0))
          (Conj
            (Neg (Var 0))
            (Eq Prop
              (\<diamond>\<^sub>o (Var 0))
              (Disj (Var 1) (Var 0))))))"

definition pp_e_HO_child_variation_term :: oterm where
  "pp_e_HO_child_variation_term =
    Lam Prop
      (Exists Prop
        (Conj
          (App pp_e_HO_atom_term (Var 0))
          (Conj
            (Var 0)
            (Conj
              (Exists Prop
                (Conj
                  (App
                    (App pp_e_HO_immediate_term (Var 1))
                    (Var 0))
                  (Eq Prop
                    (Var 0)
                    (Conj (Var 0) (Var 2)))))
              (Exists Prop
                (Conj
                  (App
                    (App pp_e_HO_immediate_term (Var 1))
                    (Var 0))
                  (Eq Prop
                    (Var 0)
                    (Conj (Var 0) (Neg (Var 2))))))))))"

lemma pp_e_HO_child_variation_terms_typed:
  "[] \<turnstile> pp_e_HO_atom_term : (Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_e_HO_immediate_term :
    (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)"
  "[] \<turnstile> pp_e_HO_child_variation_term :
    (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound;
      simp add: pp_e_HO_atom_term_def
        pp_e_HO_immediate_term_def
        pp_e_HO_child_variation_term_def
        ObjFalse_def ObjDiamond_def ObjBox_def ObjTrue_def lookup_def)+

lemma pp_e_HO_child_variation_terms_logical:
  "pp_logical_vocabulary pp_e_HO_atom_term"
  "pp_logical_vocabulary pp_e_HO_immediate_term"
  "pp_logical_vocabulary pp_e_HO_child_variation_term"
  by (simp_all add: pp_logical_vocabulary_def
      pp_e_HO_atom_term_def pp_e_HO_immediate_term_def
      pp_e_HO_child_variation_term_def ObjFalse_def
      ObjDiamond_def ObjBox_def ObjTrue_def)

definition pp_e_child_variation :: pp_e_operator where
  "pp_e_child_variation P =
    {i. (\<exists>n. n # i \<in> P) \<and> (\<exists>n. n # i \<notin> P)}"

definition pp_e_atom_at :: "nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_e_atom_at w Q \<longleftrightarrow>
    (\<exists>v. prefix w v \<and>
      (\<forall>u. prefix w u \<longrightarrow>
        (pp_e_holds Q u \<longleftrightarrow> u = v)))"

lemma pp_e_HO_atom_raw:
  assumes Q: "Elem Q (pp_e_domain Prop)"
  shows "pp_e_holds
      ((pp_e_closed_den pp_e_HO_atom_term) \<acute> Q) w
    \<longleftrightarrow>
    ((\<exists>v. prefix w v \<and> pp_e_holds Q v) \<and>
      (\<forall>R.
        Elem R (pp_e_domain Prop) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds R v \<longrightarrow> pp_e_holds Q v))
          \<longrightarrow>
          ((\<forall>v. prefix w v \<longrightarrow>
              \<not> pp_e_holds R v) \<or>
           (\<forall>v. prefix w v \<longrightarrow>
              (pp_e_holds R v \<longleftrightarrow>
               pp_e_holds Q v))))))"
  using Q
  by (simp add: pp_e_closed_den_def pp_e_HO_atom_term_def
      ObjFalse_def pp_e_eval_ObjTrue Lambda_app; blast)

theorem pp_e_HO_atom_holds:
  assumes Q: "Elem Q (pp_e_domain Prop)"
  shows "pp_e_holds
      ((pp_e_closed_den pp_e_HO_atom_term) \<acute> Q) w
    \<longleftrightarrow> pp_e_atom_at w Q"
proof
  assume atom:
      "pp_e_holds
        ((pp_e_closed_den pp_e_HO_atom_term) \<acute> Q) w"
  have raw:
      "(\<exists>v. prefix w v \<and> pp_e_holds Q v) \<and>
       (\<forall>R.
        Elem R (pp_e_domain Prop) \<longrightarrow>
        ((\<forall>v. prefix w v \<longrightarrow>
            (pp_e_holds R v \<longrightarrow> pp_e_holds Q v))
          \<longrightarrow>
          ((\<forall>v. prefix w v \<longrightarrow>
              \<not> pp_e_holds R v) \<or>
           (\<forall>v. prefix w v \<longrightarrow>
              (pp_e_holds R v \<longleftrightarrow>
               pp_e_holds Q v)))))"
    using atom pp_e_HO_atom_raw[OF Q, of w] by blast
  then obtain v where v_future: "prefix w v"
    and Q_v: "pp_e_holds Q v"
    by blast
  show "pp_e_atom_at w Q"
    unfolding pp_e_atom_at_def
  proof (intro exI[of _ v] conjI allI impI)
    show "prefix w v"
      by (rule v_future)
  next
    fix u
    assume u_future: "prefix w u"
    show "pp_e_holds Q u \<longleftrightarrow> u = v"
    proof
      assume Q_u: "pp_e_holds Q u"
      let ?R = "pp_n_prop (\<lambda>x. x = u)"
      have R_domain: "Elem ?R (pp_e_domain Prop)"
        using pp_n_prop_in_power by simp
      have R_subset:
          "\<forall>t. prefix w t \<longrightarrow>
            (pp_e_holds ?R t \<longrightarrow> pp_e_holds Q t)"
        using Q_u by auto
      have alternatives:
          "(\<forall>t. prefix w t \<longrightarrow>
              \<not> pp_e_holds ?R t) \<or>
           (\<forall>t. prefix w t \<longrightarrow>
              (pp_e_holds ?R t \<longleftrightarrow>
               pp_e_holds Q t))"
        using raw R_domain R_subset by blast
      have not_empty:
          "\<not> (\<forall>t. prefix w t \<longrightarrow>
            \<not> pp_e_holds ?R t)"
        using u_future by auto
      have same:
          "\<forall>t. prefix w t \<longrightarrow>
            (pp_e_holds ?R t \<longleftrightarrow>
             pp_e_holds Q t)"
        using alternatives not_empty by blast
      have "pp_e_holds ?R v"
        using same v_future Q_v by blast
      then show "u = v"
        by simp
    next
      assume "u = v"
      then show "pp_e_holds Q u"
        using Q_v by simp
    qed
  qed
next
  assume atom_at: "pp_e_atom_at w Q"
  then obtain v where v_future: "prefix w v"
    and unique:
      "\<forall>u. prefix w u \<longrightarrow>
        (pp_e_holds Q u \<longleftrightarrow> u = v)"
    unfolding pp_e_atom_at_def by blast
  have Q_v: "pp_e_holds Q v"
    using unique v_future by blast
  have raw:
      "(\<exists>u. prefix w u \<and> pp_e_holds Q u) \<and>
       (\<forall>R.
        Elem R (pp_e_domain Prop) \<longrightarrow>
        ((\<forall>u. prefix w u \<longrightarrow>
            (pp_e_holds R u \<longrightarrow> pp_e_holds Q u))
          \<longrightarrow>
          ((\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_e_holds R u) \<or>
           (\<forall>u. prefix w u \<longrightarrow>
              (pp_e_holds R u \<longleftrightarrow>
               pp_e_holds Q u)))))"
  proof (intro conjI)
    show "\<exists>u. prefix w u \<and> pp_e_holds Q u"
      using v_future Q_v by blast
  next
    show "\<forall>R.
        Elem R (pp_e_domain Prop) \<longrightarrow>
        ((\<forall>u. prefix w u \<longrightarrow>
            (pp_e_holds R u \<longrightarrow> pp_e_holds Q u))
          \<longrightarrow>
          ((\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_e_holds R u) \<or>
           (\<forall>u. prefix w u \<longrightarrow>
              (pp_e_holds R u \<longleftrightarrow>
               pp_e_holds Q u))))"
    proof (intro allI impI)
      fix R
      assume subset:
          "\<forall>u. prefix w u \<longrightarrow>
            (pp_e_holds R u \<longrightarrow> pp_e_holds Q u)"
      show "(\<forall>u. prefix w u \<longrightarrow>
              \<not> pp_e_holds R u) \<or>
          (\<forall>u. prefix w u \<longrightarrow>
              (pp_e_holds R u \<longleftrightarrow>
               pp_e_holds Q u))"
      proof (cases "\<exists>u. prefix w u \<and> pp_e_holds R u")
        case False
        then show ?thesis by blast
      next
        case True
        then obtain u where u_future: "prefix w u"
          and R_u: "pp_e_holds R u"
          by blast
        have Q_u: "pp_e_holds Q u"
          using subset u_future R_u by blast
        have u_v: "u = v"
          using unique u_future Q_u by blast
        have same:
            "\<forall>t. prefix w t \<longrightarrow>
              (pp_e_holds R t \<longleftrightarrow>
               pp_e_holds Q t)"
        proof (intro allI impI iffI)
          fix t
          assume t_future: "prefix w t"
            and R_t: "pp_e_holds R t"
          show "pp_e_holds Q t"
            using subset t_future R_t by blast
        next
          fix t
          assume t_future: "prefix w t"
            and Q_t: "pp_e_holds Q t"
          have "t = v"
            using unique t_future Q_t by blast
          then show "pp_e_holds R t"
            using R_u u_v by simp
        qed
        then show ?thesis by blast
      qed
    qed
  qed
  show "pp_e_holds
      ((pp_e_closed_den pp_e_HO_atom_term) \<acute> Q) w"
    using pp_e_HO_atom_raw[OF Q, of w] raw by blast
qed

lemma pp_e_shift_HO_atom_term[simp]:
  "shift pp_e_HO_atom_term = pp_e_HO_atom_term"
  by (simp add: shift_def pp_e_HO_atom_term_def
      ObjFalse_def ObjTrue_def)

lemma pp_e_rename_HO_atom_term[simp]:
  "rename f pp_e_HO_atom_term = pp_e_HO_atom_term"
  by (simp add: pp_e_HO_atom_term_def
      ObjFalse_def ObjTrue_def)

lemma pp_e_eval_HO_atom_term_extend[simp]:
  "pp_e_eval C (extend_env x \<rho>) pp_e_HO_atom_term =
    pp_e_eval C \<rho> pp_e_HO_atom_term"
  using pp_e_eval_shift[of C x \<rho> pp_e_HO_atom_term]
  by simp

end
