theory Bacon_PP_Goodman_T2f_Verified
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_T2f_Pairwise"
begin

section \<open>Goodman T2f as a single object-language theorem\<close>

text \<open>
  The six propositions are, in order,
  \<open>\<top>\<close>, \<open>\<bottom>\<close>, \<open>r\<close>, \<open>\<not>r\<close>,
  \<open>(r = \<top>)\<close>, \<open>(r = \<bottom>)\<close>,
  and the conjunction below lists the fifteen pairwise inequalities in
  lexicographic order.
\<close>

definition pp_T2f_six_distinct :: "oterm \<Rightarrow> oterm" where
  "pp_T2f_six_distinct r =
    Conj
          (Neg (Eq Prop (ObjTrue) (ObjFalse)))
          (Conj
          (Neg (Eq Prop (ObjTrue) (r)))
          (Conj
          (Neg (Eq Prop (ObjTrue) (Neg r)))
          (Conj
          (Neg (Eq Prop (ObjTrue) (Eq Prop r ObjTrue)))
          (Conj
          (Neg (Eq Prop (ObjTrue) (Eq Prop r ObjFalse)))
          (Conj
          (Neg (Eq Prop (ObjFalse) (r)))
          (Conj
          (Neg (Eq Prop (ObjFalse) (Neg r)))
          (Conj
          (Neg (Eq Prop (ObjFalse) (Eq Prop r ObjTrue)))
          (Conj
          (Neg (Eq Prop (ObjFalse) (Eq Prop r ObjFalse)))
          (Conj
          (Neg (Eq Prop (r) (Neg r)))
          (Conj
          (Neg (Eq Prop (r) (Eq Prop r ObjTrue)))
          (Conj
          (Neg (Eq Prop (r) (Eq Prop r ObjFalse)))
          (Conj
          (Neg (Eq Prop (Neg r) (Eq Prop r ObjTrue)))
          (Conj
          (Neg (Eq Prop (Neg r) (Eq Prop r ObjFalse)))
          (Neg (Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse))))))))))))))))"

theorem CEV_Goodman_T2f:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (pp_T2f_six_distinct r)"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have c0: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Ktop_Kbot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c1: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (r))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Ktop_Id[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c2: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Neg r))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Ktop_Neg[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c3: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Eq Prop r ObjTrue))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Ktop_Box[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c4: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Eq Prop r ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Ktop_Bot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c5: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (r))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Kbot_Id[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c6: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Neg r))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Kbot_Neg[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c7: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Eq Prop r ObjTrue))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Kbot_Box[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c8: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Eq Prop r ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Kbot_Bot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c9: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Neg r))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Id_Neg[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c10: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Eq Prop r ObjTrue))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Id_Box[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c11: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Eq Prop r ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Id_Bot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c12: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Neg r) (Eq Prop r ObjTrue))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Neg_Box[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c13: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Neg r) (Eq Prop r ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Neg_Bot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have c14: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse))"
    using d_F CEV_axiom_from.Theorem[OF T2f_Box_Bot[OF core r_type]]
    by (rule CEV_axiom_from.MP)
  have body:
    "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_T2f_six_distinct r"
    unfolding pp_T2f_six_distinct_def
    using c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
    by (intro CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type body by (rule CEV_axiom_from_singleton_imp)
qed

end
