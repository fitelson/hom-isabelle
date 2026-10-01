theory Classicism_2_11_Realization
  imports Classicism_2_11_Currents
begin

section \<open>Realization of relational objects by their current and future data\<close>

text \<open>
  Fix an argument list σs and the relational type τ = σs→t. At every
  world kind, an object of type τ is determined by, and can be built
  from, the following data:
  \<^item> terminal worlds (the limit world and the leaves): its current relation;
  \<^item> the intermediate world: its current relation and its terminal image;
  \<^item> the root: its current relation, its intermediate image and its
    sequence of leaf images, subject to the ultralimit compatibility
    condition.
  The current relation is an arbitrary set of argument tuples drawn from
  the carriers of the world itself. The proofs are by induction on σs.
  At an arrow step, the output on each argument is the unique object, given
  by the hypothesis, whose current relation is the section of the
  prescribed relation at that argument and whose future components are
  the prescribed applications. Ordinary joint surjectivity alone does not
  suffice, since it cannot prescribe the current relation. No restriction
  of σs to relational argument types is needed for these facts.
\<close>

subsection \<open>Sections and world bookkeeping\<close>

definition c211_section :: "ZF list set \<Rightarrow> ZF \<Rightarrow> ZF list set" where
  "c211_section R x = {ys. x # ys \<in> R}"

definition c211_terminal :: "ZF \<Rightarrow> bool" where
  "c211_terminal w \<longleftrightarrow> w = raw_limit \<or> (\<exists>n. w = raw_leaf n)"

lemma c211_terminal_worlds [simp]:
  "c211_terminal raw_limit" "c211_terminal (raw_leaf n)"
  by (auto simp: c211_terminal_def)

lemma c211_terminal_code:
  assumes "c211_terminal w"
  shows "Nat2nat w \<noteq> 0" "Nat2nat w \<noteq> 1"
  using assms by (auto simp: c211_terminal_def)

lemma c211_terminal_simps:
  assumes "c211_terminal w"
  shows "raw_D a w = typed_M a" "raw_app a b w F x = app F x"
    "raw_truth w p = bit_dec p"
  using c211_terminal_code[OF assms]
  by (simp_all add: raw_D_def raw_app_def raw_truth_def)

lemma c211_middle_simps:
  "raw_app a b raw_middle F x = typed_S_app F x"
  "raw_truth raw_middle p = bit_dec (Fst p)"
  by (simp_all add: raw_app_def raw_truth_def)

lemma c211_root_simps:
  "raw_app a b raw_root F x = typed_R_app F x"
  "raw_truth raw_root p = bit_dec (Fst p)"
  by (simp_all add: raw_app_def raw_truth_def)

subsection \<open>Current relations through sections\<close>

lemma c211_rcur_Nil_iff:
  "c211_rcur [] w F = c211_rcur [] w G \<longleftrightarrow> (raw_truth w F \<longleftrightarrow> raw_truth w G)"
  unfolding c211_rcur_Nil by auto

lemma c211_rcur_Nil_eq:
  assumes "R \<subseteq> {[]}"
  shows "c211_rcur [] w F = R \<longleftrightarrow> (raw_truth w F \<longleftrightarrow> [] \<in> R)"
  using subset_singletonD[OF assms] by (auto simp: c211_rcur_Nil)

lemma c211_section_tuples:
  assumes "R \<subseteq> c211_tuples (\<sigma> # \<sigma>s) w"
  shows "c211_section R x \<subseteq> c211_tuples \<sigma>s w"
  using assms by (auto simp: c211_section_def c211_tuples_def)

lemma c211_rcur_section:
  assumes "Elem x (raw_D \<sigma> w)"
  shows "c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x) =
    c211_section (c211_rcur (\<sigma> # \<sigma>s) w F) x"
  using assms by (auto simp: c211_section_def c211_rcur_Cons)

lemma c211_rcur_Cons_eqI:
  assumes R: "R \<subseteq> c211_tuples (\<sigma> # \<sigma>s) w"
    and sec: "\<And>x. Elem x (raw_D \<sigma> w) \<Longrightarrow>
      c211_rcur \<sigma>s w (raw_app \<sigma> (paper_type_vector \<sigma>s Prop) w F x) = c211_section R x"
  shows "c211_rcur (\<sigma> # \<sigma>s) w F = R"
proof (rule set_eqI)
  fix zs
  show "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F \<longleftrightarrow> zs \<in> R"
  proof
    assume zs: "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F"
    then have "zs \<in> c211_tuples (\<sigma> # \<sigma>s) w" using c211_rcur_tuples by blast
    then obtain x ys where z: "zs = x # ys" and xm: "Elem x (raw_D \<sigma> w)"
      unfolding c211_tuples_Cons by blast
    have "ys \<in> c211_section R x"
      using zs by (simp add: z c211_rcur_Cons sec[OF xm])
    then show "zs \<in> R" by (simp add: z c211_section_def)
  next
    assume zs: "zs \<in> R"
    then have "zs \<in> c211_tuples (\<sigma> # \<sigma>s) w" using R by blast
    then obtain x ys where z: "zs = x # ys" and xm: "Elem x (raw_D \<sigma> w)"
      unfolding c211_tuples_Cons by blast
    have "ys \<in> c211_section R x" using zs by (simp add: z c211_section_def)
    then show "zs \<in> c211_rcur (\<sigma> # \<sigma>s) w F"
      using xm by (simp add: z c211_rcur_Cons sec[OF xm])
  qed
qed

lemma c211_seq_ext:
  assumes "Elem Q (Fun HOLZF.Nat A)" "Elem Q' (Fun HOLZF.Nat B)"
    and "\<And>n. typed_at Q n = typed_at Q' n"
  shows "Q = Q'"
proof (rule typed_graph_ext[OF assms(1,2)])
  fix N assume N: "Elem N HOLZF.Nat"
  show "app Q N = app Q' N"
    using assms(3)[of "Nat2nat N"] by (simp add: typed_at_def N)
qed

subsection \<open>Terminal worlds\<close>

theorem c211_terminal_unique:
  assumes w: "c211_terminal w"
    and Fm: "Elem F (typed_M (paper_type_vector \<sigma>s Prop))"
    and Gm: "Elem G (typed_M (paper_type_vector \<sigma>s Prop))"
    and cur: "c211_rcur \<sigma>s w F = c211_rcur \<sigma>s w G"
  shows "F = G"
  using Fm Gm cur
proof (induction \<sigma>s arbitrary: F G)
  case Nil
  have Fm: "Elem F typed_two" and Gm: "Elem G typed_two"
    using Nil.prems(1,2) by simp_all
  have "bit_dec F = bit_dec G"
    using Nil.prems(3) by (simp add: c211_rcur_Nil_iff c211_terminal_simps[OF w])
  then show ?case by (rule raw_bit_separates[OF Fm Gm])
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Fm: "Elem F (Fun (typed_M \<sigma>) (typed_M ?\<tau>))"
    and Gm: "Elem G (Fun (typed_M \<sigma>) (typed_M ?\<tau>))"
    using Cons.prems(1,2) by simp_all
  show ?case
  proof (rule typed_graph_ext[OF Fm Gm])
    fix x assume xm: "Elem x (typed_M \<sigma>)"
    have xD: "Elem x (raw_D \<sigma> w)" using xm by (simp add: c211_terminal_simps[OF w])
    have cur: "c211_rcur \<sigma>s w (app F x) = c211_rcur \<sigma>s w (app G x)"
      using c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=F]
        c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=G] Cons.prems(3)
      by (simp add: c211_terminal_simps[OF w])
    show "app F x = app G x"
      by (rule Cons.IH[OF typed_graph_value[OF Fm xm] typed_graph_value[OF Gm xm] cur])
  qed
qed

theorem c211_terminal_realize:
  assumes w: "c211_terminal w" and R: "R \<subseteq> c211_tuples \<sigma>s w"
  shows "\<exists>F. Elem F (typed_M (paper_type_vector \<sigma>s Prop)) \<and> c211_rcur \<sigma>s w F = R"
  using R
proof (induction \<sigma>s arbitrary: R)
  case Nil
  have R0: "R \<subseteq> {[]}" using Nil.prems by simp
  let ?F = "zbit ([] \<in> R)"
  have "c211_rcur [] w ?F = R"
    by (simp add: c211_rcur_Nil_eq[OF R0] c211_terminal_simps[OF w])
  then show ?case by (intro exI[of _ ?F]) simp
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  define f where "f x = (SOME F. Elem F (typed_M ?\<tau>) \<and>
    c211_rcur \<sigma>s w F = c211_section R x)" for x
  have f: "Elem (f x) (typed_M ?\<tau>) \<and> c211_rcur \<sigma>s w (f x) = c211_section R x" for x
    unfolding f_def by (rule someI_ex[OF Cons.IH[OF c211_section_tuples[OF Cons.prems]]])
  let ?F = "Lambda (typed_M \<sigma>) f"
  have Fm: "Elem ?F (typed_M (paper_type_vector (\<sigma> # \<sigma>s) Prop))"
    using f by (simp add: Elem_Lambda_Fun)
  have "c211_rcur (\<sigma> # \<sigma>s) w ?F = R"
  proof (rule c211_rcur_Cons_eqI[OF Cons.prems])
    fix x assume "Elem x (raw_D \<sigma> w)"
    then have xm: "Elem x (typed_M \<sigma>)" by (simp add: c211_terminal_simps[OF w])
    show "c211_rcur \<sigma>s w (raw_app \<sigma> ?\<tau> w ?F x) = c211_section R x"
      using f[of x] by (simp add: c211_terminal_simps[OF w] Lambda_app[OF xm])
  qed
  then show ?case using Fm by blast
qed

corollary c211_terminal_realize_ex1:
  assumes "c211_terminal w" "R \<subseteq> c211_tuples \<sigma>s w"
  shows "\<exists>!F. Elem F (typed_M (paper_type_vector \<sigma>s Prop)) \<and> c211_rcur \<sigma>s w F = R"
  by (rule ex_ex1I[OF c211_terminal_realize[OF assms]], elim conjE,
      rule c211_terminal_unique[OF assms(1), where \<sigma>s=\<sigma>s]) simp_all

subsection \<open>The intermediate world\<close>

theorem c211_middle_unique:
  assumes Sm: "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    and S'm: "Elem S' (typed_S (paper_type_vector \<sigma>s Prop))"
    and cur: "c211_rcur \<sigma>s raw_middle S = c211_rcur \<sigma>s raw_middle S'"
    and fut: "typed_j (paper_type_vector \<sigma>s Prop) S = typed_j (paper_type_vector \<sigma>s Prop) S'"
  shows "S = S'"
  using Sm S'm cur fut
proof (induction \<sigma>s arbitrary: S S')
  case Nil
  obtain a b where S: "S = Opair a b" "Elem a typed_two"
    using Nil.prems(1) by (auto simp: CartProd)
  obtain c d where S': "S' = Opair c d" "Elem c typed_two"
    using Nil.prems(2) by (auto simp: CartProd)
  have "bit_dec a = bit_dec c"
    using Nil.prems(3) by (simp add: c211_rcur_Nil_iff c211_middle_simps S(1) S'(1) Fst)
  then have ac: "a = c" by (rule raw_bit_separates[OF S(2) S'(2)])
  have bd: "b = d" using Nil.prems(4) by (simp add: S(1) S'(1) Snd)
  show ?case by (simp add: S(1) S'(1) ac bd)
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Sm: "Elem S (typed_S (Arr \<sigma> ?\<tau>))" and S'm: "Elem S' (typed_S (Arr \<sigma> ?\<tau>))"
    using Cons.prems(1,2) by simp_all
  show ?case
  proof (rule typed_S_extensional[OF Sm S'm])
    fix x assume xm: "Elem x (typed_S \<sigma>)"
    have xD: "Elem x (raw_D \<sigma> raw_middle)" using xm by simp
    have cur: "c211_rcur \<sigma>s raw_middle (typed_S_app S x) =
        c211_rcur \<sigma>s raw_middle (typed_S_app S' x)"
      using c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=S]
        c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=S'] Cons.prems(3)
      by (simp add: c211_middle_simps)
    have fut: "typed_j ?\<tau> (typed_S_app S x) = typed_j ?\<tau> (typed_S_app S' x)"
      using Cons.prems(4)
      by (simp add: typed_S_application_natural[OF Sm xm] typed_S_application_natural[OF S'm xm])
    show "typed_S_app S x = typed_S_app S' x"
      by (rule Cons.IH[OF typed_S_application[OF Sm xm] typed_S_application[OF S'm xm] cur fut])
  qed
qed

theorem c211_middle_realize:
  assumes R: "R \<subseteq> c211_tuples \<sigma>s raw_middle"
    and Um: "Elem U (typed_M (paper_type_vector \<sigma>s Prop))"
  shows "\<exists>S. Elem S (typed_S (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_middle S = R \<and> typed_j (paper_type_vector \<sigma>s Prop) S = U"
  using R Um
proof (induction \<sigma>s arbitrary: R U)
  case Nil
  have R0: "R \<subseteq> {[]}" using Nil.prems(1) by simp
  let ?S = "Opair (zbit ([] \<in> R)) U"
  have Sm: "Elem ?S (typed_S (paper_type_vector [] Prop))"
    using Nil.prems(2) by (simp add: CartProd Opair)
  have "c211_rcur [] raw_middle ?S = R"
    by (simp add: c211_rcur_Nil_eq[OF R0] c211_middle_simps Fst)
  moreover have "typed_j (paper_type_vector [] Prop) ?S = U" by (simp add: Snd)
  ultimately show ?case using Sm by blast
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Um: "Elem U (Fun (typed_M \<sigma>) (typed_M ?\<tau>))" using Cons.prems(2) by simp
  define f where "f x = (SOME S. Elem S (typed_S ?\<tau>) \<and>
    c211_rcur \<sigma>s raw_middle S = c211_section R x \<and>
    typed_j ?\<tau> S = app U (typed_j \<sigma> x))" for x
  have f: "Elem (f x) (typed_S ?\<tau>) \<and> c211_rcur \<sigma>s raw_middle (f x) = c211_section R x \<and>
      typed_j ?\<tau> (f x) = app U (typed_j \<sigma> x)" if xm: "Elem x (typed_S \<sigma>)" for x
    unfolding f_def
    by (rule someI_ex[OF Cons.IH[OF c211_section_tuples[OF Cons.prems(1)]
          typed_graph_value[OF Um typed_j_type[OF xm]]]])
  let ?S = "Opair (Lambda (typed_S \<sigma>) f) U"
  have Sm: "Elem ?S (typed_S (paper_type_vector (\<sigma> # \<sigma>s) Prop))"
    using f Um by (auto simp: typed_compatible_pair Elem_Lambda_Fun Lambda_app)
  have "c211_rcur (\<sigma> # \<sigma>s) raw_middle ?S = R"
  proof (rule c211_rcur_Cons_eqI[OF Cons.prems(1)])
    fix x assume "Elem x (raw_D \<sigma> raw_middle)"
    then have xm: "Elem x (typed_S \<sigma>)" by simp
    show "c211_rcur \<sigma>s raw_middle (raw_app \<sigma> ?\<tau> raw_middle ?S x) = c211_section R x"
      using f[OF xm] by (simp add: c211_middle_simps typed_S_app_def Fst Lambda_app[OF xm])
  qed
  moreover have "typed_j (paper_type_vector (\<sigma> # \<sigma>s) Prop) ?S = U" by (simp add: Snd)
  ultimately show ?case using Sm by blast
qed

corollary c211_middle_realize_ex1:
  assumes "R \<subseteq> c211_tuples \<sigma>s raw_middle"
    and "Elem U (typed_M (paper_type_vector \<sigma>s Prop))"
  shows "\<exists>!S. Elem S (typed_S (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_middle S = R \<and> typed_j (paper_type_vector \<sigma>s Prop) S = U"
  by (rule ex_ex1I[OF c211_middle_realize[OF assms]], elim conjE,
      rule c211_middle_unique[where \<sigma>s=\<sigma>s]) simp_all

theorem c211_middle_data:
  assumes "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
  shows "c211_rcur \<sigma>s raw_middle S \<subseteq> c211_tuples \<sigma>s raw_middle"
    "Elem (typed_j (paper_type_vector \<sigma>s Prop) S) (typed_M (paper_type_vector \<sigma>s Prop))"
  by (rule c211_rcur_tuples) (rule typed_j_type[OF assms])

subsection \<open>The root\<close>

theorem c211_root_unique:
  assumes Xm: "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    and Ym: "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
    and cur: "c211_rcur \<sigma>s raw_root X = c211_rcur \<sigma>s raw_root Y"
    and mid: "typed_rs (paper_type_vector \<sigma>s Prop) X = typed_rs (paper_type_vector \<sigma>s Prop) Y"
    and leaf: "\<forall>n. typed_rn (paper_type_vector \<sigma>s Prop) X n =
      typed_rn (paper_type_vector \<sigma>s Prop) Y n"
  shows "X = Y"
  using Xm Ym cur mid leaf
proof (induction \<sigma>s arbitrary: X Y)
  case Nil
  have XP: "Elem X (typed_R Prop)" and YP: "Elem Y (typed_R Prop)"
    using Nil.prems(1,2) by simp_all
  obtain a b Q where X: "X = Opair a (Opair b Q)" "Elem a typed_two"
      "Elem Q (Fun HOLZF.Nat typed_two)"
    using typed_R_propE[OF XP] by blast
  obtain c d Q' where Y: "Y = Opair c (Opair d Q')" "Elem c typed_two"
      "Elem Q' (Fun HOLZF.Nat typed_two)"
    using typed_R_propE[OF YP] by blast
  have "bit_dec a = bit_dec c"
    using Nil.prems(3) by (simp add: c211_rcur_Nil_iff c211_root_simps X(1) Y(1) Fst)
  then have ac: "a = c" by (rule raw_bit_separates[OF X(2) Y(2)])
  have bd: "b = d" using Nil.prems(4) by (simp add: X(1) Y(1) Fst Snd Opair)
  have QQ: "Q = Q'"
  proof (rule c211_seq_ext[OF X(3) Y(3)])
    fix n
    show "typed_at Q n = typed_at Q' n"
      using Nil.prems(5) by (simp add: X(1) Y(1) Snd)
  qed
  show ?case by (simp add: X(1) Y(1) ac bd QQ)
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Xm: "Elem X (typed_R (Arr \<sigma> ?\<tau>))" and Ym: "Elem Y (typed_R (Arr \<sigma> ?\<tau>))"
    using Cons.prems(1,2) by simp_all
  show ?case
  proof (rule typed_R_extensional[OF Xm Ym])
    fix x assume xm: "Elem x (typed_R \<sigma>)"
    have xD: "Elem x (raw_D \<sigma> raw_root)" using xm by simp
    have cur: "c211_rcur \<sigma>s raw_root (typed_R_app X x) =
        c211_rcur \<sigma>s raw_root (typed_R_app Y x)"
      using c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=X]
        c211_rcur_section[OF xD, where \<sigma>s=\<sigma>s and F=Y] Cons.prems(3)
      by (simp add: c211_root_simps)
    have mid: "typed_rs ?\<tau> (typed_R_app X x) = typed_rs ?\<tau> (typed_R_app Y x)"
      using Cons.prems(4)
      by (simp add: typed_R_application_s[OF Xm xm] typed_R_application_s[OF Ym xm])
    have leaf: "\<forall>n. typed_rn ?\<tau> (typed_R_app X x) n = typed_rn ?\<tau> (typed_R_app Y x) n"
      using Cons.prems(5)
      by (simp add: typed_R_application_n[OF Xm xm] typed_R_application_n[OF Ym xm])
    show "typed_R_app X x = typed_R_app Y x"
      by (rule Cons.IH[OF typed_R_application[OF Xm xm] typed_R_application[OF Ym xm]
            cur mid leaf])
  qed
qed

theorem c211_root_realize:
  assumes R: "R \<subseteq> c211_tuples \<sigma>s raw_root"
    and Sm: "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    and Nm: "\<And>n. Elem (N n) (typed_M (paper_type_vector \<sigma>s Prop))"
    and compat: "typed_j (paper_type_vector \<sigma>s Prop) S = ulim N"
  shows "\<exists>X. Elem X (typed_R (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_root X = R \<and> typed_rs (paper_type_vector \<sigma>s Prop) X = S \<and>
    (\<forall>n. typed_rn (paper_type_vector \<sigma>s Prop) X n = N n)"
  using R Sm Nm compat
proof (induction \<sigma>s arbitrary: R S N)
  case Nil
  have R0: "R \<subseteq> {[]}" using Nil.prems(1) by simp
  obtain s u where S: "S = Opair s u" "Elem s typed_two"
    using Nil.prems(2) by (auto simp: CartProd)
  have Nm: "Elem (N n) typed_two" for n using Nil.prems(3)[of n] by simp
  have u: "u = ulim N" using Nil.prems(4) by (simp add: S(1) Snd)
  let ?X = "Opair (zbit ([] \<in> R)) (Opair s (typed_seq N))"
  have Xm: "Elem ?X (typed_R (paper_type_vector [] Prop))"
    using typed_R_propI[OF zbit_type[of "[] \<in> R"] S(2) Nm] by simp
  have "c211_rcur [] raw_root ?X = R"
    by (simp add: c211_rcur_Nil_eq[OF R0] c211_root_simps Fst)
  moreover have "typed_rs (paper_type_vector [] Prop) ?X = S"
    by (simp add: S(1) u Fst Snd)
  moreover have "\<forall>n. typed_rn (paper_type_vector [] Prop) ?X n = N n"
    by (simp add: Snd)
  ultimately show ?case using Xm by blast
next
  case (Cons \<sigma> \<sigma>s)
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have Sm: "Elem S (typed_S (Arr \<sigma> ?\<tau>))" using Cons.prems(2) by simp
  have Nm: "Elem (N n) (typed_M (Arr \<sigma> ?\<tau>))" for n using Cons.prems(3)[of n] by simp
  have compat: "typed_j (Arr \<sigma> ?\<tau>) S = ulim N" using Cons.prems(4) by simp
  have out: "\<exists>X'. Elem X' (typed_R ?\<tau>) \<and> c211_rcur \<sigma>s raw_root X' = c211_section R x \<and>
      typed_rs ?\<tau> X' = typed_S_app S (typed_rs \<sigma> x) \<and>
      (\<forall>n. typed_rn ?\<tau> X' n = app (N n) (typed_rn \<sigma> x n))"
    if xm: "Elem x (typed_R \<sigma>)" for x
  proof -
    have sm: "Elem (typed_S_app S (typed_rs \<sigma> x)) (typed_S ?\<tau>)"
      by (rule typed_S_application[OF Sm typed_rs_type[OF xm]])
    have nm: "Elem (app (N n) (typed_rn \<sigma> x n)) (typed_M ?\<tau>)" for n
      by (rule typed_M_application[OF Nm typed_rn_type[OF xm]])
    have coh: "typed_j ?\<tau> (typed_S_app S (typed_rs \<sigma> x)) =
        ulim (\<lambda>n. app (N n) (typed_rn \<sigma> x n))"
      using typed_S_application_natural[OF Sm typed_rs_type[OF xm]]
        typed_ulim_app[where a=\<sigma> and b="paper_type_vector \<sigma>s Prop"
          and f=N and x="typed_rn \<sigma> x", OF Nm typed_rn_type[OF xm]]
        compat
      by (simp add: typed_R_compatible[OF xm])
    show ?thesis
      by (rule Cons.IH[OF c211_section_tuples[OF Cons.prems(1)] sm nm coh])
  qed
  define f where "f x = (SOME X'. Elem X' (typed_R ?\<tau>) \<and>
    c211_rcur \<sigma>s raw_root X' = c211_section R x \<and>
    typed_rs ?\<tau> X' = typed_S_app S (typed_rs \<sigma> x) \<and>
    (\<forall>n. typed_rn ?\<tau> X' n = app (N n) (typed_rn \<sigma> x n)))" for x
  have f: "Elem (f x) (typed_R ?\<tau>) \<and> c211_rcur \<sigma>s raw_root (f x) = c211_section R x \<and>
      typed_rs ?\<tau> (f x) = typed_S_app S (typed_rs \<sigma> x) \<and>
      (\<forall>n. typed_rn ?\<tau> (f x) n = app (N n) (typed_rn \<sigma> x n))"
    if "Elem x (typed_R \<sigma>)" for x
    unfolding f_def by (rule someI_ex[OF out[OF that]])
  let ?X = "Opair (Lambda (typed_R \<sigma>) f) (Opair S (typed_seq N))"
  have Xm: "Elem ?X (typed_R (paper_type_vector (\<sigma> # \<sigma>s) Prop))"
    using Sm Nm compat f typed_seq_type[OF Nm]
    by (auto simp: typed_root_arrow_triple Elem_Lambda_Fun Lambda_app)
  have "c211_rcur (\<sigma> # \<sigma>s) raw_root ?X = R"
  proof (rule c211_rcur_Cons_eqI[OF Cons.prems(1)])
    fix x assume "Elem x (raw_D \<sigma> raw_root)"
    then have xm: "Elem x (typed_R \<sigma>)" by simp
    show "c211_rcur \<sigma>s raw_root (raw_app \<sigma> ?\<tau> raw_root ?X x) = c211_section R x"
      using f[OF xm] by (simp add: c211_root_simps typed_R_app_def Fst Lambda_app[OF xm])
  qed
  moreover have "typed_rs (paper_type_vector (\<sigma> # \<sigma>s) Prop) ?X = S"
    by (simp add: Fst Snd)
  moreover have "\<forall>n. typed_rn (paper_type_vector (\<sigma> # \<sigma>s) Prop) ?X n = N n"
    by (simp add: Snd)
  ultimately show ?case using Xm by blast
qed

corollary c211_root_realize_ex1:
  assumes "R \<subseteq> c211_tuples \<sigma>s raw_root"
    and "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    and "\<And>n. Elem (N n) (typed_M (paper_type_vector \<sigma>s Prop))"
    and "typed_j (paper_type_vector \<sigma>s Prop) S = ulim N"
  shows "\<exists>!X. Elem X (typed_R (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_root X = R \<and> typed_rs (paper_type_vector \<sigma>s Prop) X = S \<and>
    (\<forall>n. typed_rn (paper_type_vector \<sigma>s Prop) X n = N n)"
  by (rule ex_ex1I[OF c211_root_realize[OF assms]], elim conjE,
      rule c211_root_unique[where \<sigma>s=\<sigma>s]) simp_all

theorem c211_root_data:
  assumes "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
  shows "c211_rcur \<sigma>s raw_root X \<subseteq> c211_tuples \<sigma>s raw_root"
    "Elem (typed_rs (paper_type_vector \<sigma>s Prop) X) (typed_S (paper_type_vector \<sigma>s Prop))"
    "\<And>n. Elem (typed_rn (paper_type_vector \<sigma>s Prop) X n) (typed_M (paper_type_vector \<sigma>s Prop))"
    "typed_j (paper_type_vector \<sigma>s Prop) (typed_rs (paper_type_vector \<sigma>s Prop) X) =
      ulim (typed_rn (paper_type_vector \<sigma>s Prop) X)"
  by (rule c211_rcur_tuples, rule typed_rs_type[OF assms], rule typed_rn_type[OF assms],
      rule typed_R_compatible[OF assms])

text \<open>
  Together with c211_root_data, the root theorems say that X is
  determined by, and freely realizes, the triple of its current relation,
  its intermediate image, and its leaf sequence, subject only to the
  ultralimit condition. The middle and terminal theorems give the
  analogous statements for the other worlds.
\<close>

ML \<open>
  val facts = [@{thm c211_rcur_section}, @{thm c211_rcur_Cons_eqI},
    @{thm c211_terminal_unique}, @{thm c211_terminal_realize},
    @{thm c211_terminal_realize_ex1},
    @{thm c211_middle_unique}, @{thm c211_middle_realize},
    @{thm c211_middle_realize_ex1}, @{thm c211_middle_data(1)}, @{thm c211_middle_data(2)},
    @{thm c211_root_unique}, @{thm c211_root_realize}, @{thm c211_root_realize_ex1},
    @{thm c211_root_data(1)}, @{thm c211_root_data(2)}, @{thm c211_root_data(3)},
    @{thm c211_root_data(4)}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-REALIZATION: relational objects at every world kind are realized uniquely by current relation and future data";
\<close>

end
