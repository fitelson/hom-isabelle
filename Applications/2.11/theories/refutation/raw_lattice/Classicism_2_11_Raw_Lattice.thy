theory Classicism_2_11_Raw_Lattice
  imports "Classicism_2_11_Lattice.Classicism_2_11_Realization" "Classicism_2_11_Lattice.Classicism_2_11_Raw_Order"
begin

section \<open>Completeness and atomicity of the raw relational carriers\<close>

text \<open>
  Let τ = σ1→…→σk→t, written paper_type_vector σs Prop. At each world
  an object of type τ has free coordinates, each an arbitrary set of
  argument tuples:
  \<^item> at the root: its current relation, the current relation of its
    intermediate image, and the current relation of each leaf image;
  \<^item> at the intermediate world: its current relation and that of its
    terminal image;
  \<^item> at a terminal world: its current relation.
  The realization theorems make the coordinate map a bijection onto the
  product of the powersets of the tuple sets. The raw order and emptiness
  are coordinatewise inclusion and emptiness (Classicism_2_11_Raw_Order).
  The limit coordinate of a root object is not free: it is the ultralimit
  of the leaf coordinates, so it is never intersected separately; the
  meet below rebuilds it from the intersected leaves. Completeness and
  atomicity then follow from a generic argument about such products.
  No restriction of σs to relational argument types is needed.
\<close>

subsection \<open>Generic product-of-powersets arguments\<close>

lemma c211_coord_glb:
  assumes T: "\<And>x i. P x \<Longrightarrow> crd x i \<subseteq> T i"
    and onto: "\<And>f. (\<And>i. f i \<subseteq> T i) \<Longrightarrow> \<exists>x. P x \<and> (\<forall>i. crd x i = f i)"
    and le: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> leq x y \<longleftrightarrow> (\<forall>i. crd x i \<subseteq> crd y i)"
    and S: "\<And>y. y \<in> S \<Longrightarrow> P y"
  shows "\<exists>m. P m \<and> (\<forall>i. crd m i = {t \<in> T i. \<forall>y\<in>S. t \<in> crd y i}) \<and>
    (\<forall>z. P z \<longrightarrow> ((\<forall>y\<in>S. leq z y) \<longleftrightarrow> leq z m))"
proof -
  obtain m where m: "P m" and mc: "\<And>i. crd m i = {t \<in> T i. \<forall>y\<in>S. t \<in> crd y i}"
    using onto[of "\<lambda>i. {t \<in> T i. \<forall>y\<in>S. t \<in> crd y i}"] by blast
  have glb: "(\<forall>y\<in>S. leq z y) \<longleftrightarrow> leq z m" if z: "P z" for z
  proof -
    have "(\<forall>y\<in>S. leq z y) \<longleftrightarrow> (\<forall>y\<in>S. \<forall>i. crd z i \<subseteq> crd y i)"
      using S le[OF z] by blast
    also have "\<dots> \<longleftrightarrow> (\<forall>i. crd z i \<subseteq> crd m i)"
      unfolding mc using T[OF z] by blast
    also have "\<dots> \<longleftrightarrow> leq z m" by (rule le[OF z m, symmetric])
    finally show ?thesis .
  qed
  show ?thesis using m mc glb by blast
qed

lemma c211_coord_atom:
  assumes T: "\<And>x i. P x \<Longrightarrow> crd x i \<subseteq> T i"
    and onto: "\<And>f. (\<And>i. f i \<subseteq> T i) \<Longrightarrow> \<exists>x. P x \<and> (\<forall>i. crd x i = f i)"
    and inj: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> (\<And>i. crd x i = crd y i) \<Longrightarrow> x = y"
    and le: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> leq x y \<longleftrightarrow> (\<forall>i. crd x i \<subseteq> crd y i)"
    and em: "\<And>x. P x \<Longrightarrow> emp x \<longleftrightarrow> (\<forall>i. crd x i = {})"
    and t: "t \<in> T i"
  shows "\<exists>y. P y \<and> (\<forall>j. crd y j = (if j = i then {t} else {})) \<and>
    (\<forall>z. P z \<longrightarrow> ((leq z y \<and> z \<noteq> y) \<longleftrightarrow> emp z))"
proof -
  define f where "f j = (if j = i then {t} else {})" for j
  have fT: "f j \<subseteq> T j" for j using t by (simp add: f_def)
  obtain y where y: "P y" and yc: "\<And>j. crd y j = f j" using onto[OF fT] by blast
  have atom: "(leq z y \<and> z \<noteq> y) \<longleftrightarrow> emp z" if z: "P z" for z
  proof
    assume zy: "leq z y \<and> z \<noteq> y"
    have sub: "crd z j \<subseteq> f j" for j using zy by (simp add: le[OF z y] yc)
    show "emp z"
    proof (rule ccontr)
      assume "\<not> emp z"
      then obtain j s where s: "s \<in> crd z j" using em[OF z] by blast
      have ji: "j = i" and st: "s = t"
        using sub[of j] s by (auto simp: f_def split: if_splits)
      have same: "crd z j' = crd y j'" for j'
      proof (cases "j' = i")
        case True
        then show ?thesis using sub[of j'] s by (auto simp: yc f_def ji st)
      next
        case False
        then show ?thesis using sub[of j'] by (auto simp: yc f_def)
      qed
      have "z = y" by (rule inj[OF z y same])
      with zy show False by blast
    qed
  next
    assume ez: "emp z"
    have "leq z y" using em[OF z] ez by (simp add: le[OF z y])
    moreover have "z \<noteq> y"
    proof
      assume "z = y"
      then have "crd y i = {}" using em[OF z] ez by simp
      then show False by (simp add: yc f_def)
    qed
    ultimately show "leq z y \<and> z \<noteq> y" ..
  qed
  have yc': "\<forall>j. crd y j = (if j = i then {t} else {})"
  proof
    fix j show "crd y j = (if j = i then {t} else {})" by (simp only: yc f_def)
  qed
  have atom': "\<forall>z. P z \<longrightarrow> ((leq z y \<and> z \<noteq> y) \<longleftrightarrow> emp z)"
    by (intro allI impI) (rule atom)
  show ?thesis by (intro exI[of _ y] conjI) (fact y, fact yc', fact atom')
qed

lemma c211_coord_atomic:
  assumes T: "\<And>x i. P x \<Longrightarrow> crd x i \<subseteq> T i"
    and onto: "\<And>f. (\<And>i. f i \<subseteq> T i) \<Longrightarrow> \<exists>x. P x \<and> (\<forall>i. crd x i = f i)"
    and inj: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> (\<And>i. crd x i = crd y i) \<Longrightarrow> x = y"
    and le: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> leq x y \<longleftrightarrow> (\<forall>i. crd x i \<subseteq> crd y i)"
    and em: "\<And>x. P x \<Longrightarrow> emp x \<longleftrightarrow> (\<forall>i. crd x i = {})"
    and x: "P x"
  shows "emp x \<or> (\<exists>y. P y \<and> (\<forall>z. P z \<longrightarrow> ((leq z y \<and> z \<noteq> y) \<longleftrightarrow> emp z)) \<and> leq y x)"
proof (cases "emp x")
  case True
  then show ?thesis ..
next
  case False
  then obtain i t where tx: "t \<in> crd x i" using em[OF x] by blast
  have t: "t \<in> T i" using T[OF x] tx by blast
  obtain y where y: "P y" and yc: "\<forall>j. crd y j = (if j = i then {t} else {})"
    and atom: "\<forall>z. P z \<longrightarrow> ((leq z y \<and> z \<noteq> y) \<longleftrightarrow> emp z)"
    using c211_coord_atom[OF T onto inj le em t] by blast
  have "leq y x" using tx by (simp add: le[OF y x] yc)
  then show ?thesis using y atom by blast
qed

subsection \<open>Free coordinates at the intermediate world and at the root\<close>

theorem c211_middle_free_realize:
  assumes Sm: "Sm \<subseteq> c211_tuples \<sigma>s raw_middle" and L: "L \<subseteq> c211_tuples \<sigma>s raw_limit"
  shows "\<exists>S. Elem S (typed_S (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_middle S = Sm \<and>
    c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S) = L"
proof -
  obtain U where Um: "Elem U (typed_M (paper_type_vector \<sigma>s Prop))"
    and U: "c211_rcur \<sigma>s raw_limit U = L"
    using c211_terminal_realize[OF c211_terminal_worlds(1) L] by blast
  obtain S where "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    "c211_rcur \<sigma>s raw_middle S = Sm" "typed_j (paper_type_vector \<sigma>s Prop) S = U"
    using c211_middle_realize[OF Sm Um] by blast
  then show ?thesis using U by blast
qed

theorem c211_middle_free_unique:
  assumes Sm: "Elem S (typed_S (paper_type_vector \<sigma>s Prop))"
    and S'm: "Elem S' (typed_S (paper_type_vector \<sigma>s Prop))"
    and cur: "c211_rcur \<sigma>s raw_middle S = c211_rcur \<sigma>s raw_middle S'"
    and lim: "c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S) =
      c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S')"
  shows "S = S'"
proof -
  have "typed_j (paper_type_vector \<sigma>s Prop) S = typed_j (paper_type_vector \<sigma>s Prop) S'"
    by (rule c211_terminal_unique[OF c211_terminal_worlds(1)
          typed_j_type[OF Sm] typed_j_type[OF S'm] lim])
  then show ?thesis by (rule c211_middle_unique[OF Sm S'm cur])
qed

theorem c211_root_free_realize:
  assumes Ro: "Ro \<subseteq> c211_tuples \<sigma>s raw_root" and Sm: "Sm \<subseteq> c211_tuples \<sigma>s raw_middle"
    and L: "\<And>n. L n \<subseteq> c211_tuples \<sigma>s (raw_leaf n)"
  shows "\<exists>X. Elem X (typed_R (paper_type_vector \<sigma>s Prop)) \<and>
    c211_rcur \<sigma>s raw_root X = Ro \<and>
    c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X) = Sm \<and>
    (\<forall>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) = L n)"
proof -
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  define N where "N n = (SOME F. Elem F (typed_M ?\<tau>) \<and> c211_rcur \<sigma>s (raw_leaf n) F = L n)"
    for n
  have N: "Elem (N n) (typed_M ?\<tau>) \<and> c211_rcur \<sigma>s (raw_leaf n) (N n) = L n" for n
    unfolding N_def by (rule someI_ex[OF c211_terminal_realize[OF c211_terminal_worlds(2) L]])
  have Nm: "Elem (N n) (typed_M ?\<tau>)" for n using N by blast
  have Um: "Elem (ulim N) (typed_M ?\<tau>)" by (rule typed_ulim_type[OF Nm])
  obtain S where S: "Elem S (typed_S ?\<tau>)" "c211_rcur \<sigma>s raw_middle S = Sm"
    "typed_j ?\<tau> S = ulim N"
    using c211_middle_realize[OF Sm Um] by blast
  obtain X where X: "Elem X (typed_R ?\<tau>)" "c211_rcur \<sigma>s raw_root X = Ro"
    "typed_rs ?\<tau> X = S" "\<forall>n. typed_rn ?\<tau> X n = N n"
    using c211_root_realize[OF Ro S(1) Nm S(3)] by blast
  show ?thesis using X S(2) N by (intro exI[of _ X]) simp
qed

theorem c211_root_free_unique:
  assumes Xm: "Elem X (typed_R (paper_type_vector \<sigma>s Prop))"
    and Ym: "Elem Y (typed_R (paper_type_vector \<sigma>s Prop))"
    and cur: "c211_rcur \<sigma>s raw_root X = c211_rcur \<sigma>s raw_root Y"
    and mid: "c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X) =
      c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) Y)"
    and leaf: "\<And>n. c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n) =
      c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) Y n)"
  shows "X = Y"
proof -
  let ?\<tau> = "paper_type_vector \<sigma>s Prop"
  have rn: "typed_rn ?\<tau> X n = typed_rn ?\<tau> Y n" for n
    by (rule c211_terminal_unique[OF c211_terminal_worlds(2)
          typed_rn_type[OF Xm] typed_rn_type[OF Ym] leaf])
  have rnf: "typed_rn ?\<tau> X = typed_rn ?\<tau> Y" by (rule ext) (rule rn)
  have "typed_j ?\<tau> (typed_rs ?\<tau> X) = typed_j ?\<tau> (typed_rs ?\<tau> Y)"
    by (simp only: typed_R_compatible[OF Xm] typed_R_compatible[OF Ym] rnf)
  then have rs: "typed_rs ?\<tau> X = typed_rs ?\<tau> Y"
    by (rule c211_middle_unique[OF typed_rs_type[OF Xm] typed_rs_type[OF Ym] mid])
  show ?thesis by (rule c211_root_unique[OF Xm Ym cur rs]) (simp add: rn)
qed

subsection \<open>Uniform coordinates at every world\<close>

datatype c211_cix = C211_cur | C211_next | C211_leaf nat

lemma c211_cix_all:
  "(\<forall>i. P i) \<longleftrightarrow> P C211_cur \<and> P C211_next \<and> (\<forall>n. P (C211_leaf n))"
proof
  assume "\<forall>i. P i"
  then show "P C211_cur \<and> P C211_next \<and> (\<forall>n. P (C211_leaf n))" by blast
next
  assume h: "P C211_cur \<and> P C211_next \<and> (\<forall>n. P (C211_leaf n))"
  show "\<forall>i. P i"
  proof
    fix i show "P i" using h by (cases i) simp_all
  qed
qed

text \<open>Root: current, intermediate and leaf coordinates. Intermediate world:
  current and terminal-image coordinates. Terminal worlds: the current
  coordinate. Unused coordinates are constantly empty with empty range.\<close>

definition c211_coord :: "otype list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> c211_cix \<Rightarrow> ZF list set" where
  "c211_coord \<sigma>s w x i =
    (if w = raw_root then
      (case i of C211_cur \<Rightarrow> c211_rcur \<sigma>s raw_root x
        | C211_next \<Rightarrow> c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) x)
        | C211_leaf n \<Rightarrow> c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) x n))
    else if w = raw_middle then
      (case i of C211_cur \<Rightarrow> c211_rcur \<sigma>s raw_middle x
        | C211_next \<Rightarrow> c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) x)
        | C211_leaf n \<Rightarrow> {})
    else (case i of C211_cur \<Rightarrow> c211_rcur \<sigma>s w x | C211_next \<Rightarrow> {} | C211_leaf n \<Rightarrow> {}))"

definition c211_ctuples :: "otype list \<Rightarrow> ZF \<Rightarrow> c211_cix \<Rightarrow> ZF list set" where
  "c211_ctuples \<sigma>s w i =
    (if w = raw_root then
      (case i of C211_cur \<Rightarrow> c211_tuples \<sigma>s raw_root | C211_next \<Rightarrow> c211_tuples \<sigma>s raw_middle
        | C211_leaf n \<Rightarrow> c211_tuples \<sigma>s (raw_leaf n))
    else if w = raw_middle then
      (case i of C211_cur \<Rightarrow> c211_tuples \<sigma>s raw_middle | C211_next \<Rightarrow> c211_tuples \<sigma>s raw_limit
        | C211_leaf n \<Rightarrow> {})
    else (case i of C211_cur \<Rightarrow> c211_tuples \<sigma>s w | C211_next \<Rightarrow> {} | C211_leaf n \<Rightarrow> {}))"

lemma c211_terminal_ne:
  assumes "c211_terminal w"
  shows "w \<noteq> raw_root" "w \<noteq> raw_middle"
  using assms by (auto simp: c211_terminal_def)

lemma c211_coord_root [simp]:
  "c211_coord \<sigma>s raw_root X C211_cur = c211_rcur \<sigma>s raw_root X"
  "c211_coord \<sigma>s raw_root X C211_next =
    c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) X)"
  "c211_coord \<sigma>s raw_root X (C211_leaf n) =
    c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) X n)"
  "c211_ctuples \<sigma>s raw_root C211_cur = c211_tuples \<sigma>s raw_root"
  "c211_ctuples \<sigma>s raw_root C211_next = c211_tuples \<sigma>s raw_middle"
  "c211_ctuples \<sigma>s raw_root (C211_leaf n) = c211_tuples \<sigma>s (raw_leaf n)"
  by (simp_all add: c211_coord_def c211_ctuples_def)

lemma c211_coord_middle [simp]:
  "c211_coord \<sigma>s raw_middle S C211_cur = c211_rcur \<sigma>s raw_middle S"
  "c211_coord \<sigma>s raw_middle S C211_next =
    c211_rcur \<sigma>s raw_limit (typed_j (paper_type_vector \<sigma>s Prop) S)"
  "c211_coord \<sigma>s raw_middle S (C211_leaf n) = {}"
  "c211_ctuples \<sigma>s raw_middle C211_cur = c211_tuples \<sigma>s raw_middle"
  "c211_ctuples \<sigma>s raw_middle C211_next = c211_tuples \<sigma>s raw_limit"
  "c211_ctuples \<sigma>s raw_middle (C211_leaf n) = {}"
  by (simp_all add: c211_coord_def c211_ctuples_def)

lemma c211_coord_terminal:
  assumes "c211_terminal w"
  shows "c211_coord \<sigma>s w F C211_cur = c211_rcur \<sigma>s w F"
    "c211_coord \<sigma>s w F C211_next = {}" "c211_coord \<sigma>s w F (C211_leaf n) = {}"
    "c211_ctuples \<sigma>s w C211_cur = c211_tuples \<sigma>s w"
    "c211_ctuples \<sigma>s w C211_next = {}" "c211_ctuples \<sigma>s w (C211_leaf n) = {}"
  using c211_terminal_ne[OF assms] by (simp_all add: c211_coord_def c211_ctuples_def)

theorem c211_coord_tuples: "c211_coord \<sigma>s w x i \<subseteq> c211_ctuples \<sigma>s w i"
  by (cases i) (simp_all add: c211_coord_def c211_ctuples_def c211_rcur_tuples)

lemma c211_world_trichotomy [consumes 1, case_names root middle terminal]:
  assumes "Elem w raw_W"
  obtains "w = raw_root" | "w = raw_middle" | "c211_terminal w"
  using assms by (cases rule: c211_world_exhaust) (auto simp: c211_terminal_def)

lemma c211_terminal_raw_form:
  assumes "c211_terminal w"
  obtains n where "w = raw_limit \<or> w = raw_leaf n"
  using assms by (auto simp: c211_terminal_def)

subsubsection \<open>The coordinate map is onto the product\<close>

lemma c211_coord_onto_root:
  assumes f: "\<And>i. f i \<subseteq> c211_ctuples \<sigma>s raw_root i"
  shows "\<exists>X. Elem X (typed_R (paper_type_vector \<sigma>s Prop)) \<and>
    (\<forall>i. c211_coord \<sigma>s raw_root X i = f i)"
proof -
  have f1: "f C211_cur \<subseteq> c211_tuples \<sigma>s raw_root" using f[of C211_cur] by simp
  have f2: "f C211_next \<subseteq> c211_tuples \<sigma>s raw_middle" using f[of C211_next] by simp
  have f3: "f (C211_leaf n) \<subseteq> c211_tuples \<sigma>s (raw_leaf n)" for n
    using f[of "C211_leaf n"] by simp
  show ?thesis
    using c211_root_free_realize[where L="\<lambda>n. f (C211_leaf n)", OF f1 f2 f3]
    by (simp add: c211_cix_all)
qed

lemma c211_coord_onto_middle:
  assumes f: "\<And>i. f i \<subseteq> c211_ctuples \<sigma>s raw_middle i"
  shows "\<exists>S. Elem S (typed_S (paper_type_vector \<sigma>s Prop)) \<and>
    (\<forall>i. c211_coord \<sigma>s raw_middle S i = f i)"
proof -
  have f1: "f C211_cur \<subseteq> c211_tuples \<sigma>s raw_middle" using f[of C211_cur] by simp
  have f2: "f C211_next \<subseteq> c211_tuples \<sigma>s raw_limit" using f[of C211_next] by simp
  have f3: "f (C211_leaf n) = {}" for n using f[of "C211_leaf n"] by simp
  show ?thesis using c211_middle_free_realize[OF f1 f2] by (simp add: c211_cix_all f3)
qed

lemma c211_coord_onto_terminal:
  assumes w: "c211_terminal w" and f: "\<And>i. f i \<subseteq> c211_ctuples \<sigma>s w i"
  shows "\<exists>F. Elem F (typed_M (paper_type_vector \<sigma>s Prop)) \<and>
    (\<forall>i. c211_coord \<sigma>s w F i = f i)"
proof -
  have f1: "f C211_cur \<subseteq> c211_tuples \<sigma>s w"
    using f[of C211_cur] by (simp add: c211_coord_terminal[OF w])
  have f2: "f C211_next = {}" "f (C211_leaf n) = {}" for n
    using f[of C211_next] f[of "C211_leaf n"] by (simp_all add: c211_coord_terminal[OF w])
  show ?thesis using c211_terminal_realize[OF w f1]
    by (simp add: c211_cix_all f2 c211_coord_terminal[OF w])
qed

theorem c211_coord_onto:
  assumes w: "Elem w raw_W" and f: "\<And>i. f i \<subseteq> c211_ctuples \<sigma>s w i"
  shows "\<exists>x. Elem x (raw_D (paper_type_vector \<sigma>s Prop) w) \<and> (\<forall>i. c211_coord \<sigma>s w x i = f i)"
  using w
proof (cases rule: c211_world_trichotomy)
  case root
  have f': "f i \<subseteq> c211_ctuples \<sigma>s raw_root i" for i using f[of i] by (simp add: root)
  show ?thesis using c211_coord_onto_root[OF f'] by (simp add: root)
next
  case middle
  have f': "f i \<subseteq> c211_ctuples \<sigma>s raw_middle i" for i using f[of i] by (simp add: middle)
  show ?thesis using c211_coord_onto_middle[OF f'] by (simp add: middle)
next
  case terminal
  show ?thesis using c211_coord_onto_terminal[OF terminal f] by (simp add: c211_terminal_simps[OF terminal])
qed

subsubsection \<open>The coordinate map is injective\<close>

theorem c211_coord_inj:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ym: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and same: "\<And>i. c211_coord \<sigma>s w x i = c211_coord \<sigma>s w y i"
  shows "x = y"
  using w
proof (cases rule: c211_world_trichotomy)
  case root
  have xR: "Elem x (typed_R (paper_type_vector \<sigma>s Prop))"
    and yR: "Elem y (typed_R (paper_type_vector \<sigma>s Prop))" using xm ym by (simp_all add: root)
  show ?thesis
  proof (rule c211_root_free_unique[OF xR yR])
    show "c211_rcur \<sigma>s raw_root x = c211_rcur \<sigma>s raw_root y"
      using same[of C211_cur] by (simp add: root)
    show "c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) x) =
        c211_rcur \<sigma>s raw_middle (typed_rs (paper_type_vector \<sigma>s Prop) y)"
      using same[of C211_next] by (simp add: root)
    fix n
    show "c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) x n) =
        c211_rcur \<sigma>s (raw_leaf n) (typed_rn (paper_type_vector \<sigma>s Prop) y n)"
      using same[of "C211_leaf n"] by (simp add: root)
  qed
next
  case middle
  have xS: "Elem x (typed_S (paper_type_vector \<sigma>s Prop))"
    and yS: "Elem y (typed_S (paper_type_vector \<sigma>s Prop))" using xm ym by (simp_all add: middle)
  show ?thesis
    by (rule c211_middle_free_unique[OF xS yS])
      (use same[of C211_cur] same[of C211_next] in \<open>simp_all add: middle\<close>)
next
  case terminal
  have xM: "Elem x (typed_M (paper_type_vector \<sigma>s Prop))"
    and yM: "Elem y (typed_M (paper_type_vector \<sigma>s Prop))"
    using xm ym by (simp_all add: c211_terminal_simps[OF terminal])
  show ?thesis
    by (rule c211_terminal_unique[OF terminal xM yM])
      (use same[of C211_cur] in \<open>simp add: c211_coord_terminal[OF terminal]\<close>)
qed

subsubsection \<open>Order and emptiness are coordinatewise\<close>

theorem c211_rleq_coord:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ym: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x y \<longleftrightarrow>
    (\<forall>i. c211_coord \<sigma>s w x i \<subseteq> c211_coord \<sigma>s w y i)"
  using w
proof (cases rule: c211_world_trichotomy)
  case root
  have xR: "Elem x (typed_R (paper_type_vector \<sigma>s Prop))"
    and yR: "Elem y (typed_R (paper_type_vector \<sigma>s Prop))" using xm ym by (simp_all add: root)
  show ?thesis by (simp add: root c211_rleq_root[OF xR yR] c211_cix_all)
next
  case middle
  have xS: "Elem x (typed_S (paper_type_vector \<sigma>s Prop))"
    and yS: "Elem y (typed_S (paper_type_vector \<sigma>s Prop))" using xm ym by (simp_all add: middle)
  show ?thesis by (simp add: middle c211_rleq_middle[OF xS yS] c211_cix_all)
next
  case terminal
  obtain n where wn: "w = raw_limit \<or> w = raw_leaf n" by (rule c211_terminal_raw_form[OF terminal])
  show ?thesis
    by (simp add: c211_rleq_terminal[OF wn xm ym] c211_cix_all c211_coord_terminal[OF terminal])
qed

theorem c211_rempty_coord:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rempty (paper_type_vector \<sigma>s Prop) w x \<longleftrightarrow> (\<forall>i. c211_coord \<sigma>s w x i = {})"
  using w
proof (cases rule: c211_world_trichotomy)
  case root
  have xR: "Elem x (typed_R (paper_type_vector \<sigma>s Prop))" using xm by (simp add: root)
  show ?thesis by (simp add: root c211_rempty_root[OF xR] c211_cix_all)
next
  case middle
  have xS: "Elem x (typed_S (paper_type_vector \<sigma>s Prop))" using xm by (simp add: middle)
  show ?thesis by (simp add: middle c211_rempty_middle[OF xS] c211_cix_all)
next
  case terminal
  obtain n where wn: "w = raw_limit \<or> w = raw_leaf n" by (rule c211_terminal_raw_form[OF terminal])
  show ?thesis
    by (simp add: c211_rempty_terminal[OF wn xm] c211_cix_all c211_coord_terminal[OF terminal])
qed

subsection \<open>Order facts\<close>

theorem c211_rleq_refl:
  assumes "Elem w raw_W" "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x x"
  by (simp add: c211_rleq_coord[OF assms(1,2,2)])

theorem c211_rleq_trans:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ym: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and zm: "Elem z (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and xy: "c211_rleq (paper_type_vector \<sigma>s Prop) w x y"
    and yz: "c211_rleq (paper_type_vector \<sigma>s Prop) w y z"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x z"
  using xy yz unfolding c211_rleq_coord[OF w xm ym] c211_rleq_coord[OF w ym zm]
    c211_rleq_coord[OF w xm zm] by blast

theorem c211_rleq_antisym:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ym: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and xy: "c211_rleq (paper_type_vector \<sigma>s Prop) w x y"
    and yx: "c211_rleq (paper_type_vector \<sigma>s Prop) w y x"
  shows "x = y"
proof (rule c211_coord_inj[OF w xm ym])
  fix i
  show "c211_coord \<sigma>s w x i = c211_coord \<sigma>s w y i"
    using xy yx unfolding c211_rleq_coord[OF w xm ym] c211_rleq_coord[OF w ym xm] by blast
qed

theorem c211_rempty_rleq:
  assumes w: "Elem w raw_W"
    and xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ym: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
    and ex: "c211_rempty (paper_type_vector \<sigma>s Prop) w x"
  shows "c211_rleq (paper_type_vector \<sigma>s Prop) w x y"
  using ex by (simp add: c211_rempty_coord[OF w xm] c211_rleq_coord[OF w xm ym])

subsection \<open>Meets, atoms, completeness and atomicity\<close>

lemma c211_ex_drop_middle: "\<exists>m. A m \<and> B m \<and> C m \<Longrightarrow> \<exists>m. A m \<and> C m"
  by blast

theorem c211_raw_glb:
  assumes w: "Elem w raw_W"
    and S: "\<And>y. y \<in> S \<Longrightarrow> Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)"
  shows "\<exists>m. Elem m (raw_D (paper_type_vector \<sigma>s Prop) w) \<and>
    (\<forall>i. c211_coord \<sigma>s w m i = {t \<in> c211_ctuples \<sigma>s w i. \<forall>y\<in>S. t \<in> c211_coord \<sigma>s w y i}) \<and>
    (\<forall>z. Elem z (raw_D (paper_type_vector \<sigma>s Prop) w) \<longrightarrow>
      ((\<forall>y\<in>S. c211_rleq (paper_type_vector \<sigma>s Prop) w z y) \<longleftrightarrow>
        c211_rleq (paper_type_vector \<sigma>s Prop) w z m))"
  by (rule c211_coord_glb[where P="\<lambda>x. Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
        and crd="c211_coord \<sigma>s w" and T="c211_ctuples \<sigma>s w"
        and leq="c211_rleq (paper_type_vector \<sigma>s Prop) w",
        OF c211_coord_tuples c211_coord_onto[OF w] c211_rleq_coord[OF w] S])

theorem c211_raw_atom:
  assumes w: "Elem w raw_W" and t: "t \<in> c211_ctuples \<sigma>s w i"
  shows "\<exists>y. Elem y (raw_D (paper_type_vector \<sigma>s Prop) w) \<and>
    (\<forall>j. c211_coord \<sigma>s w y j = (if j = i then {t} else {})) \<and>
    c211_ratom (paper_type_vector \<sigma>s Prop) w y"
  unfolding c211_ratom_def
  by (rule c211_coord_atom[where P="\<lambda>x. Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
        and crd="c211_coord \<sigma>s w" and T="c211_ctuples \<sigma>s w"
        and leq="c211_rleq (paper_type_vector \<sigma>s Prop) w"
        and emp="c211_rempty (paper_type_vector \<sigma>s Prop) w",
        OF c211_coord_tuples c211_coord_onto[OF w] c211_coord_inj[OF w]
        c211_rleq_coord[OF w] c211_rempty_coord[OF w] t])

theorem c211_raw_complete:
  assumes w: "Elem w raw_W"
  shows "c211_rcomplete (paper_type_vector \<sigma>s Prop) w"
  unfolding c211_rcomplete_def
proof (intro allI impI)
  fix S assume S: "S \<subseteq> explode (raw_D (paper_type_vector \<sigma>s Prop) w)"
  have Sy: "Elem y (raw_D (paper_type_vector \<sigma>s Prop) w)" if "y \<in> S" for y
    using subsetD[OF S that] by (simp only: explode_Elem)
  show "\<exists>m. Elem m (raw_D (paper_type_vector \<sigma>s Prop) w) \<and>
      (\<forall>z. Elem z (raw_D (paper_type_vector \<sigma>s Prop) w) \<longrightarrow>
        ((\<forall>y\<in>S. c211_rleq (paper_type_vector \<sigma>s Prop) w z y) \<longleftrightarrow>
          c211_rleq (paper_type_vector \<sigma>s Prop) w z m))"
    by (rule c211_ex_drop_middle[OF c211_raw_glb[OF w Sy]])
qed

corollary c211_raw_complete_root: "c211_rcomplete (paper_type_vector \<sigma>s Prop) raw_root"
  by (rule c211_raw_complete[OF raw_worlds(1)])

theorem c211_raw_atomic:
  assumes w: "Elem w raw_W"
  shows "c211_ratomic (paper_type_vector \<sigma>s Prop) w"
  unfolding c211_ratomic_def c211_ratom_def
proof (intro allI impI)
  fix x assume xm: "Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
  show "c211_rempty (paper_type_vector \<sigma>s Prop) w x \<or>
      (\<exists>y. Elem y (raw_D (paper_type_vector \<sigma>s Prop) w) \<and>
        (\<forall>z. Elem z (raw_D (paper_type_vector \<sigma>s Prop) w) \<longrightarrow>
          ((c211_rleq (paper_type_vector \<sigma>s Prop) w z y \<and> z \<noteq> y) \<longleftrightarrow>
            c211_rempty (paper_type_vector \<sigma>s Prop) w z)) \<and>
        c211_rleq (paper_type_vector \<sigma>s Prop) w y x)"
    by (rule c211_coord_atomic[where P="\<lambda>x. Elem x (raw_D (paper_type_vector \<sigma>s Prop) w)"
          and crd="c211_coord \<sigma>s w" and T="c211_ctuples \<sigma>s w"
          and leq="c211_rleq (paper_type_vector \<sigma>s Prop) w"
          and emp="c211_rempty (paper_type_vector \<sigma>s Prop) w",
          OF c211_coord_tuples c211_coord_onto[OF w] c211_coord_inj[OF w]
          c211_rleq_coord[OF w] c211_rempty_coord[OF w] xm])
qed

ML \<open>
  val facts = [@{thm c211_coord_glb}, @{thm c211_coord_atom}, @{thm c211_coord_atomic},
    @{thm c211_middle_free_realize}, @{thm c211_middle_free_unique},
    @{thm c211_root_free_realize}, @{thm c211_root_free_unique},
    @{thm c211_coord_tuples}, @{thm c211_coord_onto}, @{thm c211_coord_inj},
    @{thm c211_rleq_coord}, @{thm c211_rempty_coord},
    @{thm c211_rleq_refl}, @{thm c211_rleq_trans}, @{thm c211_rleq_antisym},
    @{thm c211_rempty_rleq}, @{thm c211_raw_glb}, @{thm c211_raw_atom},
    @{thm c211_raw_complete}, @{thm c211_raw_complete_root}, @{thm c211_raw_atomic}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln "C211-RAW-LATTICE: raw relational carriers are complete and atomic at every world";
\<close>

end
