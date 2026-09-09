theory Bacon_Source_Typed_Arrows
  imports Bacon_Source_Typed_Map_Normalization
begin

section \<open>Arrows with specified typed domains\<close>

text \<open>
  A map f:A→B consists of functions fσ:D(A)σ→D(B)σ, together
  with its specified source A and target B. This implements the
  domain-restricted functions used in Bacon–Dorr §3.3, p.49.
  We normalize each total HOL extension outside D(A)σ. Hence two
  arrows with the same endpoints are equal precisely when their
  maps agree on those domains, rather than on irrelevant arguments.

  This is generic typed-map syntax. Objects and values have fixed,
  arbitrary HOL carriers; domains may overlap or be empty. No
  interpretation, valuation, BBK model or denotation preservation is
  required. The later BBK category must restrict these arrows further.
\<close>

record ('o, 'v) paper_typed_arrow =
  paper_arrow_source :: 'o
  paper_arrow_target :: 'o
  paper_arrow_map :: "otype \<Rightarrow> 'v \<Rightarrow> 'v"

definition paper_typed_arrows ::
  "'o set \<Rightarrow> ('o \<Rightarrow> otype \<Rightarrow> 'v set) \<Rightarrow> ('o, 'v) paper_typed_arrow set" where
  "paper_typed_arrows Obj D = {f.
    paper_arrow_source f \<in> Obj \<and> paper_arrow_target f \<in> Obj \<and>
    (\<forall>\<sigma> a. a \<in> D (paper_arrow_source f) \<sigma> \<longrightarrow>
      paper_arrow_map f \<sigma> a \<in> D (paper_arrow_target f) \<sigma>) \<and>
    paper_typed_map_normal (D (paper_arrow_source f)) (paper_arrow_map f)}"

definition paper_typed_identity ::
  "('o \<Rightarrow> otype \<Rightarrow> 'v set) \<Rightarrow> 'o \<Rightarrow> ('o, 'v) paper_typed_arrow" where
  "paper_typed_identity D A = \<lparr>paper_arrow_source = A, paper_arrow_target = A,
    paper_arrow_map = paper_typed_map_normalize (D A) (\<lambda>\<sigma> a. a)\<rparr>"

definition paper_typed_compose ::
  "('o \<Rightarrow> otype \<Rightarrow> 'v set) \<Rightarrow> ('o, 'v) paper_typed_arrow \<Rightarrow>
    ('o, 'v) paper_typed_arrow \<Rightarrow> ('o, 'v) paper_typed_arrow" where
  "paper_typed_compose D g f =
    \<lparr>paper_arrow_source = paper_arrow_source f, paper_arrow_target = paper_arrow_target g,
     paper_arrow_map = paper_typed_map_normalize (D (paper_arrow_source f))
       (\<lambda>\<sigma> a. paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a))\<rparr>"

lemma paper_typed_arrowsI:
  assumes src: "paper_arrow_source f \<in> Obj" and tgt: "paper_arrow_target f \<in> Obj"
    and maps: "\<And>\<sigma> a. a \<in> D (paper_arrow_source f) \<sigma> \<Longrightarrow>
      paper_arrow_map f \<sigma> a \<in> D (paper_arrow_target f) \<sigma>"
    and normal: "paper_typed_map_normal (D (paper_arrow_source f)) (paper_arrow_map f)"
  shows "f \<in> paper_typed_arrows Obj D"
  using src tgt maps normal unfolding paper_typed_arrows_def by blast

lemma paper_typed_arrows_source:
  "f \<in> paper_typed_arrows Obj D \<Longrightarrow> paper_arrow_source f \<in> Obj"
  unfolding paper_typed_arrows_def by blast

lemma paper_typed_arrows_target:
  "f \<in> paper_typed_arrows Obj D \<Longrightarrow> paper_arrow_target f \<in> Obj"
  unfolding paper_typed_arrows_def by blast

lemma paper_typed_arrows_map:
  assumes arrow: "f \<in> paper_typed_arrows Obj D"
    and member: "a \<in> D (paper_arrow_source f) \<sigma>"
  shows "paper_arrow_map f \<sigma> a \<in> D (paper_arrow_target f) \<sigma>"
  using arrow member unfolding paper_typed_arrows_def by blast

lemma paper_typed_arrows_normal:
  "f \<in> paper_typed_arrows Obj D \<Longrightarrow>
    paper_typed_map_normal (D (paper_arrow_source f)) (paper_arrow_map f)"
  unfolding paper_typed_arrows_def by blast

lemma paper_typed_identity_endpoints [simp]:
  "paper_arrow_source (paper_typed_identity D A) = A"
  "paper_arrow_target (paper_typed_identity D A) = A"
  by (simp_all only: paper_typed_identity_def paper_typed_arrow.select_convs)

lemma paper_typed_compose_endpoints [simp]:
  "paper_arrow_source (paper_typed_compose D g f) = paper_arrow_source f"
  "paper_arrow_target (paper_typed_compose D g f) = paper_arrow_target g"
  by (simp_all only: paper_typed_compose_def paper_typed_arrow.select_convs)

lemma paper_typed_identity_map_on:
  assumes member: "a \<in> D A \<sigma>"
  shows "paper_arrow_map (paper_typed_identity D A) \<sigma> a = a"
  by (simp only: paper_typed_identity_def paper_typed_arrow.select_convs
    paper_typed_map_normalize_on_domain[where D="D A" and \<sigma>=\<sigma>, OF member])

lemma paper_typed_compose_map_on:
  assumes member: "a \<in> D (paper_arrow_source f) \<sigma>"
  shows "paper_arrow_map (paper_typed_compose D g f) \<sigma> a =
    paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a)"
  by (simp only: paper_typed_compose_def paper_typed_arrow.select_convs
    paper_typed_map_normalize_on_domain[where D="D (paper_arrow_source f)" and \<sigma>=\<sigma>, OF member])

lemma paper_typed_arrow_ext:
  fixes f g :: "('o, 'v) paper_typed_arrow"
  assumes first: "f \<in> paper_typed_arrows Obj D" and second: "g \<in> paper_typed_arrows Obj D"
    and src: "paper_arrow_source f = paper_arrow_source g"
    and tgt: "paper_arrow_target f = paper_arrow_target g"
    and agree: "\<And>\<sigma> a. a \<in> D (paper_arrow_source f) \<sigma> \<Longrightarrow>
      paper_arrow_map f \<sigma> a = paper_arrow_map g \<sigma> a"
  shows "f = g"
proof -
  have fn: "paper_typed_map_normal (D (paper_arrow_source f)) (paper_arrow_map f)"
    by (rule paper_typed_arrows_normal[OF first])
  have gn: "paper_typed_map_normal (D (paper_arrow_source g)) (paper_arrow_map g)"
    by (rule paper_typed_arrows_normal[OF second])
  have maps_eq: "paper_arrow_map f = paper_arrow_map g"
  proof (rule ext, rule ext)
    fix \<sigma> a
    show "paper_arrow_map f \<sigma> a = paper_arrow_map g \<sigma> a"
    proof (cases "a \<in> D (paper_arrow_source f) \<sigma>")
      case True
      show ?thesis by (rule agree[OF True])
    next
      case False
      have outside: "a \<notin> D (paper_arrow_source g) \<sigma>" using False by (simp add: src)
      have fv: "paper_arrow_map f \<sigma> a = undefined"
        using fn False unfolding paper_typed_map_normal_def by blast
      have gv: "paper_arrow_map g \<sigma> a = undefined"
        using gn outside unfolding paper_typed_map_normal_def by blast
      show ?thesis by (simp only: fv gv)
    qed
  qed
  show ?thesis using src tgt maps_eq by (cases f; cases g; simp_all)
qed

lemma paper_typed_identity_arrow:
  assumes object: "A \<in> Obj"
  shows "paper_typed_identity D A \<in> paper_typed_arrows Obj D"
proof (rule paper_typed_arrowsI)
  show "paper_arrow_source (paper_typed_identity D A) \<in> Obj" by (simp only: paper_typed_identity_endpoints; rule object)
  show "paper_arrow_target (paper_typed_identity D A) \<in> Obj" by (simp only: paper_typed_identity_endpoints; rule object)
  show "paper_typed_map_normal (D (paper_arrow_source (paper_typed_identity D A)))
      (paper_arrow_map (paper_typed_identity D A))"
    by (simp only: paper_typed_identity_def paper_typed_arrow.select_convs;
      rule paper_typed_map_normalize_normal)
next
  fix \<sigma> a
  assume member: "a \<in> D (paper_arrow_source (paper_typed_identity D A)) \<sigma>"
  have am: "a \<in> D A \<sigma>" using member by (simp only: paper_typed_identity_endpoints)
  show "paper_arrow_map (paper_typed_identity D A) \<sigma> a \<in>
      D (paper_arrow_target (paper_typed_identity D A)) \<sigma>"
    by (simp only: paper_typed_identity_endpoints
      paper_typed_identity_map_on[where D=D and A=A and \<sigma>=\<sigma>, OF am]; rule am)
qed

lemma paper_typed_compose_arrow:
  assumes first: "f \<in> paper_typed_arrows Obj D" and second: "g \<in> paper_typed_arrows Obj D"
    and meeting: "paper_arrow_target f = paper_arrow_source g"
  shows "paper_typed_compose D g f \<in> paper_typed_arrows Obj D"
proof (rule paper_typed_arrowsI)
  show "paper_arrow_source (paper_typed_compose D g f) \<in> Obj"
    by (simp only: paper_typed_compose_endpoints; rule paper_typed_arrows_source[OF first])
  show "paper_arrow_target (paper_typed_compose D g f) \<in> Obj"
    by (simp only: paper_typed_compose_endpoints; rule paper_typed_arrows_target[OF second])
  show "paper_typed_map_normal (D (paper_arrow_source (paper_typed_compose D g f)))
      (paper_arrow_map (paper_typed_compose D g f))"
    by (simp only: paper_typed_compose_def paper_typed_arrow.select_convs;
      rule paper_typed_map_normalize_normal)
next
  fix \<sigma> a
  assume member: "a \<in> D (paper_arrow_source (paper_typed_compose D g f)) \<sigma>"
  have am: "a \<in> D (paper_arrow_source f) \<sigma>" using member by (simp only: paper_typed_compose_endpoints)
  have fm: "paper_arrow_map f \<sigma> a \<in> D (paper_arrow_source g) \<sigma>"
    using paper_typed_arrows_map[OF first am] by (simp only: meeting)
  have gm: "paper_arrow_map g \<sigma> (paper_arrow_map f \<sigma> a) \<in> D (paper_arrow_target g) \<sigma>"
    by (rule paper_typed_arrows_map[OF second fm])
  show "paper_arrow_map (paper_typed_compose D g f) \<sigma> a \<in>
      D (paper_arrow_target (paper_typed_compose D g f)) \<sigma>"
    by (simp only: paper_typed_compose_endpoints
      paper_typed_compose_map_on[where D=D and f=f and \<sigma>=\<sigma>, OF am]; rule gm)
qed

lemma paper_typed_arrows_empty [simp]: "paper_typed_arrows {} D = {}"
  unfolding paper_typed_arrows_def by simp

end
