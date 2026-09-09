theory Bacon_Source_Typed_Map_Normalization
  imports Bacon_Source_BBK_Homomorphism
begin

section \<open>Canonical extensions of functions hσ:Dσ→Eσ\<close>

text \<open>
  A source homomorphism has components hσ defined on Dσ.
  Source: Bacon–Dorr §3.3, p.49. Isabelle functions are total on
  their ambient HOL type, so we choose undefined outside Dσ.
  This choice makes equality of normalized extensions coincide with
  agreement on the actual domains. It adds no source semantic axiom.

  Source and target carriers may differ. No assumption says that
  undefined lies outside a semantic domain. Its role is only to fix
  irrelevant off-domain values. Preservation of denotation additionally
  uses the explicitly guarded typing of the source interpretation.
\<close>

definition paper_typed_map_normalize ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow>
    otype \<Rightarrow> 'v \<Rightarrow> 'w" where
  "paper_typed_map_normalize D h \<sigma> a = (if a \<in> D \<sigma> then h \<sigma> a else undefined)"

definition paper_typed_map_normal ::
  "(otype \<Rightarrow> 'v set) \<Rightarrow> (otype \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> bool" where
  "paper_typed_map_normal D h \<longleftrightarrow> (\<forall>\<sigma> a. a \<notin> D \<sigma> \<longrightarrow> h \<sigma> a = undefined)"

lemma paper_typed_map_normalize_on_domain:
  assumes member: "a \<in> D \<sigma>"
  shows "paper_typed_map_normalize D h \<sigma> a = h \<sigma> a"
  by (simp only: paper_typed_map_normalize_def if_P[OF member])

lemma paper_typed_map_normalize_off_domain:
  assumes outside: "a \<notin> D \<sigma>"
  shows "paper_typed_map_normalize D h \<sigma> a = undefined"
  by (simp only: paper_typed_map_normalize_def if_not_P[OF outside])

lemma paper_typed_map_normalize_normal:
  "paper_typed_map_normal D (paper_typed_map_normalize D h)"
  unfolding paper_typed_map_normal_def
  by (intro allI impI; rule paper_typed_map_normalize_off_domain; assumption)

lemma paper_typed_map_normalize_fixes_normal:
  assumes normal: "paper_typed_map_normal D h"
  shows "paper_typed_map_normalize D h = h"
proof (rule ext, rule ext)
  fix \<sigma> a
  show "paper_typed_map_normalize D h \<sigma> a = h \<sigma> a"
  proof (cases "a \<in> D \<sigma>")
    case True
    show ?thesis by (rule paper_typed_map_normalize_on_domain[where D=D and \<sigma>=\<sigma>, OF True])
  next
    case False
    have old: "h \<sigma> a = undefined"
      using normal False unfolding paper_typed_map_normal_def by blast
    show ?thesis by (simp only: paper_typed_map_normalize_off_domain[where D=D and \<sigma>=\<sigma>, OF False] old)
  qed
qed

lemma paper_typed_map_normalize_idempotent:
  "paper_typed_map_normalize D (paper_typed_map_normalize D h) = paper_typed_map_normalize D h"
  by (rule paper_typed_map_normalize_fixes_normal[OF paper_typed_map_normalize_normal])

theorem paper_typed_map_normalized_eq_iff:
  "paper_typed_map_normalize D h = paper_typed_map_normalize D k \<longleftrightarrow>
    (\<forall>\<sigma> a. a \<in> D \<sigma> \<longrightarrow> h \<sigma> a = k \<sigma> a)"
proof
  assume equality: "paper_typed_map_normalize D h = paper_typed_map_normalize D k"
  show "\<forall>\<sigma> a. a \<in> D \<sigma> \<longrightarrow> h \<sigma> a = k \<sigma> a"
  proof (intro allI impI)
    fix \<sigma> a
    assume member: "a \<in> D \<sigma>"
    have point: "paper_typed_map_normalize D h \<sigma> a = paper_typed_map_normalize D k \<sigma> a"
      by (rule fun_cong[OF fun_cong[OF equality]])
    show "h \<sigma> a = k \<sigma> a" using point
      by (simp only: paper_typed_map_normalize_on_domain[where D=D and \<sigma>=\<sigma>, OF member])
  qed
next
  assume agree: "\<forall>\<sigma> a. a \<in> D \<sigma> \<longrightarrow> h \<sigma> a = k \<sigma> a"
  show "paper_typed_map_normalize D h = paper_typed_map_normalize D k"
  proof (rule ext, rule ext)
    fix \<sigma> a
    show "paper_typed_map_normalize D h \<sigma> a = paper_typed_map_normalize D k \<sigma> a"
    proof (cases "a \<in> D \<sigma>")
      case True
      have same: "h \<sigma> a = k \<sigma> a" using agree True by blast
      show ?thesis by (simp only: paper_typed_map_normalize_on_domain[where D=D and \<sigma>=\<sigma>, OF True] same)
    next
      case False
      show ?thesis by (simp only: paper_typed_map_normalize_off_domain[where D=D and \<sigma>=\<sigma>, OF False])
    qed
  qed
qed

section \<open>Normalization preserves homomorphisms on typed interpretations\<close>

text \<open>
  Replacing h by its normalized extension leaves hσ(⟦A⟧ᵍ) and
  h∘g unchanged when ⟦A⟧ᵍ∈Dσ and g is typed.
  The first theorem states precisely this interpretation-typing
  premise; the corollary obtains it from an independently supplied
  source BBK model. Neither theorem constrains valuations under h.
\<close>

theorem paper_typed_map_normalize_homomorphism:
  assumes hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
    and source_typed: "\<And>A \<sigma> g. named_in_language paper_logical_type \<Sigma> G A \<sigma> \<Longrightarrow>
      named_env_typed D G g \<Longrightarrow> named_adequate g A \<Longrightarrow> J g A \<in> D \<sigma>"
  shows "paper_bbk_homomorphism \<Sigma> G D J E K (paper_typed_map_normalize D h)"
proof (rule paper_bbk_homomorphism_cong[OF hom source_typed])
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  show "h \<sigma> a = paper_typed_map_normalize D h \<sigma> a"
    by (rule sym[OF paper_typed_map_normalize_on_domain[where D=D and \<sigma>=\<sigma>, OF member]])
qed

corollary paper_typed_map_normalize_homomorphism_from_model:
  assumes source_model: "paper_named_bbk_model \<Sigma> G D J V"
    and hom: "paper_bbk_homomorphism \<Sigma> G D J E K h"
  shows "paper_bbk_homomorphism \<Sigma> G D J E K (paper_typed_map_normalize D h)"
proof -
  interpret Source: paper_named_bbk_model \<Sigma> G D J V by (rule source_model)
  show ?thesis
  proof (rule paper_typed_map_normalize_homomorphism[OF hom])
    fix A \<sigma> g
    assume language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
      and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
    show "J g A \<in> D \<sigma>" by (rule Source.denote_type[OF language typed adequate])
  qed
qed

section \<open>Normalized composition\<close>

text \<open>
  On Dσ, composing the normalized extensions agrees with kσ∘hσ,
  provided hσ(Dσ)⊆Eσ. Normalizing the composite therefore gives
  the same total function. The domain-mapping premise is essential:
  without it the intermediate value could reach the off-domain default.
\<close>

theorem paper_typed_map_normalize_compose:
  assumes maps: "\<And>\<sigma> a. a \<in> D \<sigma> \<Longrightarrow> h \<sigma> a \<in> E \<sigma>"
  shows "paper_typed_map_normalize D
      (\<lambda>\<sigma> a. paper_typed_map_normalize E k \<sigma> (paper_typed_map_normalize D h \<sigma> a)) =
    paper_typed_map_normalize D (\<lambda>\<sigma> a. k \<sigma> (h \<sigma> a))"
proof (rule iffD2[OF paper_typed_map_normalized_eq_iff], intro allI impI)
  fix \<sigma> a
  assume member: "a \<in> D \<sigma>"
  have image: "h \<sigma> a \<in> E \<sigma>" by (rule maps[OF member])
  show "paper_typed_map_normalize E k \<sigma> (paper_typed_map_normalize D h \<sigma> a) = k \<sigma> (h \<sigma> a)"
    by (simp only: paper_typed_map_normalize_on_domain[where D=D and \<sigma>=\<sigma>, OF member]
      paper_typed_map_normalize_on_domain[where D=E and \<sigma>=\<sigma>, OF image])
qed

end
