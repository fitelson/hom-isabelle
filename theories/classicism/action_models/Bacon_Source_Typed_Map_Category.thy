theory Bacon_Source_Typed_Map_Category
  imports Bacon_Source_Typed_Arrows Bacon_Source_Category
begin

section \<open>The category of normalized typed maps\<close>

text \<open>
  For f:A→B and g:B→C, the composite has components
  (g∘f)σ(a)=gσ(fσ(a)) on D(A)σ; the identity has components
  1Aσ(a)=a there. Source: Bacon–Dorr §3.3, p.49.
  The displayed maps are normalized outside their source domains,
  so associativity and the unit laws are literal arrow equalities.

  This constructs the generic small category of ALL typed maps on
  the supplied object-indexed domains. No BBK or interpretation
  condition is present. In particular, this is not yet the category
  of BBK models in Theorem 3.12. Empty object sets are allowed.
\<close>

lemma paper_typed_compose_assoc:
  assumes fa: "f \<in> paper_typed_arrows Obj D" and ga: "g \<in> paper_typed_arrows Obj D"
    and ha: "h \<in> paper_typed_arrows Obj D"
    and fg: "paper_arrow_target f = paper_arrow_source g"
    and gh: "paper_arrow_target g = paper_arrow_source h"
  shows "paper_typed_compose D h (paper_typed_compose D g f) =
    paper_typed_compose D (paper_typed_compose D h g) f"
proof -
  have gfa: "paper_typed_compose D g f \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF fa ga fg])
  have hga: "paper_typed_compose D h g \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF ga ha gh])
  have gfh: "paper_arrow_target (paper_typed_compose D g f) = paper_arrow_source h"
    by (simp only: paper_typed_compose_endpoints; rule gh)
  have fhg: "paper_arrow_target f = paper_arrow_source (paper_typed_compose D h g)"
    by (simp only: paper_typed_compose_endpoints; rule fg)
  have lhs: "paper_typed_compose D h (paper_typed_compose D g f) \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF gfa ha gfh])
  have rhs: "paper_typed_compose D (paper_typed_compose D h g) f \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF fa hga fhg])
  show ?thesis
  proof (rule paper_typed_arrow_ext[OF lhs rhs])
    show "paper_arrow_source (paper_typed_compose D h (paper_typed_compose D g f)) =
        paper_arrow_source (paper_typed_compose D (paper_typed_compose D h g) f)"
      by (simp only: paper_typed_compose_endpoints)
    show "paper_arrow_target (paper_typed_compose D h (paper_typed_compose D g f)) =
        paper_arrow_target (paper_typed_compose D (paper_typed_compose D h g) f)"
      by (simp only: paper_typed_compose_endpoints)
  next
    fix \<sigma> a
    assume member: "a \<in> D (paper_arrow_source
      (paper_typed_compose D h (paper_typed_compose D g f))) \<sigma>"
    have am: "a \<in> D (paper_arrow_source f) \<sigma>"
      using member by (simp only: paper_typed_compose_endpoints)
    have agf: "a \<in> D (paper_arrow_source (paper_typed_compose D g f)) \<sigma>"
      using am by (simp only: paper_typed_compose_endpoints)
    have fm: "paper_arrow_map f \<sigma> a \<in> D (paper_arrow_source g) \<sigma>"
      using paper_typed_arrows_map[OF fa am] by (simp only: fg)
    show "paper_arrow_map (paper_typed_compose D h (paper_typed_compose D g f)) \<sigma> a =
        paper_arrow_map (paper_typed_compose D (paper_typed_compose D h g) f) \<sigma> a"
      by (simp only: paper_typed_compose_map_on[where D=D and f="paper_typed_compose D g f" and \<sigma>=\<sigma>, OF agf]
        paper_typed_compose_map_on[where D=D and f=f and \<sigma>=\<sigma>, OF am]
        paper_typed_compose_map_on[where D=D and f=g and \<sigma>=\<sigma>, OF fm])
  qed
qed

lemma paper_typed_identity_left:
  assumes fa: "f \<in> paper_typed_arrows Obj D"
  shows "paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f = f"
proof -
  have ta: "paper_arrow_target f \<in> Obj" by (rule paper_typed_arrows_target[OF fa])
  have ia: "paper_typed_identity D (paper_arrow_target f) \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_identity_arrow[OF ta])
  have meet: "paper_arrow_target f = paper_arrow_source (paper_typed_identity D (paper_arrow_target f))"
    by (simp only: paper_typed_identity_endpoints)
  have ca: "paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF fa ia meet])
  show ?thesis
  proof (rule paper_typed_arrow_ext[OF ca fa])
    show "paper_arrow_source (paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f) = paper_arrow_source f"
      by (simp only: paper_typed_compose_endpoints)
    show "paper_arrow_target (paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f) = paper_arrow_target f"
      by (simp only: paper_typed_compose_endpoints paper_typed_identity_endpoints)
  next
    fix \<sigma> a
    assume member: "a \<in> D (paper_arrow_source
      (paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f)) \<sigma>"
    have am: "a \<in> D (paper_arrow_source f) \<sigma>"
      using member by (simp only: paper_typed_compose_endpoints)
    have fm: "paper_arrow_map f \<sigma> a \<in> D (paper_arrow_target f) \<sigma>"
      by (rule paper_typed_arrows_map[OF fa am])
    show "paper_arrow_map (paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f) \<sigma> a = paper_arrow_map f \<sigma> a"
      by (simp only: paper_typed_compose_map_on[where D=D and f=f and \<sigma>=\<sigma>, OF am]
        paper_typed_identity_map_on[where D=D and A="paper_arrow_target f" and \<sigma>=\<sigma>, OF fm])
  qed
qed

lemma paper_typed_identity_right:
  assumes fa: "f \<in> paper_typed_arrows Obj D"
  shows "paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f)) = f"
proof -
  have sa: "paper_arrow_source f \<in> Obj" by (rule paper_typed_arrows_source[OF fa])
  have ia: "paper_typed_identity D (paper_arrow_source f) \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_identity_arrow[OF sa])
  have meet: "paper_arrow_target (paper_typed_identity D (paper_arrow_source f)) = paper_arrow_source f"
    by (simp only: paper_typed_identity_endpoints)
  have ca: "paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f)) \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow[OF ia fa meet])
  show ?thesis
  proof (rule paper_typed_arrow_ext[OF ca fa])
    show "paper_arrow_source (paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f))) = paper_arrow_source f"
      by (simp only: paper_typed_compose_endpoints paper_typed_identity_endpoints)
    show "paper_arrow_target (paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f))) = paper_arrow_target f"
      by (simp only: paper_typed_compose_endpoints)
  next
    fix \<sigma> a
    assume member: "a \<in> D (paper_arrow_source
      (paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f)))) \<sigma>"
    have am: "a \<in> D (paper_arrow_source f) \<sigma>"
      using member by (simp only: paper_typed_compose_endpoints paper_typed_identity_endpoints)
    have aim: "a \<in> D (paper_arrow_source (paper_typed_identity D (paper_arrow_source f))) \<sigma>"
      using am by (simp only: paper_typed_identity_endpoints)
    show "paper_arrow_map (paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f))) \<sigma> a = paper_arrow_map f \<sigma> a"
      by (simp only: paper_typed_compose_map_on[where D=D and f="paper_typed_identity D (paper_arrow_source f)" and \<sigma>=\<sigma>, OF aim]
        paper_typed_identity_map_on[where D=D and A="paper_arrow_source f" and \<sigma>=\<sigma>, OF am])
  qed
qed

theorem paper_typed_map_category:
  "paper_category Obj (paper_typed_arrows Obj D) paper_arrow_source paper_arrow_target
    (paper_typed_compose D) (paper_typed_identity D)"
proof unfold_locales
  show "\<And>f. f \<in> paper_typed_arrows Obj D \<Longrightarrow> paper_arrow_source f \<in> Obj"
    by (rule paper_typed_arrows_source)
  show "\<And>f. f \<in> paper_typed_arrows Obj D \<Longrightarrow> paper_arrow_target f \<in> Obj"
    by (rule paper_typed_arrows_target)
  show "\<And>A. A \<in> Obj \<Longrightarrow> paper_typed_identity D A \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_identity_arrow)
  show "\<And>A. A \<in> Obj \<Longrightarrow> paper_arrow_source (paper_typed_identity D A) = A"
    by (simp only: paper_typed_identity_endpoints)
  show "\<And>A. A \<in> Obj \<Longrightarrow> paper_arrow_target (paper_typed_identity D A) = A"
    by (simp only: paper_typed_identity_endpoints)
  show "\<And>f g. f \<in> paper_typed_arrows Obj D \<Longrightarrow> g \<in> paper_typed_arrows Obj D \<Longrightarrow>
      paper_arrow_target f = paper_arrow_source g \<Longrightarrow> paper_typed_compose D g f \<in> paper_typed_arrows Obj D"
    by (rule paper_typed_compose_arrow)
  show "\<And>f g. f \<in> paper_typed_arrows Obj D \<Longrightarrow> g \<in> paper_typed_arrows Obj D \<Longrightarrow>
      paper_arrow_target f = paper_arrow_source g \<Longrightarrow>
      paper_arrow_source (paper_typed_compose D g f) = paper_arrow_source f"
    by (simp only: paper_typed_compose_endpoints)
  show "\<And>f g. f \<in> paper_typed_arrows Obj D \<Longrightarrow> g \<in> paper_typed_arrows Obj D \<Longrightarrow>
      paper_arrow_target f = paper_arrow_source g \<Longrightarrow>
      paper_arrow_target (paper_typed_compose D g f) = paper_arrow_target g"
    by (simp only: paper_typed_compose_endpoints)
  show "\<And>f g h. f \<in> paper_typed_arrows Obj D \<Longrightarrow> g \<in> paper_typed_arrows Obj D \<Longrightarrow>
      h \<in> paper_typed_arrows Obj D \<Longrightarrow> paper_arrow_target f = paper_arrow_source g \<Longrightarrow>
      paper_arrow_target g = paper_arrow_source h \<Longrightarrow>
      paper_typed_compose D h (paper_typed_compose D g f) = paper_typed_compose D (paper_typed_compose D h g) f"
    by (rule paper_typed_compose_assoc)
  show "\<And>f. f \<in> paper_typed_arrows Obj D \<Longrightarrow>
      paper_typed_compose D (paper_typed_identity D (paper_arrow_target f)) f = f"
    by (rule paper_typed_identity_left)
  show "\<And>f. f \<in> paper_typed_arrows Obj D \<Longrightarrow>
      paper_typed_compose D f (paper_typed_identity D (paper_arrow_source f)) = f"
    by (rule paper_typed_identity_right)
qed

end
