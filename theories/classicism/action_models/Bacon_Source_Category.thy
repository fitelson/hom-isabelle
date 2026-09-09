theory Bacon_Source_Category
  imports Main
begin

section \<open>Set-indexed categories with guarded operations\<close>

text \<open>
  A category has objects A, arrows f:A→B, identities 1A, and
  composition g∘f when the target of f is the source of g.
  Source: Bacon–Dorr §3.3, pp.49–50. Associativity and the two
  identity laws apply only to the indicated valid arrows.

  Representation: objects and arrows are explicit sets; source, target,
  compose and identity are total HOL functions constrained only on their
  legitimate inputs. compose g f means g AFTER f. Set-indexed means
  small, not finite or countable. Empty categories are allowed.
  Section 3.3 also allows proper classes; this interface represents the
  small case required by Proposition 3.22. It does not by itself put
  the class of all models in Theorem 3.12 into one HOL carrier.
  No BBK models, interpretation, valuation or Classicism proof predicate
  appears in this interface.
\<close>

locale paper_category =
  fixes objects :: "'o set" and arrows :: "'a set"
    and source :: "'a \<Rightarrow> 'o" and target :: "'a \<Rightarrow> 'o"
    and compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and identity :: "'o \<Rightarrow> 'a"
  assumes source_object: "f \<in> arrows \<Longrightarrow> source f \<in> objects"
    and target_object: "f \<in> arrows \<Longrightarrow> target f \<in> objects"
    and identity_arrow: "A \<in> objects \<Longrightarrow> identity A \<in> arrows"
    and identity_source: "A \<in> objects \<Longrightarrow> source (identity A) = A"
    and identity_target: "A \<in> objects \<Longrightarrow> target (identity A) = A"
    and compose_arrow: "f \<in> arrows \<Longrightarrow> g \<in> arrows \<Longrightarrow> target f = source g \<Longrightarrow>
      compose g f \<in> arrows"
    and compose_source: "f \<in> arrows \<Longrightarrow> g \<in> arrows \<Longrightarrow> target f = source g \<Longrightarrow>
      source (compose g f) = source f"
    and compose_target: "f \<in> arrows \<Longrightarrow> g \<in> arrows \<Longrightarrow> target f = source g \<Longrightarrow>
      target (compose g f) = target g"
    and compose_assoc: "f \<in> arrows \<Longrightarrow> g \<in> arrows \<Longrightarrow> h \<in> arrows \<Longrightarrow>
      target f = source g \<Longrightarrow> target g = source h \<Longrightarrow>
      compose h (compose g f) = compose (compose h g) f"
    and identity_left: "f \<in> arrows \<Longrightarrow> compose (identity (target f)) f = f"
    and identity_right: "f \<in> arrows \<Longrightarrow> compose f (identity (source f)) = f"
begin

definition paper_composable :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "paper_composable f g \<longleftrightarrow> f \<in> arrows \<and> g \<in> arrows \<and> target f = source g"

lemma paper_composableI:
  assumes first: "f \<in> arrows" and second: "g \<in> arrows" and meeting: "target f = source g"
  shows "paper_composable f g"
  unfolding paper_composable_def by (rule conjI[OF first conjI[OF second meeting]])

lemma paper_composableD:
  assumes composable: "paper_composable f g"
  shows "f \<in> arrows" and "g \<in> arrows" and "target f = source g"
  using composable unfolding paper_composable_def by blast+

lemma paper_composite_arrow:
  assumes composable: "paper_composable f g"
  shows "compose g f \<in> arrows"
  by (rule compose_arrow[OF paper_composableD(1,2,3)[OF composable]])

lemma paper_composable_right_identity:
  assumes arrow: "f \<in> arrows"
  shows "paper_composable (identity (source f)) f"
proof -
  have object: "source f \<in> objects" by (rule source_object[OF arrow])
  show ?thesis by (rule paper_composableI[
    OF identity_arrow[OF object] arrow identity_target[OF object]])
qed

lemma paper_composable_left_identity:
  assumes arrow: "f \<in> arrows"
  shows "paper_composable f (identity (target f))"
proof -
  have object: "target f \<in> objects" by (rule target_object[OF arrow])
  have meeting: "target f = source (identity (target f))"
    by (rule identity_source[OF object, symmetric])
  show ?thesis by (rule paper_composableI[OF arrow identity_arrow[OF object] meeting])
qed

lemma paper_composable_composites:
  assumes first: "paper_composable f g" and second: "paper_composable g h"
  shows "paper_composable (compose g f) h" and "paper_composable f (compose h g)"
proof -
  have fa: "f \<in> arrows" and ga: "g \<in> arrows" and fg: "target f = source g"
    by (rule paper_composableD[OF first])+
  have ha: "h \<in> arrows" and gh: "target g = source h"
    by (rule paper_composableD[OF second])+
  have first_target: "target (compose g f) = source h"
    by (simp only: compose_target[OF fa ga fg] gh)
  show "paper_composable (compose g f) h"
    by (rule paper_composableI[OF compose_arrow[OF fa ga fg] ha first_target])
  have second_source: "target f = source (compose h g)"
    by (simp only: compose_source[OF ga ha gh]; rule fg)
  show "paper_composable f (compose h g)"
    by (rule paper_composableI[OF fa compose_arrow[OF ga ha gh] second_source])
qed

lemma paper_identity_inj_on:
  "inj_on identity objects"
proof (rule inj_onI)
  fix A B
  assume am: "A \<in> objects" and bm: "B \<in> objects" and equal: "identity A = identity B"
  have sources: "source (identity A) = source (identity B)" by (rule arg_cong[OF equal])
  show "A = B" using sources by (simp only: identity_source[OF am] identity_source[OF bm])
qed

end

lemma paper_empty_category:
  "paper_category {} {} source target compose identity"
  by unfold_locales simp_all

end
