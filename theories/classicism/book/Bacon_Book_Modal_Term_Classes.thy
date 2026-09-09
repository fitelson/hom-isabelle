theory Bacon_Book_Modal_Term_Classes
  imports Bacon_Book_Identity_World_Algebra
begin

section \<open>Definition 18.9: classes of closed terms under identity in w\<close>

definition book_C_identity_class where
  "book_C_identity_class \<Sigma> G w \<sigma> A = {B \<in> book_closed_terms \<Sigma> G \<sigma>. book_leibniz G \<sigma> A B \<in> w}"

definition book_C_identity_domain where
  "book_C_identity_domain \<Sigma> G w \<sigma> = book_C_identity_class \<Sigma> G w \<sigma> ` book_closed_terms \<Sigma> G \<sigma>"

lemma book_C_identity_class_member:
  "B \<in> book_C_identity_class \<Sigma> G w \<sigma> A \<longleftrightarrow>
    B \<in> book_closed_terms \<Sigma> G \<sigma> \<and> book_leibniz G \<sigma> A B \<in> w"
  by (simp only: book_C_identity_class_def mem_Collect_eq)

context book_C_identity_world
begin

lemma identity_class_self:
  assumes member: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "A \<in> book_C_identity_class \<Sigma> G w \<sigma> A"
  unfolding book_C_identity_class_def by (rule CollectI, rule conjI[OF member identity_refl[OF member]])

lemma identity_class_inclusion:
  assumes am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and identity: "book_leibniz G \<sigma> A B \<in> w"
  shows "book_C_identity_class \<Sigma> G w \<sigma> A \<subseteq> book_C_identity_class \<Sigma> G w \<sigma> B"
proof
  fix C
  assume member: "C \<in> book_C_identity_class \<Sigma> G w \<sigma> A"
  have data: "C \<in> book_closed_terms \<Sigma> G \<sigma> \<and> book_leibniz G \<sigma> A C \<in> w"
    using member unfolding book_C_identity_class_def by (rule CollectD)
  have cm: "C \<in> book_closed_terms \<Sigma> G \<sigma>" by (rule conjunct1[OF data])
  have ac: "book_leibniz G \<sigma> A C \<in> w" by (rule conjunct2[OF data])
  have ba: "book_leibniz G \<sigma> B A \<in> w" by (rule identity_sym[OF am bm identity])
  have bc: "book_leibniz G \<sigma> B C \<in> w" by (rule identity_trans[OF bm am cm ba ac])
  show "C \<in> book_C_identity_class \<Sigma> G w \<sigma> B"
    unfolding book_C_identity_class_def by (rule CollectI, rule conjI[OF cm bc])
qed

theorem identity_class_eq_iff:
  assumes am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
  shows "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> B \<longleftrightarrow>
    book_leibniz G \<sigma> A B \<in> w"
proof
  assume equal: "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> B"
  have self: "B \<in> book_C_identity_class \<Sigma> G w \<sigma> B" by (rule identity_class_self[OF bm])
  have in_A: "B \<in> book_C_identity_class \<Sigma> G w \<sigma> A"
    by (rule subst[where P="\<lambda>X. B \<in> X", OF equal[symmetric] self])
  have data: "B \<in> book_closed_terms \<Sigma> G \<sigma> \<and> book_leibniz G \<sigma> A B \<in> w"
    using in_A unfolding book_C_identity_class_def by (rule CollectD)
  show "book_leibniz G \<sigma> A B \<in> w" by (rule conjunct2[OF data])
next
  assume identity: "book_leibniz G \<sigma> A B \<in> w"
  show "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> B"
    by (rule subset_antisym[OF identity_class_inclusion[OF am bm identity]
      identity_class_inclusion[OF bm am identity_sym[OF am bm identity]]])
qed

theorem identity_class_application:
  assumes fm: "F \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)" and hm: "H \<in> book_closed_terms \<Sigma> G (Arr \<sigma> \<tau>)"
    and am: "A \<in> book_closed_terms \<Sigma> G \<sigma>" and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and heads: "book_C_identity_class \<Sigma> G w (Arr \<sigma> \<tau>) F = book_C_identity_class \<Sigma> G w (Arr \<sigma> \<tau>) H"
    and arguments: "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> B"
  shows "book_C_identity_class \<Sigma> G w \<tau> (NApp F A) = book_C_identity_class \<Sigma> G w \<tau> (NApp H B)"
proof -
  have fh: "book_leibniz G (Arr \<sigma> \<tau>) F H \<in> w" using heads by (simp only: identity_class_eq_iff[OF fm hm])
  have ab: "book_leibniz G \<sigma> A B \<in> w" using arguments by (simp only: identity_class_eq_iff[OF am bm])
  have results: "book_leibniz G \<tau> (NApp F A) (NApp H B) \<in> w" by (rule identity_application[OF fm hm am bm fh ab])
  show ?thesis by (simp only: identity_class_eq_iff[OF book_closed_terms_App[OF fm am] book_closed_terms_App[OF hm bm]]; rule results)
qed

end

text \<open>
  [A]w consists of closed terms B of the same type and language for
  which A=σB belongs to w. For typed closed representatives, equality
  of these sets is equivalent to identity in w, not βη-convertibility.
  Application respects both representative choices. Nonemptiness of
  every typed domain and the actual counterpart/application maps are
  later obligations; none is stipulated by these class definitions.
\<close>

end
