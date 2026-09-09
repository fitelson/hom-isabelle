theory Bacon_Book_Modalized_Set
  imports Bacon_Book_Preorder_Category Bacon_Source_Action
begin

section \<open>Independent modalized sets on a preorder of worlds\<close>

locale book_modalized_set = book_preorder worlds le
  for worlds :: "'w set" and le :: "'w \<Rightarrow> 'w \<Rightarrow> bool" +
  fixes domain :: "'w \<Rightarrow> 'a set"
    and counterpart :: "'w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes counterpart_type: "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
      a \<in> domain w \<Longrightarrow> counterpart w v a \<in> domain v"
    and counterpart_identity: "w \<in> worlds \<Longrightarrow> a \<in> domain w \<Longrightarrow> counterpart w w a = a"
    and counterpart_compose: "w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> u \<in> worlds \<Longrightarrow>
      le w v \<Longrightarrow> le v u \<Longrightarrow> a \<in> domain w \<Longrightarrow>
      counterpart w u a = counterpart v u (counterpart w v a)"
begin

theorem book_modalized_set_action:
  "paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
    domain (\<lambda>f. counterpart (fst f) (snd f))"
proof unfold_locales
  fix f a
  assume arrow: "f \<in> book_preorder_arrows worlds le" and member: "a \<in> domain (fst f)"
  have source_world: "fst f \<in> worlds" and target_world: "snd f \<in> worlds" and related: "le (fst f) (snd f)"
    using arrow by (simp_all add: book_preorder_arrow_member)
  show "counterpart (fst f) (snd f) a \<in> domain (snd f)"
    by (rule counterpart_type[OF source_world target_world related member])
next
  fix w a
  assume world: "w \<in> worlds" and member: "a \<in> domain w"
  show "counterpart (fst (book_preorder_identity w)) (snd (book_preorder_identity w)) a = a"
    by (simp only: book_preorder_identity_def fst_conv snd_conv; rule counterpart_identity[OF world member])
next
  fix f g a
  assume first: "f \<in> book_preorder_arrows worlds le" and second: "g \<in> book_preorder_arrows worlds le"
    and meeting: "snd f = fst g" and member: "a \<in> domain (fst f)"
  have sw: "fst f \<in> worlds" and mw: "snd f \<in> worlds" and first_relation: "le (fst f) (snd f)"
    using first by (simp_all add: book_preorder_arrow_member)
  have tw: "snd g \<in> worlds" and second_relation: "le (snd f) (snd g)"
    using second by (simp_all add: book_preorder_arrow_member meeting)
  have chain: "counterpart (fst f) (snd g) a =
      counterpart (snd f) (snd g) (counterpart (fst f) (snd f) a)"
    by (rule counterpart_compose[OF sw mw tw first_relation second_relation member])
  show "counterpart (fst (book_preorder_compose g f)) (snd (book_preorder_compose g f)) a =
      counterpart (fst g) (snd g) (counterpart (fst f) (snd f) a)"
    using chain by (simp only: book_preorder_compose_def fst_conv snd_conv meeting)
qed

end

context book_preorder
begin

theorem book_modalized_set_from_action:
  assumes action: "paper_action worlds (book_preorder_arrows worlds le) fst snd
    book_preorder_compose book_preorder_identity D (\<lambda>f. i (fst f) (snd f))"
  shows "book_modalized_set worlds le D i"
proof -
  interpret Action: paper_action worlds "book_preorder_arrows worlds le" fst snd
    book_preorder_compose book_preorder_identity D "\<lambda>f. i (fst f) (snd f)"
    by (rule action)
  show ?thesis
  proof unfold_locales
    fix w v a
    assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and related: "le w v" and member: "a \<in> D w"
    have arrow: "(w,v) \<in> book_preorder_arrows worlds le"
      by (simp only: book_preorder_arrow_pair; rule conjI[OF ww conjI[OF vw related]])
    have source_member: "a \<in> D (fst (w,v))" by (simp only: fst_conv; rule member)
    show "i w v a \<in> D v" using Action.transport_type[OF arrow source_member] by simp
  next
    fix w a
    assume ww: "w \<in> worlds" and member: "a \<in> D w"
    show "i w w a = a" using Action.transport_identity[OF ww member]
      by (simp only: book_preorder_identity_def fst_conv snd_conv)
  next
    fix w v u a
    assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds"
      and first_relation: "le w v" and second_relation: "le v u" and member: "a \<in> D w"
    have first: "(w,v) \<in> book_preorder_arrows worlds le"
      by (simp only: book_preorder_arrow_pair; rule conjI[OF ww conjI[OF vw first_relation]])
    have second: "(v,u) \<in> book_preorder_arrows worlds le"
      by (simp only: book_preorder_arrow_pair; rule conjI[OF vw conjI[OF uw second_relation]])
    have meeting: "snd (w,v) = fst (v,u)" by simp
    have source_member: "a \<in> D (fst (w,v))" by (simp only: fst_conv; rule member)
    show "i w u a = i v u (i w v a)"
      using Action.transport_compose[OF first second meeting source_member]
      by (simp only: book_preorder_compose_def fst_conv snd_conv)
  qed
qed

theorem book_modalized_set_iff_action:
  "book_modalized_set worlds le D i \<longleftrightarrow>
    paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
      D (\<lambda>f. i (fst f) (snd f))"
proof
  assume modalized: "book_modalized_set worlds le D i"
  show "paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
      D (\<lambda>f. i (fst f) (snd f))"
    by (rule book_modalized_set.book_modalized_set_action[OF modalized])
next
  assume action: "paper_action worlds (book_preorder_arrows worlds le) fst snd book_preorder_compose book_preorder_identity
      D (\<lambda>f. i (fst f) (snd f))"
  show "book_modalized_set worlds le D i" by (rule book_modalized_set_from_action[OF action])
qed

end

text \<open>
  Definition 17.3, p.360, gives sets D_w and counterparts i_wv
  satisfying typing, identity and composition on w≤v≤u.
  These conditions were declared independently and are now proved
  equivalent to the action conditions for the actual thin category.
  The root plays no role in these conditions; a pointed preorder
  inherits the result from its underlying preorder.

  Fibers may be empty and overlap. No antisymmetry, nonempty fiber,
  surjectivity, injectivity, λ interpretation or full-model premise is
  included. Total HOL functions outside valid worlds or fiber members
  are unconstrained by the interface.
\<close>

end
