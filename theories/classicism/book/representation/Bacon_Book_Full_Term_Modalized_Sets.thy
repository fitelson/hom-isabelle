theory Bacon_Book_Full_Term_Modalized_Sets
  imports Bacon_Book_Classicism_Development.Bacon_Book_Full_Term_Quasi_Functionality
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Proposition_Representation
    Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Product
    Bacon_Classicism_Action_Development.Bacon_Book_Modalized_Map
begin

context book_full_C_canonical_frame
begin

lemma full_rooted_base_world:
  "w \<in> worlds \<Longrightarrow> w \<in> book_C_canonical_worlds \<Sigma> B G"
  by (rule book_full_C_canonical_world_is_base[OF rich book_full_C_rooted_world_data(1)]; assumption)

theorem full_frame_pointed_preorder:
  "book_pointed_preorder worlds le actual"
proof unfold_locales
  show "\<And>w. w \<in> worlds \<Longrightarrow> le w w" by (rule book_full_C_rooted_refl)
  show "\<And>w v u. w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> u \<in> worlds \<Longrightarrow>
    le w v \<Longrightarrow> le v u \<Longrightarrow> le w u"
    by (rule book_full_C_rooted_trans; assumption)
  show "actual \<in> worlds" by (rule book_full_C_root_is_world)
  show "\<And>w. w \<in> worlds \<Longrightarrow> le actual w" by (rule book_full_C_rooted_world_data(2))
qed

theorem full_term_modalized_set:
  "book_modalized_set worlds le
    (\<lambda>w. book_C_identity_domain (fst w) G (snd w) \<sigma>)
    (\<lambda>w v X. book_C_term_counterpart G w v \<sigma> X)"
proof unfold_locales
  show "\<And>w. w \<in> worlds \<Longrightarrow> le w w" by (rule book_full_C_rooted_refl)
  show "\<And>w v u. w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> u \<in> worlds \<Longrightarrow>
    le w v \<Longrightarrow> le v u \<Longrightarrow> le w u"
    by (rule book_full_C_rooted_trans; assumption)
  show "\<And>w v X. w \<in> worlds \<Longrightarrow> v \<in> worlds \<Longrightarrow> le w v \<Longrightarrow>
    X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma> \<Longrightarrow>
    book_C_term_counterpart G w v \<sigma> X \<in> book_C_identity_domain (fst v) G (snd v) \<sigma>"
    by (rule book_C_term_counterpart_typed[OF rich full_rooted_base_world full_rooted_base_world]; assumption)
  show "\<And>w X. w \<in> worlds \<Longrightarrow> X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma> \<Longrightarrow>
    book_C_term_counterpart G w w \<sigma> X = X"
    by (rule book_C_term_counterpart_identity[OF rich full_rooted_base_world]; assumption)
  fix w v u X
  assume ww: "w \<in> worlds" and vw: "v \<in> worlds" and uw: "u \<in> worlds"
    and wv: "le w v" and vu: "le v u" and xd: "X \<in> book_C_identity_domain (fst w) G (snd w) \<sigma>"
  show "book_C_term_counterpart G w u \<sigma> X = book_C_term_counterpart G v u \<sigma> (book_C_term_counterpart G w v \<sigma> X)"
    by (rule book_C_term_counterpart_composition[OF rich full_rooted_base_world[OF ww]
      full_rooted_base_world[OF vw] full_rooted_base_world[OF uw] wv vu xd, symmetric])
qed

end

text \<open>
  The actual full-C frame satisfies Definition 17.1's pointed-preorder
  interface, and every actual term domain with its proved counterparts
  satisfies Definition 17.3's modalized-set interface. No additional
  frame, transport, or model condition is assumed by these adapters.
  They connect the source-faithful Chapter 17 and Chapter 18 developments.
\<close>

end
