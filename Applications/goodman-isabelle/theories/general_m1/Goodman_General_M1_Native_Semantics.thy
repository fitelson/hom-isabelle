theory Goodman_General_M1_Native_Semantics
  imports
    "Goodman_Integration_Exact_M.Goodman_M1_Fn59_Purity"
    "Goodman_Integration_Central_Stock.Goodman_Native_QSS"
    "Bacon_Book_Environment_Development.Bacon_Book_Minimal_Leibniz_Truth"
    "Bacon_Book_Environment_Development.Bacon_Book_Minimal_Existential_Truth"
    "Bacon_Book_Environment_Development.Bacon_Book_Leibniz_Application"
begin

section \<open>The native footnote-59 formulas in an arbitrary full minimal model\<close>

text \<open>
  The carrier below is an arbitrary HOL type. We use the book's actual
  named-term interpretation and its derived Leibniz relation, not Bacon's
  tree carriers, raw operator functions, or an assumed semantic diagonal.
  All quantifiers range over the model's domains. Richness and a typed
  assignment are explicit. No Functionality or actual identity is imposed.

  This is a pointwise theorem for a full minimal-basis model. Applying it
  at every world of a modal model is legitimate only when that world's
  interpretation satisfies these fields. Soundness of C+[T], particularly
  its theorem rules above added axioms, is a separate interface obligation.
\<close>

locale gi_M1_book_model =
  book_full_minimal_model domain app gb_signature G denote V kappa
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and G :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> gb_term \<Rightarrow> 'v"
    and V :: "'v \<Rightarrow> bool"
    and kappa :: "book_minimal_logical \<Rightarrow> 'v" +
  fixes g :: "nat \<Rightarrow> 'v"
  assumes rich: "sg_rich G"
    and gt: "book_env_typed domain G g"
begin

definition gi_book_Pure where
  "gi_book_Pure \<sigma> a = V (app \<sigma> Prop (denote g (gb_Pure \<sigma>)) a)"

definition gi_book_Fun where
  "gi_book_Fun a = V (app Prop Prop (denote g (gb_Fun Prop)) a)"

abbreviation gi_book_eq where
  "gi_book_eq \<sigma> a b \<equiv> book_leibniz_equiv domain app V \<sigma> a b"

lemma gi_book_Pure_constant:
  "book_env_typed domain G h \<Longrightarrow>
    denote h (gb_Pure \<sigma>) = denote g (gb_Pure \<sigma>)"
  by (rule book_denote_locality[OF UNIV_I gb_Pure_language _ gt]; simp)

lemma gi_book_Fun_constant:
  "book_env_typed domain G h \<Longrightarrow>
    denote h (gb_Fun Prop) = denote g (gb_Fun Prop)"
  by (rule book_denote_locality[OF UNIV_I gb_Fun_language _ gt]; simp)

lemma gi_book_pure_truth:
  assumes ht: "book_env_typed domain G h"
    and al: "book_in_language book_minimal_logical_type UNIV gb_signature G A \<sigma>"
  shows "V (denote h (gb_pure \<sigma> A)) = gi_book_Pure \<sigma> (denote h A)"
  unfolding gb_pure_def gi_book_Pure_def
  by (simp only: denote_app[OF UNIV_I UNIV_I UNIV_I gb_Pure_language al ht]
    gi_book_Pure_constant[OF ht])

lemma gi_book_fun_truth:
  assumes ht: "book_env_typed domain G h"
    and al: "book_in_language book_minimal_logical_type UNIV gb_signature G A Prop"
  shows "V (denote h (gb_fun Prop A)) = gi_book_Fun (denote h A)"
  unfolding gb_fun_def gi_book_Fun_def
  by (simp only: denote_app[OF UNIV_I UNIV_I UNIV_I gb_Fun_language al ht]
    gi_book_Fun_constant[OF ht])

lemma gi_book_unary_application:
  assumes ht: "book_env_typed domain G h"
    and fl: "book_in_language book_minimal_logical_type UNIV gb_signature G F gb_unary"
    and al: "book_in_language book_minimal_logical_type UNIV gb_signature G A Prop"
  shows "denote h (NApp F A) = app Prop Prop (denote h F) (denote h A)"
  by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fl al ht])

lemmas gi_book_formula_language =
  book_all_language book_exists_language[OF rich]
  book_imp_language book_and_language[OF rich] book_not_language[OF rich]
  book_leibniz_language[OF rich] gb_pure_language gb_fun_language
  book_language_App[where \<sigma>=Prop and \<tau>=Prop]
  gb_x_language[OF rich] gb_y_language[OF rich] gb_z_language[OF rich]

lemmas gi_book_formula_truth =
  book_all_truth book_exists_truth[OF rich] book_imp_truth
  book_and_truth[OF rich] book_not_truth[OF rich]
  book_leibniz_truth[OF rich] gi_book_pure_truth gi_book_fun_truth
  gi_book_unary_application denote_var[OF UNIV_I]

lemma gi_book_fn59_liar_clause:
  assumes pm: "p \<in> domain Prop"
  shows "V (app Prop Prop (denote g (gi_M1_native_fn59_liar G)) p) =
    (\<forall>X \<in> domain gb_unary. \<forall>q \<in> domain Prop.
      gi_book_Pure gb_unary X \<and> gi_book_Fun q \<and>
        gi_book_eq Prop p (app Prop Prop X q) \<longrightarrow>
      \<not> V (app Prop Prop X p))"
proof -
  let ?x = "gb_x G Prop"
  let ?y = "gb_y G Prop gb_unary"
  let ?z = "gb_z G Prop gb_unary Prop"
  let ?body = "book_all G ?y (book_all G ?z
    (book_imp (book_and G (gb_pure gb_unary (NVar ?y))
      (book_and G (gb_fun Prop (NVar ?z))
        (book_leibniz G Prop (NVar ?x) (NApp (NVar ?y) (NVar ?z)))))
      (book_not G (NApp (NVar ?y) (NVar ?x)))))"
  have bl: "book_theory_formula gb_signature G ?body"
    by (intro gi_book_formula_language)
  have pn: "p \<in> domain (G ?x)"
    by (simp only: gb_names_type[OF rich]; rule pm)
  have beta: "app Prop Prop (denote g (gi_M1_native_fn59_liar G)) p =
    denote (g(?x := p)) ?body"
    using book_full_lambda_application[OF bl gt pn]
    by (simp only: gi_M1_native_fn59_liar_def gb_names_type[OF rich])
  have nd: "?x \<noteq> ?y" "?x \<noteq> ?z" "?y \<noteq> ?z"
    using gb_names_distinct[OF rich, where \<sigma>=Prop and \<tau>=gb_unary and \<upsilon>=Prop]
    by auto
  show ?thesis
    by (simp add: beta gi_book_formula_truth gi_book_formula_language
      book_env_update gt pm gb_names_type[OF rich] nd)
qed

lemma gi_book_QSS_clause:
  "V (denote g (gb_QSS G)) =
    (\<forall>X \<in> domain gb_unary. \<forall>Y \<in> domain gb_unary.
      \<forall>r \<in> domain Prop.
        gi_book_Pure gb_unary X \<and> gi_book_Pure gb_unary Y \<and> gi_book_Fun r
        \<longrightarrow> gi_book_eq Prop (app Prop Prop X r) (app Prop Prop Y r)
        \<longrightarrow> gi_book_eq gb_unary X Y)"
proof -
  have nd: "gb_x G gb_unary \<noteq> gb_y G gb_unary gb_unary"
    "gb_x G gb_unary \<noteq> gb_z G gb_unary gb_unary Prop"
    "gb_y G gb_unary gb_unary \<noteq> gb_z G gb_unary gb_unary Prop"
    using gb_names_distinct[OF rich, where \<sigma>=gb_unary and \<tau>=gb_unary and \<upsilon>=Prop]
    by auto
  show ?thesis
    by (simp add: gb_QSS_def gb_QSS_instance_def gi_book_formula_truth
      gi_book_formula_language book_env_update gt gb_names_type[OF rich] nd)
qed

lemma gi_book_unique_fundamental_clause:
  "V (denote g (gb_unique_fundamental G Prop)) =
    (\<exists>r \<in> domain Prop. gi_book_Fun r \<and>
      (\<forall>q \<in> domain Prop. gi_book_Fun q \<longrightarrow> gi_book_eq Prop q r))"
proof -
  have nd: "gb_x G Prop \<noteq> gb_y G Prop Prop"
    using gb_names_distinct[OF rich, where \<sigma>=Prop and \<tau>=Prop and \<upsilon>=Prop]
    by auto
  show ?thesis
    by (simp add: gb_unique_fundamental_def gi_book_formula_truth
      gi_book_formula_language book_env_update gt gb_names_type[OF rich] nd)
qed

section \<open>The diagonal contradiction, with its semantic fields discharged\<close>

lemma gi_book_fn59_liar_member:
  "denote g (gi_M1_native_fn59_liar G) \<in> domain gb_unary"
  by (rule denote_type[OF UNIV_I gi_M1_native_fn59_liar_language[OF rich] gt])

theorem gi_book_fn59_diagonal_contradiction:
  assumes pure: "gi_book_Pure gb_unary (denote g (gi_M1_native_fn59_liar G))"
    and qss: "V (denote g (gb_QSS G))"
    and unique: "V (denote g (gb_unique_fundamental G Prop))"
  shows False
proof -
  let ?D = "denote g (gi_M1_native_fn59_liar G)"
  have Dm: "?D \<in> domain gb_unary" by (rule gi_book_fn59_liar_member)
  obtain r where rm: "r \<in> domain Prop" and rf: "gi_book_Fun r"
    and uq: "\<And>q. q \<in> domain Prop \<Longrightarrow> gi_book_Fun q \<Longrightarrow>
      gi_book_eq Prop q r"
    using unique gi_book_unique_fundamental_clause by blast
  let ?d = "app Prop Prop ?D r"
  have dm: "?d \<in> domain Prop" by (rule app_type[OF Dm rm])
  have diag: "V (app Prop Prop ?D ?d) =
      (\<forall>X \<in> domain gb_unary. \<forall>q \<in> domain Prop.
        gi_book_Pure gb_unary X \<and> gi_book_Fun q \<and>
          gi_book_eq Prop ?d (app Prop Prop X q) \<longrightarrow>
        \<not> V (app Prop Prop X ?d))"
    by (rule gi_book_fn59_liar_clause[OF dm])
  have qss_rule: "\<And>X Y q. X \<in> domain gb_unary \<Longrightarrow>
      Y \<in> domain gb_unary \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
      gi_book_Pure gb_unary X \<Longrightarrow> gi_book_Pure gb_unary Y \<Longrightarrow>
      gi_book_Fun q \<Longrightarrow>
      gi_book_eq Prop (app Prop Prop X q) (app Prop Prop Y q) \<Longrightarrow>
      gi_book_eq gb_unary X Y"
    using qss gi_book_QSS_clause by blast
  have dd: "gi_book_eq Prop ?d ?d"
    by (rule book_leibniz_refl[where D=domain and \<sigma>=Prop, OF dm])
  have not_true: "\<not> V (app Prop Prop ?D ?d)"
    using diag Dm rm pure rf dd by blast
  have rhs: "\<forall>X \<in> domain gb_unary. \<forall>q \<in> domain Prop.
      gi_book_Pure gb_unary X \<and> gi_book_Fun q \<and>
        gi_book_eq Prop ?d (app Prop Prop X q) \<longrightarrow>
      \<not> V (app Prop Prop X ?d)"
  proof (intro ballI impI)
    fix X q
    assume Xm: "X \<in> domain gb_unary" and qm: "q \<in> domain Prop"
      and premise: "gi_book_Pure gb_unary X \<and> gi_book_Fun q \<and>
        gi_book_eq Prop ?d (app Prop Prop X q)"
    have qr: "gi_book_eq Prop q r" using uq[OF qm] premise by blast
    have Xq_Xr: "gi_book_eq Prop (app Prop Prop X q) (app Prop Prop X r)"
      by (rule book_leibniz_argument_cong[OF rich gt qr Xm])
    have d_Xr: "gi_book_eq Prop ?d (app Prop Prop X r)"
      by (rule book_leibniz_trans[OF conjunct2[OF conjunct2[OF premise]] Xq_Xr])
    have DX: "gi_book_eq gb_unary ?D X"
      by (rule qss_rule[OF Dm Xm rm pure conjunct1[OF premise] rf d_Xr])
    have Dd_Xd: "gi_book_eq Prop (app Prop Prop ?D ?d) (app Prop Prop X ?d)"
      by (rule book_leibniz_head_cong[OF rich gt DX dm])
    have same_truth: "V (app Prop Prop ?D ?d) = V (app Prop Prop X ?d)"
      by (rule book_minimal_leibniz_valuation[OF Dd_Xd])
    show "\<not> V (app Prop Prop X ?d)" using not_true same_truth by simp
  qed
  show False using diag rhs not_true by blast
qed

theorem gi_book_native_fn59_contradiction:
  assumes pure: "V (denote g (gb_pure gb_unary (gi_M1_native_fn59_liar G)))"
    and qss: "V (denote g (gb_QSS G))"
    and unique: "V (denote g (gb_unique_fundamental G Prop))"
  shows False
proof -
  have pure_value: "gi_book_Pure gb_unary (denote g (gi_M1_native_fn59_liar G))"
    using pure gi_book_pure_truth[OF gt gi_M1_native_fn59_liar_language[OF rich]]
    by simp
  show False by (rule gi_book_fn59_diagonal_contradiction[OF pure_value qss unique])
qed

text \<open>
  The next corollary makes the proof-theoretic boundary explicit. It
  assumes truth preservation for the native C+[T] derivations over the
  displayed purity stock. This is not supplied by the minimal H model
  fields. Those fields have already discharged every compositional,
  typing, identity-congruence and truth condition in the diagonal above.
  In particular, we do not assume the diagonal's semantic equation.
\<close>

corollary gi_book_fn59_from_native_extension_soundness:
  assumes sound: "\<And>A. goodman_book_proves gb_signature G
      (gi_M1_fn59_native_axioms G) A \<Longrightarrow> V (denote g A)"
    and qss: "V (denote g (gb_QSS G))"
    and unique: "V (denote g (gb_unique_fundamental G Prop))"
  shows False
  by (rule gi_book_native_fn59_contradiction[
    OF sound[OF gi_M1_native_fn59_liar_pure[OF rich]] qss unique])

end

end
