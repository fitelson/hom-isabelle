theory Goodman_Exact_M1_Fn59
  imports Goodman_M1_Fn59_Purity
    "Goodman_Integration_Exact_Applicative.Goodman_Exact_Goodman_Translation"
    "Goodman_Integration_Central_Stock.Goodman_Native_QSS"
begin

section \<open>Arbitrary typed Pure/Fun interpretations on the exact carriers\<close>

definition gi_M1_exact_Pure where
  "gi_M1_exact_Pure C \<sigma> w x = pp_e_holds (C pp_pure_name (Arr \<sigma> Prop) \<acute> x) w"

definition gi_M1_exact_Fun where
  "gi_M1_exact_Fun C w x = pp_e_holds (C pp_fun_name (Arr Prop Prop) \<acute> x) w"

lemma gi_M1_native_pure_clause:
  "gi_exact_valuation w (gi_exact_goodman_denote C G g (gb_pure \<sigma> A)) =
    gi_M1_exact_Pure C \<sigma> w (gi_exact_goodman_denote C G g A)"
  unfolding gb_pure_def gi_exact_goodman_denote_def gi_M1_exact_Pure_def gi_exact_valuation_def
  by (simp add: gi_goodman_string_term_Pure
      gi_exact_named_denote_app[where \<sigma>=\<sigma> and \<tau>=Prop]
      gi_exact_named_denote_const)

context pp_e_constants
begin

lemma gi_M1_exact_fn59_liar_clause:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "pp_e_holds (pp_e_eval C \<rho> gi_M1_fn59_liar \<acute> p) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
        (gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Fun C w q \<and>
          pp_e_eqv Prop w p (X \<acute> q) \<longrightarrow> \<not> pp_e_holds (X \<acute> p) w)))"
  by (simp only: gi_M1_fn59_liar_def pp_e_eval.simps(4) Lambda_app[OF pm]
      pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds
      pp_e_eval_Neg_holds pp_e_eval_Eq_holds pp_pure_def pp_fun_def pp_Pure_def pp_Fun_def
      pp_e_eval.simps(1,2,3) numeral_2_eq_2 One_nat_def extend_env.simps
      pp_unary_ty_def gi_M1_exact_Pure_def gi_M1_exact_Fun_def)

lemma gi_M1_exact_QSS_clause:
  "pp_e_holds (pp_e_eval C \<rho> pp_QSS) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
          (gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Pure C gb_unary w Y \<and>
            gi_M1_exact_Fun C w q \<longrightarrow>
            (pp_e_eqv Prop w (X \<acute> q) (Y \<acute> q) \<longrightarrow> pp_e_eqv gb_unary w X Y)))))"
  by (simp only: pp_QSS_def pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds
      pp_e_eval_Eq_holds pp_pure_def pp_fun_def pp_Pure_def pp_Fun_def
      pp_e_eval.simps(1,2,3) numeral_2_eq_2 One_nat_def extend_env.simps
      pp_unary_ty_def gi_M1_exact_Pure_def gi_M1_exact_Fun_def)

lemma gi_M1_exact_unique_fundamental_clause:
  "pp_e_holds (pp_e_eval C \<rho> (pp_unique_fundamental Prop)) w \<longleftrightarrow>
    (\<exists>r. Elem r (pp_e_domain Prop) \<and> gi_M1_exact_Fun C w r \<and>
      (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow> gi_M1_exact_Fun C w q \<longrightarrow> pp_e_eqv Prop w q r))"
  by (simp only: pp_unique_fundamental_def pp_e_eval_Exists_holds pp_e_eval_Forall_holds
      pp_e_eval_Imp_holds pp_e_eval_Conj_holds pp_e_eval_Eq_holds pp_fun_def pp_Fun_def
      pp_e_eval.simps(1,2,3) One_nat_def extend_env.simps gi_M1_exact_Fun_def)

lemma gi_M1_exact_fn59_liar_member:
  "Elem (pp_e_eval C pp_e_closed_env gi_M1_fn59_liar) (pp_e_domain gb_unary)"
  using pp_e_eval_type[OF typed_gi_M1_fn59_liar[where \<Gamma>="[]"] pp_e_empty_env_typed]
  by (simp only: pp_e_dom_def pp_unary_ty_def)

theorem gi_M1_exact_fn59_contradiction:
  assumes D_pure: "gi_M1_exact_Pure C gb_unary w (pp_e_eval C pp_e_closed_env gi_M1_fn59_liar)"
    and qss_holds: "pp_e_holds (pp_e_eval C pp_e_closed_env pp_QSS) w"
    and unique_holds: "pp_e_holds (pp_e_eval C pp_e_closed_env (pp_unique_fundamental Prop)) w"
  shows False
proof -
  let ?D = "pp_e_eval C pp_e_closed_env gi_M1_fn59_liar"
  have Dm: "Elem ?D (pp_e_domain gb_unary)" by (rule gi_M1_exact_fn59_liar_member)
  obtain r where rm: "Elem r (pp_e_domain Prop)" and r_fun: "gi_M1_exact_Fun C w r"
    and unique: "\<And>q. Elem q (pp_e_domain Prop) \<Longrightarrow> gi_M1_exact_Fun C w q \<Longrightarrow> pp_e_eqv Prop w q r"
    using unique_holds gi_M1_exact_unique_fundamental_clause by blast
  let ?d = "?D \<acute> r"
  have dm: "Elem ?d (pp_e_domain Prop)" by (rule pp_e_app_closed[OF Dm rm])
  have diagonal: "pp_e_holds (?D \<acute> ?d) w \<longleftrightarrow>
      (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
        (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
          (gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Fun C w q \<and>
            pp_e_eqv Prop w ?d (X \<acute> q) \<longrightarrow> \<not> pp_e_holds (X \<acute> ?d) w)))"
    by (rule gi_M1_exact_fn59_liar_clause[OF dm])
  have qss: "\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
          (gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Pure C gb_unary w Y \<and>
            gi_M1_exact_Fun C w q \<longrightarrow>
            (pp_e_eqv Prop w (X \<acute> q) (Y \<acute> q) \<longrightarrow> pp_e_eqv gb_unary w X Y))))"
    using qss_holds gi_M1_exact_QSS_clause by blast
  have not_true: "pp_e_holds (?D \<acute> ?d) w \<Longrightarrow> \<not> pp_e_holds (?D \<acute> ?d) w"
  proof -
    assume true_Dd: "pp_e_holds (?D \<acute> ?d) w"
    have dd: "pp_e_eqv Prop w ?d (?D \<acute> r)" by (rule pp_e_eqv_reflexive[OF dm])
    show "\<not> pp_e_holds (?D \<acute> ?d) w"
      using diagonal true_Dd Dm rm D_pure r_fun dd by blast
  qed
  have true_if_not: "\<not> pp_e_holds (?D \<acute> ?d) w \<Longrightarrow> pp_e_holds (?D \<acute> ?d) w"
  proof -
    assume false_Dd: "\<not> pp_e_holds (?D \<acute> ?d) w"
    have universal: "\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
        (\<forall>q. Elem q (pp_e_domain Prop) \<longrightarrow>
          (gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Fun C w q \<and>
            pp_e_eqv Prop w ?d (X \<acute> q) \<longrightarrow> \<not> pp_e_holds (X \<acute> ?d) w))"
    proof (intro allI impI)
      fix X q
      assume Xm: "Elem X (pp_e_domain gb_unary)" and qm: "Elem q (pp_e_domain Prop)"
        and antecedent: "gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Fun C w q \<and>
          pp_e_eqv Prop w ?d (X \<acute> q)"
      have X_pure: "gi_M1_exact_Pure C gb_unary w X" using antecedent by blast
      have q_fun: "gi_M1_exact_Fun C w q" using antecedent by blast
      have dXq: "pp_e_eqv Prop w ?d (X \<acute> q)" using antecedent by blast
      have qr: "pp_e_eqv Prop w q r" by (rule unique[OF qm q_fun])
      have Xqm: "Elem (X \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF Xm qm])
      have Xrm: "Elem (X \<acute> r) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF Xm rm])
      have XX: "pp_e_eqv gb_unary w X X" by (rule pp_e_eqv_reflexive[OF Xm])
      have XqXr: "pp_e_eqv Prop w (X \<acute> q) (X \<acute> r)"
        by (rule pp_e_app_respects[OF XX qm rm qr])
      have dXr: "pp_e_eqv Prop w ?d (X \<acute> r)"
        by (rule pp_e_eqv_transitive[OF dm Xqm Xrm dXq XqXr])
      have DX: "pp_e_eqv gb_unary w ?D X"
        using qss Dm Xm rm D_pure X_pure r_fun dXr by blast
      have dd: "pp_e_eqv Prop w ?d ?d" by (rule pp_e_eqv_reflexive[OF dm])
      have DdXd: "pp_e_eqv Prop w (?D \<acute> ?d) (X \<acute> ?d)"
        by (rule pp_e_app_respects[OF DX dm dm dd])
      have truth_equiv: "pp_e_holds (?D \<acute> ?d) w \<longleftrightarrow> pp_e_holds (X \<acute> ?d) w"
        by (rule pp_e_prop_eqv_at[OF DdXd]; simp)
      show "\<not> pp_e_holds (X \<acute> ?d) w" using false_Dd truth_equiv by blast
    qed
    show "pp_e_holds (?D \<acute> ?d) w" using diagonal universal by blast
  qed
  show False using not_true true_if_not by blast
qed

section \<open>The independent native diagonal has exactly that denotation\<close>

lemma gi_M1_native_fn59_denotation:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote C G g (gi_M1_native_fn59_liar G) =
    pp_e_eval C pp_e_closed_env gi_M1_fn59_liar"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of gi_M1_fn59_liar \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp only: gi_M1_fn59_liar_vocabulary subset_refl)
  have translated: "gi_exact_goodman_denote C G g (gi_to_book G [] k gi_M1_fn59_liar) =
      pp_e_eval C pp_e_closed_env gi_M1_fn59_liar"
    by (rule gi_exact_goodman_closed_denotation_translation[
      OF rich typed_gi_M1_fn59_liar typed names vocabulary])
  show ?thesis using translated by (simp only: gi_M1_fn59_native_shape[OF names])
qed

lemma gi_M1_native_QSS_denotation:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote C G g (gb_QSS G) = pp_e_eval C pp_e_closed_env pp_QSS"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of pp_QSS \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_QSS_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def)
  have translated: "gi_exact_goodman_denote C G g (gi_to_book G [] k pp_QSS) = pp_e_eval C pp_e_closed_env pp_QSS"
    by (rule gi_exact_goodman_closed_denotation_translation[OF rich typed_pp_QSS typed names vocabulary])
  show ?thesis using translated by (simp only: gi_QSS_translation[OF names])
qed

lemma gi_M1_native_unique_denotation:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_goodman_denote C G g (gb_unique_fundamental G Prop) =
    pp_e_eval C pp_e_closed_env (pp_unique_fundamental Prop)"
proof -
  obtain k where names: "gi_goodman_names k" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of (pp_unique_fundamental Prop) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def)
  have translated: "gi_exact_goodman_denote C G g (gi_to_book G [] k (pp_unique_fundamental Prop)) =
      pp_e_eval C pp_e_closed_env (pp_unique_fundamental Prop)"
    by (rule gi_exact_goodman_closed_denotation_translation[
      OF rich typed_pp_unique_fundamental typed names vocabulary])
  show ?thesis using translated by (simp only: gi_unique_fundamental_translation[OF names])
qed

theorem gi_M1_exact_native_fn59_contradiction:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
    and pure: "gi_exact_valuation w (gi_exact_goodman_denote C G g
      (gb_pure gb_unary (gi_M1_native_fn59_liar G)))"
    and qss: "gi_exact_valuation w (gi_exact_goodman_denote C G g (gb_QSS G))"
    and unique: "gi_exact_valuation w (gi_exact_goodman_denote C G g (gb_unique_fundamental G Prop))"
  shows False
proof -
  have D_pure: "gi_M1_exact_Pure C gb_unary w (pp_e_eval C pp_e_closed_env gi_M1_fn59_liar)"
    using pure by (simp only: gi_M1_native_pure_clause gi_M1_native_fn59_denotation[OF rich typed])
  have qss_holds: "pp_e_holds (pp_e_eval C pp_e_closed_env pp_QSS) w"
    using qss by (simp only: gi_M1_native_QSS_denotation[OF rich typed] gi_exact_valuation_def)
  have unique_holds: "pp_e_holds (pp_e_eval C pp_e_closed_env (pp_unique_fundamental Prop)) w"
    using unique by (simp only: gi_M1_native_unique_denotation[OF rich typed] gi_exact_valuation_def)
  show False by (rule gi_M1_exact_fn59_contradiction[OF D_pure qss_holds unique_holds])
qed

theorem gi_M1_no_exact_typed_interpretation_of_fn59_stock:
  assumes rich: "sg_rich G"
    and axioms: "\<And>A. A \<in> gi_M1_fn59_native_axioms G \<union>
      {gb_QSS G, gb_unique_fundamental G Prop} \<Longrightarrow> gi_exact_goodman_global_valid C G A"
  shows False
proof -
  have pure_global: "gi_exact_goodman_global_valid C G (gb_pure gb_unary (gi_M1_native_fn59_liar G))"
  proof (rule gi_exact_goodman_extension_global_sound[OF rich gi_M1_native_fn59_liar_pure[OF rich]])
    fix A assume member: "A \<in> gi_M1_fn59_native_axioms G"
    show "gi_exact_goodman_global_valid C G A" by (rule axioms; simp add: member)
  qed
  have qss_global: "gi_exact_goodman_global_valid C G (gb_QSS G)" by (rule axioms; simp)
  have unique_global: "gi_exact_goodman_global_valid C G (gb_unique_fundamental G Prop)" by (rule axioms; simp)
  let ?g = "gi_exact_default_assignment G"
  have typed: "book_env_typed gi_exact_domain G ?g" by (rule gi_exact_default_assignment_typed)
  have pure_at_root: "gi_exact_valuation [] (gi_exact_goodman_denote C G ?g
      (gb_pure gb_unary (gi_M1_native_fn59_liar G)))"
    using pure_global typed by (simp only: gi_exact_goodman_global_valid_iff; blast)
  have qss_at_root: "gi_exact_valuation [] (gi_exact_goodman_denote C G ?g (gb_QSS G))"
    using qss_global typed by (simp only: gi_exact_goodman_global_valid_iff; blast)
  have unique_at_root: "gi_exact_valuation [] (gi_exact_goodman_denote C G ?g (gb_unique_fundamental G Prop))"
    using unique_global typed by (simp only: gi_exact_goodman_global_valid_iff; blast)
  show False by (rule gi_M1_exact_native_fn59_contradiction[
    OF rich typed pure_at_root qss_at_root unique_at_root])
qed

end

text \<open>
  The diagonal argument holds at an arbitrary world of an arbitrary
  typed interpretation on Bacon's exact carriers; local identity is never
  replaced by global equality. The final exclusion applies only to the
  displayed stock, which retains PP, Purity of Fun at t, logical purity,
  application closure, QSS, and unique fundamentality. It does not assert
  unconditional impurity of the unary-stock classifier or settle the
  problem without Purity of Fun.
\<close>

end
