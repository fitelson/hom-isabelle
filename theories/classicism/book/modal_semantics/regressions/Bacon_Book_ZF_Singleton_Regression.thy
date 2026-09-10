theory Bacon_Book_ZF_Singleton_Regression
  imports
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Generic_Interpretation_Existence
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Model_Truth
    Bacon_Book_ZF_Modal_Interpretation.Bacon_Book_ZF_Nontrivial_Interpretation
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Theory_Consistency
begin

text \<open>Regression for the literal structural clauses of Definition 18.1. The inhabited all-true model is not a model of the new nontrivial refinement. No existing definition is changed.\<close>

definition probe_W :: ZF where "probe_W = Singleton Empty"

fun probe_value :: "otype \<Rightarrow> ZF" where
  "probe_value Ind = Empty"
| "probe_value Prop = probe_W"
| "probe_value (Arr \<sigma> \<tau>) =
    Lambda (Singleton (Opair Empty (probe_value \<sigma>))) (\<lambda>_. probe_value \<tau>)"

definition probe_D :: book_ZF_domains where
  "probe_D \<sigma> w = Singleton (probe_value \<sigma>)"
definition probe_i :: book_ZF_counterparts where
  "probe_i \<sigma> w v a = a"
definition probe_signature :: "nat ssignature" where
  "probe_signature \<sigma> = {}"
definition probe_I :: "nat \<Rightarrow> otype \<Rightarrow> ZF" where
  "probe_I c \<sigma> = probe_value \<sigma>"

lemma probe_world [simp]: "w \<in> explode probe_W \<longleftrightarrow> w = Empty"
  by (simp add: probe_W_def explode_Elem Singleton)
lemma probe_world_elem [simp]: "Elem w probe_W \<longleftrightarrow> w = Empty"
  by (simp add: probe_W_def Singleton)
lemma probe_domain [simp]: "a \<in> explode (probe_D \<sigma> w) \<longleftrightarrow> a = probe_value \<sigma>"
  by (simp add: probe_D_def explode_Elem Singleton)
lemma probe_domain_elem [simp]: "Elem a (probe_D \<sigma> w) \<longleftrightarrow> a = probe_value \<sigma>"
  by (simp add: probe_D_def Singleton)

lemma probe_future [simp]: "book_ZF_future probe_W (=) Empty = probe_W"
  by (subst Ext; auto simp: book_ZF_future_def Sep)

lemma probe_pairs [simp]:
  "book_ZF_pairs probe_W (=) (probe_D \<sigma>) Empty = Singleton (Opair Empty (probe_value \<sigma>))"
  by (subst Ext; auto simp: book_ZF_pairs_def paper_ZF_sigma_membership Singleton)

lemma probe_app [simp]:
  "app (probe_value (Arr \<sigma> \<tau>)) (Opair Empty (probe_value \<sigma>)) = probe_value \<tau>"
  by (simp add: probe_value.simps Lambda_app Singleton)

lemma probe_collect_true:
  assumes "P Empty"
  shows "book_ZF_collect probe_W (=) Empty P = probe_W"
  using assms by (subst Ext; auto simp: book_ZF_collect_def Sep)

lemma probe_prop_restrict [simp]: "Sep probe_W ((=) Empty) = probe_W"
  by (subst Ext; auto simp: Sep)

lemma probe_function_graph:
  "probe_value (Arr \<sigma> \<tau>) =
    Lambda (book_ZF_pairs probe_W (=) (probe_D \<sigma>) Empty)
      (app (probe_value (Arr \<sigma> \<tau>)))"
  by (simp add: probe_value.simps Lambda_ext Singleton Lambda_app)

lemma probe_function_restrict:
  "book_ZF_restrict probe_W (=) (probe_D \<sigma>) Empty (probe_value (Arr \<sigma> \<tau>)) =
    probe_value (Arr \<sigma> \<tau>)"
  by (simp add: book_ZF_restrict_def probe_value.simps Lambda_ext Singleton Lambda_app)

lemma probe_modalized:
  "book_modalized_set (explode probe_W) (=) (\<lambda>w. explode (probe_D \<sigma> w)) (probe_i \<sigma>)"
  by unfold_locales (auto simp: probe_i_def)

lemma probe_structure:
  "book_ZF_modal_structure probe_W (=) Empty probe_D probe_i"
  by unfold_locales
    (auto simp: probe_i_def probe_function_graph probe_function_restrict
      book_ZF_restrict_def Lambda_ext Singleton Lambda_app
      intro: probe_modalized)

lemma probe_k:
  "book_ZF_k probe_W (=) probe_D probe_i Empty \<sigma> \<tau> =
    probe_value (Arr \<sigma> (Arr \<tau> \<sigma>))"
  by (simp add: book_ZF_k_def probe_value.simps Lambda_ext Singleton Fst Snd probe_i_def)

lemma probe_s:
  "book_ZF_s probe_W (=) probe_D Empty \<sigma> \<tau> \<rho> =
    probe_value (Arr (Arr \<sigma> (Arr \<tau> \<rho>)) (Arr (Arr \<sigma> \<tau>) (Arr \<sigma> \<rho>)))"
  by (simp add: book_ZF_s_def probe_value.simps Lambda_ext Singleton Fst Snd Lambda_app)

lemma probe_imp:
  "book_ZF_if_future probe_W (=) probe_D probe_i Empty =
    probe_value (Arr Prop (Arr Prop Prop))"
  by (simp add: book_ZF_if_future_def probe_value.simps Lambda_ext Singleton Fst Snd
      probe_i_def probe_collect_true)

lemma probe_all:
  "book_ZF_all probe_W (=) probe_D Empty \<sigma> = probe_value (Arr (Arr \<sigma> Prop) Prop)"
  by (simp add: book_ZF_all_def probe_value.simps Lambda_ext Singleton Fst Snd
      Lambda_app probe_collect_true)

lemma probe_eq:
  "book_ZF_eq probe_W (=) probe_D probe_i Empty \<sigma> =
    probe_value (Arr \<sigma> (Arr \<sigma> Prop))"
  by (simp add: book_ZF_eq_def probe_value.simps Lambda_ext Singleton Fst Snd
      probe_i_def probe_collect_true)

theorem probe_model:
  "book_ZF_modal_model probe_W (=) Empty probe_D probe_i probe_signature probe_I"
  apply (rule book_ZF_modal_model.intro[OF probe_structure])
  apply (rule book_ZF_modal_model_axioms.intro)
  apply (simp_all add: probe_k probe_s probe_imp probe_all probe_eq probe_signature_def)
  done

interpretation Probe: book_ZF_modal_model probe_W "(=)" Empty probe_D probe_i probe_signature probe_I
  by (rule probe_model)

lemma probe_assignment:
  "book_env_typed (\<lambda>\<sigma>. explode (probe_D \<sigma> Empty)) G (\<lambda>n. probe_value (G n))"
  by (simp add: book_env_typed_def)

theorem probe_all_formulas_true:
  assumes language: "book_in_language book_minimal_logical_type UNIV probe_signature G A Prop"
  shows "book_ZF_formula_valid probe_D G (Probe.generic_interpretation G) Empty A"
proof -
  interpret J: book_ZF_modal_interpretation probe_W "(=)" Empty probe_D probe_i
    probe_signature probe_I G "Probe.generic_interpretation G"
    by (rule Probe.generic_interpretation_model)
  have val_eq: "Probe.generic_interpretation G Empty g A = probe_W"
    if typed: "book_env_typed (\<lambda>\<sigma>. explode (probe_D \<sigma> Empty)) G g" for g
    using J.denote_type[OF _ language typed] by simp
  show ?thesis
    unfolding book_ZF_formula_valid_def book_ZF_truth_at_def
    using val_eq by auto
qed

theorem probe_bottom_true:
  assumes rich: "sg_rich G"
  shows "book_ZF_satisfies probe_D G (Probe.generic_interpretation G) Empty {book_bottom G}"
  unfolding book_ZF_satisfies_def
  using probe_all_formulas_true[OF book_bottom_language[OF rich]] by simp

theorem probe_bottom_inconsistent:
  assumes rich: "sg_rich G"
  shows "\<not> book_full_C_theory_consistent probe_signature G {book_bottom G}"
proof -
  have derivation: "book_full_C_theory_derivable probe_signature G {book_bottom G} (book_bottom G)"
    unfolding book_full_C_theory_derivable_def
    by (rule book_theory_derivable.Assumption; (simp | rule book_bottom_language[OF rich]))
  show ?thesis using derivation unfolding book_full_C_theory_consistent_def by blast
qed

theorem probe_inconsistent_theory_has_model:
  "book_ZF_modal_model probe_W (=) Empty probe_D probe_i probe_signature probe_I
    \<and> book_ZF_modal_interpretation probe_W (=) Empty probe_D probe_i
      probe_signature probe_I sg_standard_stock (Probe.generic_interpretation sg_standard_stock)
    \<and> book_ZF_satisfies probe_D sg_standard_stock
      (Probe.generic_interpretation sg_standard_stock) Empty {book_bottom sg_standard_stock}
    \<and> \<not> book_full_C_theory_consistent probe_signature sg_standard_stock
      {book_bottom sg_standard_stock}"
  by (intro conjI; rule probe_model Probe.generic_interpretation_model
      probe_bottom_true[OF sg_standard_stock_rich]
      probe_bottom_inconsistent[OF sg_standard_stock_rich])

theorem probe_not_nontrivial:
  "\<not> book_ZF_nontrivial_modal_model probe_W (=) Empty probe_D probe_i probe_signature probe_I"
proof
  assume refined: "book_ZF_nontrivial_modal_model probe_W (=) Empty probe_D probe_i probe_signature probe_I"
  interpret N: book_ZF_nontrivial_modal_model probe_W "(=)" Empty probe_D probe_i probe_signature probe_I
    by (rule refined)
  have "\<exists>p\<in>explode (probe_D Prop Empty). \<not> Elem Empty p"
    by (rule N.false_at_root)
  then show False by simp
qed

text \<open>
  The broad structural class admits an actual inconsistent satisfiable
  theory. All domains and the displayed assignment are inhabited; the
  counterexample is not a vacuous universal quantification over assignments.
  The explicit nontrivial refinement excludes it. This does not prove
  soundness or the complete consistency characterization for the refinement.
\<close>

ML_file "../../../../core_audit/Bacon_Core_Audit_Check.ML"

ML \<open>
local
  val targets =
   [("the inhabited singleton data form a structural modal model", "probe_model"),
    ("the singleton model has an explicit typed assignment", "probe_assignment"),
    ("every well-typed formula is true in the singleton model", "probe_all_formulas_true"),
    ("the singleton model satisfies bottom", "probe_bottom_true"),
    ("the singleton bottom premise is syntactically inconsistent", "probe_bottom_inconsistent"),
    ("a concrete inconsistent theory has a structural modal model", "probe_inconsistent_theory_has_model"),
    ("the nontrivial model refinement excludes the singleton model", "probe_not_nontrivial")]
  val checked = Bacon_Core_Audit_Check.run @{context} "book-zf-singleton"
    (map_index (fn (i, (label, fact)) => (i, label, fact)) targets)
  val report = "FOUNDATION: standard HOL-ZF; not pure HOL\n"
    ^ "SCOPE: actual inhabited all-true structural model, inconsistent satisfiable premise set, and exclusion by the explicit nontrivial refinement\n"
    ^ Bacon_Core_Audit_Check.aggregate targets checked
in
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "book-zf-singleton-audit.txt")) [XML.Text report]
  val _ = writeln report
end
\<close>

end
