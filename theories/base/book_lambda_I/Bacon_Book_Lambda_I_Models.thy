theory Bacon_Book_Lambda_I_Models
  imports Bacon_Book_Lambda_I_Presentations
    Bacon_Book_Environment_Development.Bacon_Book_Full_Minimal_Model
    Bacon_Book_Environment_Development.Bacon_Book_Minimal_Validity
begin

section \<open>General models of the λI language and soundness\<close>

text \<open>
  Definition 15.1 (pp.314–315) over a general interpretation of the λI
  language (Definition 14.13): an applicative structure with a total
  denotation on λI terms satisfying the variable and application clauses
  and the environment clause, a valuation on propositions with the
  implication and universal clauses for the minimal signature on every
  domain element, and a false proposition. The environment clause is
  stated for internal λI conversion (Definition 14.13 read through
  Proposition 9.1); every raw-βη-invariant interpretation, in particular
  every restriction of a full minimal model, satisfies it. Logical
  constants have witnessed values κ, and a typed assignment exists (the
  same convention as book_full_minimal_model); for a rich stock this makes
  every domain inhabited. No Functionality, identity clause or full
  function space is assumed.
\<close>

locale book_lambda_I_model = book_applicative_structure domain app
  for domain :: "otype \<Rightarrow> 'v set"
    and app :: "otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes signature :: "'c ssignature" and stock :: sgcontext
    and denote :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'c book_named_term \<Rightarrow> 'v"
    and V :: "'v \<Rightarrow> bool" and \<kappa> :: "book_minimal_logical \<Rightarrow> 'v"
  assumes denote_type:
    "A \<in> book_LI signature stock \<sigma> \<Longrightarrow> book_env_typed domain stock g \<Longrightarrow> denote g A \<in> domain \<sigma>"
    and denote_var: "book_env_typed domain stock g \<Longrightarrow> denote g (NVar n) = g n"
    and denote_app:
    "F \<in> book_LI signature stock (Arr \<sigma> \<tau>) \<Longrightarrow> A \<in> book_LI signature stock \<sigma> \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (denote g A)"
    and environment:
    "book_lambda_I_conv signature stock \<sigma> A B \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> book_env_typed domain stock h \<Longrightarrow>
     (\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n) \<Longrightarrow> denote g A = denote h B"
    and logical_value: "book_env_typed domain stock g \<Longrightarrow> denote g (NLogical l) = \<kappa> l"
    and assignment_exists: "\<exists>g. book_env_typed domain stock g"
    and implication_truth:
    "p \<in> domain Prop \<Longrightarrow> q \<in> domain Prop \<Longrightarrow>
     V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) p) q) = (V p \<longrightarrow> V q)"
    and forall_truth:
    "f \<in> domain (Arr \<sigma> Prop) \<Longrightarrow>
     V (app (Arr \<sigma> Prop) Prop (\<kappa> (SBAll \<sigma>)) f) = (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
    and false_proposition: "\<exists>f \<in> domain Prop. \<not> V f"
begin

lemma book_LI_logical: "NLogical l \<in> book_LI signature stock (book_minimal_logical_type l)"
  by (rule book_LI_I[OF book_language_Logical[OF UNIV_I]]) simp

lemma logical_value_type: "\<kappa> l \<in> domain (book_minimal_logical_type l)"
proof -
  obtain g where typed: "book_env_typed domain stock g" using assignment_exists by blast
  show ?thesis using denote_type[OF book_LI_logical typed] by (simp only: logical_value[OF typed])
qed

lemma denote_locality:
  assumes member: "A \<in> book_LI signature stock \<sigma>"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "denote g A = denote h A"
  by (rule environment[OF book_lambda_I_conv.Refl[OF member] gt ht]) (simp add: agree)

lemma denote_conv:
  assumes conversion: "book_lambda_I_conv signature stock \<sigma> A B" and typed: "book_env_typed domain stock g"
  shows "denote g A = denote g B"
  by (rule environment[OF conversion typed typed]) (rule refl)

subsection \<open>Truth clauses\<close>

lemma imp_truth:
  assumes typed: "book_env_typed domain stock g"
    and al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
  shows "V (denote g (book_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
proof -
  have am: "A \<in> book_LI signature stock Prop" and bm: "B \<in> book_LI signature stock Prop"
    using al bl by (simp_all only: book_lambda_I_formula_terms)
  have opm: "NLogical SImp \<in> book_LI signature stock (Arr Prop (Arr Prop Prop))"
    using book_LI_logical[of SImp] by simp
  have partial_member: "NApp (NLogical SImp) A \<in> book_LI signature stock (Arr Prop Prop)"
    by (rule book_LI_App[OF opm am])
  have partial: "denote g (NApp (NLogical SImp) A) = app Prop (Arr Prop Prop) (\<kappa> SImp) (denote g A)"
    by (simp only: denote_app[OF opm am typed] logical_value[OF typed])
  have whole: "denote g (book_imp A B) = app Prop Prop (denote g (NApp (NLogical SImp) A)) (denote g B)"
    unfolding book_imp_def by (rule denote_app[OF partial_member bm typed])
  show ?thesis
    by (simp only: whole partial implication_truth[OF denote_type[OF am typed] denote_type[OF bm typed]])
qed

lemma forall_application_truth:
  assumes typed: "book_env_typed domain stock g" and fm: "F \<in> book_LI signature stock (Arr \<sigma> Prop)"
  shows "V (denote g (NApp (NLogical (SBAll \<sigma>)) F)) = (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop (denote g F) a))"
proof -
  have application: "denote g (NApp (NLogical (SBAll \<sigma>)) F) =
    app (Arr \<sigma> Prop) Prop (\<kappa> (SBAll \<sigma>)) (denote g F)"
    by (simp only: denote_app[OF book_LI_all_operator fm typed] logical_value[OF typed])
  show ?thesis by (simp only: application forall_truth[OF denote_type[OF fm typed]])
qed

theorem lambda_application:
  assumes body: "M \<in> book_LI signature stock \<tau>" and occurs: "n \<in> named_fv M"
    and typed: "book_env_typed domain stock g" and member: "a \<in> domain (stock n)"
  shows "app (stock n) \<tau> (denote g (NLam n M)) a = denote (g(n := a)) M"
proof -
  let ?h = "g(n := a)"
  let ?F = "NLam n M"
  let ?R = "NApp ?F (NVar n)"
  have ht: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed member])
  have fm: "?F \<in> book_LI signature stock (Arr (stock n) \<tau>)" by (rule book_LI_Lam[OF body occurs])
  have rm: "?R \<in> book_LI signature stock \<tau>" by (rule book_LI_App[OF fm book_LI_Var])
  have beta_root: "named_beta_contract ?R M"
    using named_beta_contract.beta[OF named_free_for_self_variable[of n M]] by (simp only: named_subst_same_variable)
  have beta_step: "named_compatible_step named_beta_contract ?R M"
    by (rule named_compatible_step.root[where R=named_beta_contract and M="?R" and N=M, OF beta_root])
  have conversion: "book_lambda_I_conv signature stock \<tau> ?R M" by (rule book_lambda_I_conv.Beta[OF rm body beta_step])
  have beta: "denote ?h ?R = denote ?h M" by (rule denote_conv[OF conversion ht])
  have lambda_eq: "denote ?h ?F = denote g ?F"
    by (rule denote_locality[OF fm ht typed]) simp
  have variable_eq: "denote ?h (NVar n) = a" using denote_var[OF ht] by simp
  have application: "denote ?h ?R = app (stock n) \<tau> (denote ?h ?F) (denote ?h (NVar n))"
    by (rule denote_app[OF fm book_LI_Var ht])
  show ?thesis using application by (simp only: lambda_eq variable_eq beta)
qed

theorem all_truth:
  assumes typed: "book_env_typed domain stock g"
    and bl: "book_lambda_I_formula signature stock B" and occurs: "n \<in> named_fv B"
  shows "V (denote g (book_all stock n B)) = (\<forall>a \<in> domain (stock n). V (denote (g(n := a)) B))"
proof -
  have bm: "B \<in> book_LI signature stock Prop" using bl by (simp only: book_lambda_I_formula_terms)
  have fm: "NLam n B \<in> book_LI signature stock (Arr (stock n) Prop)" by (rule book_LI_Lam[OF bm occurs])
  have primitive: "V (denote g (book_all stock n B)) =
    (\<forall>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n B)) a))"
    unfolding book_all_def by (rule forall_application_truth[OF typed fm])
  have body: "(\<forall>a \<in> domain (stock n). V (app (stock n) Prop (denote g (NLam n B)) a)) =
    (\<forall>a \<in> domain (stock n). V (denote (g(n := a)) B))"
  proof (rule ball_cong[OF refl])
    fix a assume member: "a \<in> domain (stock n)"
    show "V (app (stock n) Prop (denote g (NLam n B)) a) = V (denote (g(n := a)) B)"
      by (simp only: lambda_application[OF bm occurs typed member])
  qed
  show ?thesis by (rule trans[OF primitive body])
qed

theorem bottom_false:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
  shows "\<not> V (denote g (book_bottom stock))"
proof
  assume truth: "V (denote g (book_bottom stock))"
  let ?p = "book_prop_name stock"
  have ptype: "stock ?p = Prop" by (rule book_prop_name_type[OF rich])
  have vl: "book_lambda_I_formula signature stock (NVar ?p)" by (simp add: book_language_var_iff ptype)
  have universal: "V (denote g (book_bottom stock)) = (\<forall>a \<in> domain Prop. V (denote (g(?p := a)) (NVar ?p)))"
    using all_truth[where n="?p", OF typed vl] by (simp only: book_bottom_as_all[OF rich] ptype) simp
  obtain f where fm: "f \<in> domain Prop" and false_f: "\<not> V f" using false_proposition by blast
  have updated: "book_env_typed domain stock (g(?p := f))" by (rule book_env_update[OF typed]) (simp only: ptype fm)
  have variable_value: "denote (g(?p := f)) (NVar ?p) = f" using denote_var[OF updated] by simp
  have witness_truth: "V (denote (g(?p := f)) (NVar ?p))" by (rule bspec[OF truth[unfolded universal] fm])
  have Vf: "V f" using witness_truth by (simp only: variable_value)
  show False by (rule notE[OF false_f Vf])
qed

theorem not_truth:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and al: "book_lambda_I_formula signature stock A"
  shows "V (denote g (book_not stock A)) = (\<not> V (denote g A))"
proof -
  let ?p = "book_prop_name stock"
  let ?body = "book_imp (NVar ?p) (book_bottom stock)"
  let ?a = "denote g A"
  have ptype: "stock ?p = Prop" by (rule book_prop_name_type[OF rich])
  have am: "A \<in> book_LI signature stock Prop" using al by (simp only: book_lambda_I_formula_terms)
  have vl: "book_lambda_I_formula signature stock (NVar ?p)" by (simp add: book_language_var_iff ptype)
  have bottom_l: "book_lambda_I_formula signature stock (book_bottom stock)"
    by (simp add: book_bottom_language[OF rich] book_lambda_I_bottom)
  have body_l: "book_lambda_I_formula signature stock ?body" using vl bottom_l by (simp add: book_lambda_I_imp_formula)
  have body_m: "?body \<in> book_LI signature stock Prop" using body_l by (simp only: book_lambda_I_formula_terms)
  have occurs: "?p \<in> named_fv ?body" by (simp add: book_imp_fv)
  have const_m: "NLam ?p ?body \<in> book_LI signature stock (Arr Prop Prop)"
    using book_LI_Lam[OF body_m occurs] by (simp only: ptype)
  have a_member: "?a \<in> domain (stock ?p)" using denote_type[OF am typed] by (simp only: ptype)
  have updated: "book_env_typed domain stock (g(?p := ?a))" by (rule book_env_update[OF typed a_member])
  have application: "denote g (book_not stock A) = app Prop Prop (denote g (NLam ?p ?body)) ?a"
    using denote_app[OF const_m am typed] by (simp only: book_not_def book_not_const_def)
  have applied: "app Prop Prop (denote g (NLam ?p ?body)) ?a = denote (g(?p := ?a)) ?body"
    using lambda_application[OF body_m occurs typed a_member] by (simp only: ptype)
  have body_truth: "V (denote (g(?p := ?a)) ?body) = (V (denote (g(?p := ?a)) (NVar ?p)) \<longrightarrow> V (denote (g(?p := ?a)) (book_bottom stock)))"
    by (rule imp_truth[OF updated vl bottom_l])
  have variable_value: "denote (g(?p := ?a)) (NVar ?p) = ?a" using denote_var[OF updated] by simp
  show ?thesis
    by (simp only: application applied body_truth variable_value bottom_false[OF rich updated]) simp
qed

subsection \<open>Soundness of the λI calculus\<close>

lemma PC1_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
  shows "book_formula_valid domain stock denote V (book_imp A (book_imp B A))"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have ba: "book_lambda_I_formula signature stock (book_imp B A)" using al bl by (simp add: book_lambda_I_imp_formula)
  show "V (denote g (book_imp A (book_imp B A)))"
    by (simp only: imp_truth[OF typed al ba] imp_truth[OF typed bl al]; blast)
qed

lemma PC2_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and cl: "book_lambda_I_formula signature stock C"
  shows "book_formula_valid domain stock denote V
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have bc: "book_lambda_I_formula signature stock (book_imp B C)" using bl cl by (simp add: book_lambda_I_imp_formula)
  have abc: "book_lambda_I_formula signature stock (book_imp A (book_imp B C))" using al bc by (simp add: book_lambda_I_imp_formula)
  have ab: "book_lambda_I_formula signature stock (book_imp A B)" using al bl by (simp add: book_lambda_I_imp_formula)
  have ac: "book_lambda_I_formula signature stock (book_imp A C)" using al cl by (simp add: book_lambda_I_imp_formula)
  have conclusion: "book_lambda_I_formula signature stock (book_imp (book_imp A B) (book_imp A C))"
    using ab ac by (simp add: book_lambda_I_imp_formula)
  show "V (denote g (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C))))"
    by (simp only: imp_truth[OF typed abc conclusion] imp_truth[OF typed al bc] imp_truth[OF typed bl cl]
      imp_truth[OF typed ab ac] imp_truth[OF typed al bl] imp_truth[OF typed al cl]; blast)
qed

lemma PC3_valid:
  assumes rich: "sg_rich stock"
    and al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
  shows "book_formula_valid domain stock denote V
    (book_imp (book_imp (book_not stock A) (book_not stock B)) (book_imp B A))"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have na: "book_lambda_I_formula signature stock (book_not stock A)"
    using al by (simp add: book_not_language[OF rich] book_lambda_I_not)
  have nb: "book_lambda_I_formula signature stock (book_not stock B)"
    using bl by (simp add: book_not_language[OF rich] book_lambda_I_not)
  have nab: "book_lambda_I_formula signature stock (book_imp (book_not stock A) (book_not stock B))"
    using na nb by (simp add: book_lambda_I_imp_formula)
  have ba: "book_lambda_I_formula signature stock (book_imp B A)" using al bl by (simp add: book_lambda_I_imp_formula)
  show "V (denote g (book_imp (book_imp (book_not stock A) (book_not stock B)) (book_imp B A)))"
    by (simp only: imp_truth[OF typed nab ba] imp_truth[OF typed na nb] not_truth[OF rich typed al]
      not_truth[OF rich typed bl] imp_truth[OF typed bl al]; blast)
qed

lemma UI_valid:
  assumes fm: "F \<in> book_LI signature stock (Arr \<sigma> Prop)" and am: "a \<in> book_LI signature stock \<sigma>"
  shows "book_formula_valid domain stock denote V (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have ul: "book_lambda_I_formula signature stock (NApp (NLogical (SBAll \<sigma>)) F)"
    using book_LI_App[OF book_LI_all_operator fm] by (simp only: book_lambda_I_formula_terms)
  have il: "book_lambda_I_formula signature stock (NApp F a)"
    using book_LI_App[OF fm am] by (simp only: book_lambda_I_formula_terms)
  have implication: "V (denote g (NApp (NLogical (SBAll \<sigma>)) F)) \<longrightarrow> V (denote g (NApp F a))"
  proof
    assume all_true: "V (denote g (NApp (NLogical (SBAll \<sigma>)) F))"
    have every: "\<forall>x \<in> domain \<sigma>. V (app \<sigma> Prop (denote g F) x)"
      by (rule iffD1[OF forall_application_truth[OF typed fm] all_true])
    have tested: "V (app \<sigma> Prop (denote g F) (denote g a))" by (rule bspec[OF every denote_type[OF am typed]])
    show "V (denote g (NApp F a))" by (simp only: denote_app[OF fm am typed]; rule tested)
  qed
  show "V (denote g (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a)))"
    by (rule iffD2[OF imp_truth[OF typed ul il] implication])
qed

lemma conversion_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and conversion: "book_lambda_I_conv signature stock Prop A B"
  shows "book_formula_valid domain stock denote V (book_imp A B)"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  show "V (denote g (book_imp A B))"
    by (simp only: imp_truth[OF typed al bl] denote_conv[OF conversion typed]; blast)
qed

lemma beta_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and step: "named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A"
  shows "book_formula_valid domain stock denote V (book_imp A B)"
proof (rule conversion_valid[OF al bl])
  have am: "A \<in> book_LI signature stock Prop" and bm: "B \<in> book_LI signature stock Prop"
    using al bl by (simp_all only: book_lambda_I_formula_terms)
  show "book_lambda_I_conv signature stock Prop A B"
    using step book_lambda_I_conv.Beta[OF am bm] book_lambda_I_conv.Sym[OF book_lambda_I_conv.Beta[OF bm am]] by blast
qed

lemma eta_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and step: "named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A"
  shows "book_formula_valid domain stock denote V (book_imp A B)"
proof (rule conversion_valid[OF al bl])
  have am: "A \<in> book_LI signature stock Prop" and bm: "B \<in> book_LI signature stock Prop"
    using al bl by (simp_all only: book_lambda_I_formula_terms)
  show "book_lambda_I_conv signature stock Prop A B"
    using step book_lambda_I_conv.Eta[OF am bm] book_lambda_I_conv.Sym[OF book_lambda_I_conv.Eta[OF bm am]] by blast
qed

lemma MP_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and antecedent: "book_formula_valid domain stock denote V A"
    and conditional: "book_formula_valid domain stock denote V (book_imp A B)"
  shows "book_formula_valid domain stock denote V B"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have material: "V (denote g (book_imp A B)) = (V (denote g A) \<longrightarrow> V (denote g B))"
    by (rule imp_truth[OF typed al bl])
  show "V (denote g B)"
    by (rule mp[OF book_formula_validE[OF conditional typed, unfolded material] book_formula_validE[OF antecedent typed]])
qed

lemma Gen_valid:
  assumes al: "book_lambda_I_formula signature stock A" and bl: "book_lambda_I_formula signature stock B"
    and fresh: "n \<notin> named_fv A" and occurs: "n \<in> named_fv B"
    and conditional: "book_formula_valid domain stock denote V (book_imp A B)"
  shows "book_formula_valid domain stock denote V (book_imp A (book_all stock n B))"
proof (rule book_formula_validI)
  fix g assume typed: "book_env_typed domain stock g"
  have am: "A \<in> book_LI signature stock Prop" using al by (simp only: book_lambda_I_formula_terms)
  have all_l: "book_lambda_I_formula signature stock (book_all stock n B)"
    using bl occurs by (simp add: book_lambda_I_all book_all_language)
  have implication: "V (denote g A) \<longrightarrow> V (denote g (book_all stock n B))"
  proof
    assume a_true: "V (denote g A)"
    show "V (denote g (book_all stock n B))"
    proof (simp only: all_truth[OF typed bl occurs], rule ballI)
      fix a assume member: "a \<in> domain (stock n)"
      let ?h = "g(n := a)"
      have ht: "book_env_typed domain stock ?h" by (rule book_env_update[OF typed member])
      have same_A: "denote ?h A = denote g A"
        by (rule denote_locality[OF am ht typed]) (use fresh in auto)
      have step: "V (denote ?h A) \<longrightarrow> V (denote ?h B)"
        using book_formula_validE[OF conditional ht] by (simp only: imp_truth[OF ht al bl])
      show "V (denote ?h B)" using step a_true by (simp only: same_A)
    qed
  qed
  show "V (denote g (book_imp A (book_all stock n B)))" by (rule iffD2[OF imp_truth[OF typed al all_l] implication])
qed

theorem book_lambda_I_soundness:
  assumes rich: "sg_rich stock"
    and derivation: "book_lambda_I_derivable signature stock S A"
    and premises_valid: "\<And>B. B \<in> S \<Longrightarrow> book_formula_valid domain stock denote V B"
  shows "book_formula_valid domain stock denote V A"
  using derivation premises_valid
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule PC1_valid[OF PC1.hyps])
next
  case PC2
  show ?case by (rule PC2_valid[OF PC2.hyps])
next
  case PC3
  show ?case by (rule PC3_valid[OF rich PC3.hyps])
next
  case UI
  show ?case by (rule UI_valid[OF UI.hyps])
next
  case Beta
  show ?case by (rule beta_valid[OF Beta.hyps])
next
  case Eta
  show ?case by (rule eta_valid[OF Eta.hyps])
next
  case (MP S A B)
  have al: "book_lambda_I_formula signature stock A"
    by (rule book_lambda_I_derivable_formula[OF MP.hyps(1) rich])
  show ?case by (rule MP_valid[OF al MP.hyps(3) MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems]])
next
  case Gen
  show ?case by (rule Gen_valid[OF Gen.hyps(2,3,4,5) Gen.IH[OF Gen.prems]])
qed

theorem book_lambda_I_satisfiable_consistent:
  assumes rich: "sg_rich stock"
    and premises_valid: "\<And>B. B \<in> S \<Longrightarrow> book_formula_valid domain stock denote V B"
  shows "book_lambda_I_consistent signature stock S"
proof (unfold book_lambda_I_consistent_def, rule notI)
  assume bottom: "book_lambda_I_derivable signature stock S (book_bottom stock)"
  have valid: "book_formula_valid domain stock denote V (book_bottom stock)"
    by (rule book_lambda_I_soundness[OF rich bottom premises_valid])
  obtain g where typed: "book_env_typed domain stock g" using assignment_exists by blast
  show False by (rule notE[OF bottom_false[OF rich typed] book_formula_validE[OF valid typed]])
qed

end

subsection \<open>Every full minimal model restricts to a λI model\<close>

theorem book_full_minimal_model_lambda_I:
  assumes full: "book_full_minimal_model domain app \<Sigma> G denote V \<kappa>"
  shows "book_lambda_I_model domain app \<Sigma> G denote V \<kappa>"
proof -
  interpret Full: book_full_minimal_model domain app \<Sigma> G denote V \<kappa> by (rule full)
  show ?thesis
  proof (unfold_locales)
    fix A \<sigma> g
    assume member: "A \<in> book_LI \<Sigma> G \<sigma>" and typed: "book_env_typed domain G g"
    show "denote g A \<in> domain \<sigma>" by (rule Full.denote_type[OF UNIV_I book_lambda_I_terms_language[OF member] typed])
  next
    fix g n
    assume typed: "book_env_typed domain G g"
    show "denote g (NVar n) = g n" by (rule Full.denote_var[OF UNIV_I typed])
  next
    fix F A \<sigma> \<tau> g
    assume fm: "F \<in> book_LI \<Sigma> G (Arr \<sigma> \<tau>)" and am: "A \<in> book_LI \<Sigma> G \<sigma>" and typed: "book_env_typed domain G g"
    show "denote g (NApp F A) = app \<sigma> \<tau> (denote g F) (denote g A)"
      by (rule Full.denote_app[OF UNIV_I UNIV_I UNIV_I book_lambda_I_terms_language[OF fm]
        book_lambda_I_terms_language[OF am] typed])
  next
    fix A B \<sigma> g h
    assume conversion: "book_lambda_I_conv \<Sigma> G \<sigma> A B"
      and gt: "book_env_typed domain G g" and ht: "book_env_typed domain G h"
      and agree: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
    have am: "A \<in> book_LI \<Sigma> G \<sigma>" and bm: "B \<in> book_LI \<Sigma> G \<sigma>"
      using book_lambda_I_conv_terms[OF conversion] by blast+
    show "denote g A = denote h B"
      by (rule Full.environment[OF UNIV_I UNIV_I book_lambda_I_terms_language[OF am]
        book_lambda_I_terms_language[OF bm] book_lambda_I_conv_raw[OF conversion] gt ht agree])
  next
    fix g l
    assume typed: "book_env_typed domain G g"
    show "denote g (NLogical l) = \<kappa> l" by (rule Full.book_minimal_logical_value_at[OF typed])
  next
    show "\<exists>g. book_env_typed domain G g" by (rule Full.book_minimal_assignment_exists)
  next
    fix p q
    assume pm: "p \<in> domain Prop" and qm: "q \<in> domain Prop"
    show "V (app Prop Prop (app Prop (Arr Prop Prop) (\<kappa> SImp) p) q) = (V p \<longrightarrow> V q)"
      by (rule Full.implication_truth[OF pm qm])
  next
    fix f \<sigma>
    assume fm: "f \<in> domain (Arr \<sigma> Prop)"
    show "V (app (Arr \<sigma> Prop) Prop (\<kappa> (SBAll \<sigma>)) f) = (\<forall>a \<in> domain \<sigma>. V (app \<sigma> Prop f a))"
      by (rule Full.forall_truth[OF fm])
  next
    show "\<exists>f \<in> domain Prop. \<not> V f" by (rule Full.false_proposition)
  qed
qed

text \<open>
  Soundness (Theorem 15.1 for the λI calculus): every λI derivation from
  premises true under every typed assignment yields a formula true under
  every typed assignment, in every λI model. Satisfiable premise sets are
  λI-consistent. A rich stock is needed for the PC3 language guard
  (book_not_language), hence in the PC3 case, in the MP case through
  book_lambda_I_derivable_formula, and in the consistency corollary. Every full
  minimal model is a λI model, so full-language countermodels serve as λI
  countermodels; the converse class inclusion is not asserted.
\<close>

end
