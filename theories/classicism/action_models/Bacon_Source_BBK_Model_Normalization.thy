theory Bacon_Source_BBK_Model_Normalization
  imports Bacon_Source_BBK_Model_Data
begin

section \<open>Only genuine interpretation inputs and propositional values matter\<close>

text \<open>
  J is source-defined at (g,A) when A has a type in the common language
  and g is typed and adequate for A. Normalize its total HOL extension
  to undefined elsewhere. Normalize V to False outside Dₜ.
  The domains are unchanged. These choices remove only values that the
  source model's interpretation and valuation do not specify.

  This leaf proves the defining agreements and canonical idempotence.
  Preservation of ALL BBK model clauses is a separate theorem, not
  assumed from these equations. No claim that raw unnormalized record
  equality is already source model equality is made.
\<close>

definition paper_bbk_input ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    'v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> bool" where
  "paper_bbk_input \<Sigma> G D g A \<longleftrightarrow>
    (\<exists>\<sigma>. named_in_language paper_logical_type \<Sigma> G A \<sigma>) \<and>
    named_env_typed D G g \<and> named_adequate g A"

lemma paper_bbk_inputI:
  assumes language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g A"
  shows "paper_bbk_input \<Sigma> G D g A"
  using language typed adequate unfolding paper_bbk_input_def by blast

definition paper_bbk_normalize ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow> ('c,'v) paper_bbk_model_data" where
  "paper_bbk_normalize \<Sigma> G M =
    \<lparr>paper_bbk_domain = paper_bbk_domain M,
     paper_bbk_denote = (\<lambda>g A. if paper_bbk_input \<Sigma> G (paper_bbk_domain M) g A
       then paper_bbk_denote M g A else undefined),
     paper_bbk_valuation = (\<lambda>a. if a \<in> paper_bbk_domain M Prop then paper_bbk_valuation M a else False)\<rparr>"

lemma paper_bbk_normalize_domain [simp]:
  "paper_bbk_domain (paper_bbk_normalize \<Sigma> G M) = paper_bbk_domain M"
  by (simp add: paper_bbk_normalize_def)

lemma paper_bbk_normalize_denote:
  assumes language: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) g A = paper_bbk_denote M g A"
  by (simp add: paper_bbk_normalize_def paper_bbk_inputI[OF language typed adequate])

lemma paper_bbk_normalize_denote_outside:
  assumes outside: "\<not> paper_bbk_input \<Sigma> G (paper_bbk_domain M) g A"
  shows "paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) g A = undefined"
  by (simp add: paper_bbk_normalize_def outside)

lemma paper_bbk_normalize_valuation:
  assumes member: "a \<in> paper_bbk_domain M Prop"
  shows "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M) a = paper_bbk_valuation M a"
  by (simp add: paper_bbk_normalize_def member)

lemma paper_bbk_normalize_valuation_outside:
  assumes outside: "a \<notin> paper_bbk_domain M Prop"
  shows "\<not> paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M) a"
  by (simp add: paper_bbk_normalize_def outside)

theorem paper_bbk_normalize_truth:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g A"
  shows "paper_bbk_valuation (paper_bbk_normalize \<Sigma> G M)
      (paper_bbk_denote (paper_bbk_normalize \<Sigma> G M) g A) =
    paper_bbk_valuation M (paper_bbk_denote M g A)"
proof -
  have member: "paper_bbk_denote M g A \<in> paper_bbk_domain M Prop"
    by (rule paper_bbk_data_denote_type[OF valid language typed adequate])
  show ?thesis by (simp only: paper_bbk_normalize_denote[OF language typed adequate];
    rule paper_bbk_normalize_valuation[OF member])
qed

theorem paper_bbk_normalize_idempotent:
  "paper_bbk_normalize \<Sigma> G (paper_bbk_normalize \<Sigma> G M) = paper_bbk_normalize \<Sigma> G M"
  by (rule paper_bbk_model_data.equality)
    (auto simp: paper_bbk_normalize_def fun_eq_iff)

theorem paper_bbk_normalize_cong:
  assumes domains: "paper_bbk_domain M = paper_bbk_domain N"
    and denotations: "\<And>g A. paper_bbk_input \<Sigma> G (paper_bbk_domain M) g A \<Longrightarrow>
      paper_bbk_denote M g A = paper_bbk_denote N g A"
    and valuations: "\<And>a. a \<in> paper_bbk_domain M Prop \<Longrightarrow> paper_bbk_valuation M a = paper_bbk_valuation N a"
  shows "paper_bbk_normalize \<Sigma> G M = paper_bbk_normalize \<Sigma> G N"
  by (rule paper_bbk_model_data.equality)
    (auto simp: paper_bbk_normalize_def fun_eq_iff domains[symmetric]
      intro: denotations dest: valuations)

end
