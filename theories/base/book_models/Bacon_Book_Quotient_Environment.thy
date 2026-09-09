theory Bacon_Book_Quotient_Environment
  imports Bacon_Book_Quotient_Application
begin

section \<open>Choosing the displayed type and lifting quotient assignments\<close>

text \<open>
  Interpret a quotient assignment q by choosing one representative of each
  class q(x). For M:τ, define J̄q(M) = [Jrep(q)(M)]τ.
  Source role: the interpretation component of Bacon's Proposition 15.5,
  p.322, retaining the environment condition of Definition 14.13, p.302.

  Isabelle representation. A total selected-type function returns τ under
  the explicit book-language guard, by type uniqueness. A total class
  representative is used only under quotient-domain membership. Lifting
  a typed quotient assignment therefore gives a typed original assignment
  without any separate domain-nonemptiness hypothesis.

  Status. No valuation or logical-model clause is asserted. The original
  full environment, its logical and nonlogical signatures, and its stock
  remain explicit. Richness and an original typed assignment are used for
  the already proved application congruence, not to select representatives.
\<close>

definition book_selected_type where
  "book_selected_type L \<Lambda> \<Sigma> G M = (SOME \<tau>. book_in_language L \<Lambda> \<Sigma> G M \<tau>)"

lemma book_selected_type_eq:
  assumes language: "book_in_language L \<Lambda> \<Sigma> G M \<tau>"
  shows "book_selected_type L \<Lambda> \<Sigma> G M = \<tau>"
proof -
  have exists_type: "\<exists>\<sigma>. book_in_language L \<Lambda> \<Sigma> G M \<sigma>"
    by (rule exI[where x=\<tau>], rule language)
  have selected: "book_in_language L \<Lambda> \<Sigma> G M (book_selected_type L \<Lambda> \<Sigma> G M)"
    unfolding book_selected_type_def by (rule someI_ex[OF exists_type])
  show ?thesis by (rule book_language_type_unique[OF selected language])
qed

definition book_leibniz_lift_assignment :: "(nat \<Rightarrow> 'v set) \<Rightarrow> nat \<Rightarrow> 'v" where
  "book_leibniz_lift_assignment q n = book_leibniz_rep (q n)"

lemma book_leibniz_lift_assignment_typed:
  assumes typed: "book_env_typed (book_leibniz_quotient_domain D app V) G q"
  shows "book_env_typed D G (book_leibniz_lift_assignment q)"
proof (unfold book_env_typed_def, rule allI)
  fix n
  have member: "q n \<in> book_leibniz_quotient_domain D app V (G n)"
    by (rule book_env_at[where n=n, OF typed])
  show "book_leibniz_lift_assignment q n \<in> D (G n)"
    unfolding book_leibniz_lift_assignment_def by (rule book_leibniz_rep_type[OF member])
qed

lemma book_leibniz_lift_assignment_projection:
  assumes typed: "book_env_typed (book_leibniz_quotient_domain D app V) G q"
  shows "book_leibniz_class D app V (G n) (book_leibniz_lift_assignment q n) = q n"
proof -
  have member: "q n \<in> book_leibniz_quotient_domain D app V (G n)"
    by (rule book_env_at[where n=n, OF typed])
  show ?thesis unfolding book_leibniz_lift_assignment_def
    by (rule book_leibniz_rep_reconstruct[OF member])
qed

context book_full_environment
begin

definition book_leibniz_quotient_denote ::
  "('v \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'v set) \<Rightarrow> ('c,'l) named_term \<Rightarrow> 'v set" where
  "book_leibniz_quotient_denote V q M =
    book_leibniz_class domain app V (book_selected_type logical_type logical_signature signature stock M)
      (denote (book_leibniz_lift_assignment q) M)"

lemma book_leibniz_quotient_denote_eq:
  assumes language: "book_in_language logical_type logical_signature signature stock M \<tau>"
  shows "book_leibniz_quotient_denote V q M =
    book_leibniz_class domain app V \<tau> (denote (book_leibniz_lift_assignment q) M)"
  by (simp only: book_leibniz_quotient_denote_def book_selected_type_eq[OF language])

lemma book_leibniz_quotient_denote_type:
  assumes language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
  shows "book_leibniz_quotient_denote V q M \<in> book_leibniz_quotient_domain domain app V \<tau>"
proof -
  have lifted: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
    by (rule book_leibniz_lift_assignment_typed[OF typed])
  have original: "denote (book_leibniz_lift_assignment q) M \<in> domain \<tau>"
    by (rule denote_type[OF UNIV_I language lifted])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF language];
    rule book_leibniz_quotient_domainI[where D=domain and \<sigma>=\<tau>, OF original])
qed

lemma book_leibniz_quotient_denote_var:
  assumes typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
  shows "book_leibniz_quotient_denote V q (NVar n) = q n"
proof -
  have language: "book_in_language logical_type logical_signature signature stock (NVar n) (stock n)"
    by (rule book_language_Var)
  have lifted: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
    by (rule book_leibniz_lift_assignment_typed[OF typed])
  have variable: "denote (book_leibniz_lift_assignment q) (NVar n) = book_leibniz_lift_assignment q n"
    by (rule denote_var[OF UNIV_I lifted])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF language] variable
    book_leibniz_lift_assignment_projection[OF typed])
qed

lemma book_leibniz_quotient_denote_app:
  assumes rich: "sg_rich stock" and original_typed: "book_env_typed domain stock g0"
    and fl: "book_in_language logical_type logical_signature signature stock F (Arr \<sigma> \<tau>)"
    and al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
  shows "book_leibniz_quotient_denote V q (NApp F A) =
    book_leibniz_quotient_app domain app V \<sigma> \<tau>
      (book_leibniz_quotient_denote V q F) (book_leibniz_quotient_denote V q A)"
proof -
  let ?g = "book_leibniz_lift_assignment q"
  have gt: "book_env_typed domain stock ?g" by (rule book_leibniz_lift_assignment_typed[OF typed])
  have fa: "book_in_language logical_type logical_signature signature stock (NApp F A) \<tau>"
    by (rule book_language_App[OF fl al])
  have fm: "denote ?g F \<in> domain (Arr \<sigma> \<tau>)" by (rule denote_type[OF UNIV_I fl gt])
  have am: "denote ?g A \<in> domain \<sigma>" by (rule denote_type[OF UNIV_I al gt])
  have original: "denote ?g (NApp F A) = app \<sigma> \<tau> (denote ?g F) (denote ?g A)"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I fl al gt])
  have projection: "book_leibniz_quotient_app domain app V \<sigma> \<tau>
    (book_leibniz_class domain app V (Arr \<sigma> \<tau>) (denote ?g F))
    (book_leibniz_class domain app V \<sigma> (denote ?g A)) =
    book_leibniz_class domain app V \<tau> (app \<sigma> \<tau> (denote ?g F) (denote ?g A))"
    by (rule book_leibniz_quotient_application_projection[OF rich original_typed fm am])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF fa]
    book_leibniz_quotient_denote_eq[OF fl] book_leibniz_quotient_denote_eq[OF al] original projection)
qed

lemma book_leibniz_quotient_denote_conversion:
  assumes al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and bl: "book_in_language logical_type logical_signature signature stock B \<sigma>"
    and raw: "named_raw_beta_eta logical_type stock \<sigma> A B"
    and typed: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
  shows "book_leibniz_quotient_denote V q A = book_leibniz_quotient_denote V q B"
proof -
  have lifted: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
    by (rule book_leibniz_lift_assignment_typed[OF typed])
  have original: "denote (book_leibniz_lift_assignment q) A = denote (book_leibniz_lift_assignment q) B"
    by (rule book_denote_conversion[OF UNIV_I UNIV_I al bl raw lifted])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF al]
    book_leibniz_quotient_denote_eq[OF bl] original)
qed

lemma book_leibniz_quotient_denote_environment:
  assumes al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and bl: "book_in_language logical_type logical_signature signature stock B \<sigma>"
    and raw: "named_raw_beta_eta logical_type stock \<sigma> A B"
    and qt: "book_env_typed (book_leibniz_quotient_domain domain app V) stock q"
    and rt: "book_env_typed (book_leibniz_quotient_domain domain app V) stock r"
    and overlap: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> q n = r n"
  shows "book_leibniz_quotient_denote V q A = book_leibniz_quotient_denote V r B"
proof -
  have qlift: "book_env_typed domain stock (book_leibniz_lift_assignment q)"
    by (rule book_leibniz_lift_assignment_typed[OF qt])
  have rlift: "book_env_typed domain stock (book_leibniz_lift_assignment r)"
    by (rule book_leibniz_lift_assignment_typed[OF rt])
  have agrees: "book_leibniz_lift_assignment q n = book_leibniz_lift_assignment r n"
    if "n \<in> named_fv A \<inter> named_fv B" for n
    by (simp only: book_leibniz_lift_assignment_def overlap[OF that])
  have original: "denote (book_leibniz_lift_assignment q) A = denote (book_leibniz_lift_assignment r) B"
    by (rule environment[OF UNIV_I UNIV_I al bl raw qlift rlift agrees])
  show ?thesis by (simp only: book_leibniz_quotient_denote_eq[OF al]
    book_leibniz_quotient_denote_eq[OF bl] original)
qed

theorem book_leibniz_quotient_environment:
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g0"
  shows "book_full_environment (book_leibniz_quotient_domain domain app V)
    (book_leibniz_quotient_app domain app V) logical_type logical_signature signature stock
    (book_leibniz_quotient_denote V)"
  apply unfold_locales
      apply (rule book_leibniz_quotient_app_type; assumption)
     apply (rule book_leibniz_quotient_denote_type; assumption)
    apply (rule book_leibniz_quotient_denote_var; assumption)
   apply (rule book_leibniz_quotient_denote_app[OF rich typed]; assumption)
  apply (rule book_leibniz_quotient_denote_environment; assumption)
  done

end

end
