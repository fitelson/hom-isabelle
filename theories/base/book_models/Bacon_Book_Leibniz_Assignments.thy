theory Bacon_Book_Leibniz_Assignments
  imports Bacon_Book_Leibniz_Application
begin

section \<open>Finite assignment changes preserve denotation up to Leibniz equivalence\<close>

text \<open>
  If g(n) ≈ᴸᴱ h(n) for each n ∈ FV(M), then Jg(M) ≈ᴸᴱ Jh(M).
  First replace one value using the denotation of λn.M and application
  congruence. Induct over a finite set of replacements, then use actual
  locality for the assignment pasted from h on FV(M) and g elsewhere.
  Source role: representative independence for the Leibniz quotient in
  Bacon's Exercise 15.5 and Proposition 15.5, pp.321–322, using the full
  environment condition of Definition 14.13, p.302.

  Representation. The conclusion is Leibniz equivalence, not equality.
  The full-language, rich-stock and typed-total-assignment prerequisites
  are explicit. No Functionality, separation, logical truth clause, or
  pre-existing quotient interpretation is assumed.
\<close>

lemma book_paste_empty:
  "book_paste_assignment {} h g = g"
  by (rule ext) (simp add: book_paste_assignment_def)

lemma book_paste_insert:
  "book_paste_assignment (insert n X) h g = (book_paste_assignment X h g)(n := h n)"
  by (rule ext, rename_tac m, case_tac "m = n") (simp_all add: book_paste_assignment_def)

context book_full_environment
begin

lemma book_leibniz_denote_two_updates:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and equivalent: "book_leibniz_equiv domain app V (stock n) a b"
  shows "book_leibniz_equiv domain app V \<tau> (denote (g(n := a)) M) (denote (g(n := b)) M)"
proof -
  have am: "a \<in> domain (stock n)" by (rule book_leibniz_left[OF equivalent])
  have bm: "b \<in> domain (stock n)" by (rule book_leibniz_right[OF equivalent])
  have operation: "denote g (NLam n M) \<in> domain (Arr (stock n) \<tau>)"
    by (rule denote_type[OF UNIV_I book_language_Lam[OF language] typed])
  have application: "book_leibniz_equiv domain app V \<tau>
    (app (stock n) \<tau> (denote g (NLam n M)) a) (app (stock n) \<tau> (denote g (NLam n M)) b)"
    by (rule book_leibniz_argument_cong[OF rich typed equivalent operation])
  have first: "app (stock n) \<tau> (denote g (NLam n M)) a = denote (g(n := a)) M"
    by (rule book_full_lambda_application[OF language typed am])
  have second: "app (stock n) \<tau> (denote g (NLam n M)) b = denote (g(n := b)) M"
    by (rule book_full_lambda_application[OF language typed bm])
  show ?thesis using application by (simp only: first second)
qed

lemma book_leibniz_denote_update:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock" and typed: "book_env_typed domain stock g"
    and language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and equivalent: "book_leibniz_equiv domain app V (stock n) (g n) a"
  shows "book_leibniz_equiv domain app V \<tau> (denote g M) (denote (g(n := a)) M)"
  using book_leibniz_denote_two_updates[where n=n and a="g n" and b=a, OF rich typed language equivalent]
  by simp

theorem book_leibniz_denote_finite_changes:
  fixes V :: "'v \<Rightarrow> bool"
  assumes finite: "finite X" and rich: "sg_rich stock"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and related: "\<And>n. n \<in> X \<Longrightarrow> book_leibniz_equiv domain app V (stock n) (g n) (h n)"
  shows "book_leibniz_equiv domain app V \<tau> (denote g M) (denote (book_paste_assignment X h g) M)"
  using finite related
proof (induction X rule: finite_induct)
  case empty
  have member: "denote g M \<in> domain \<tau>" by (rule denote_type[OF UNIV_I language gt])
  show ?case by (simp only: book_paste_empty; rule book_leibniz_refl[where D=domain and \<sigma>=\<tau>, OF member])
next
  case (insert n X)
  let ?k = "book_paste_assignment X h g"
  have restricted: "\<And>i. i \<in> X \<Longrightarrow> book_leibniz_equiv domain app V (stock i) (g i) (h i)"
    by (rule insert.prems) (rule insertI2, assumption)
  have first: "book_leibniz_equiv domain app V \<tau> (denote g M) (denote ?k M)"
    by (rule insert.IH[OF restricted])
  have kt: "book_env_typed domain stock ?k" by (rule book_paste_typed[OF ht gt])
  have fresh_value: "?k n = g n" by (rule book_paste_outside[OF insert.hyps(2)])
  have at_n: "book_leibniz_equiv domain app V (stock n) (g n) (h n)"
    by (rule insert.prems) (rule insertI1)
  have updated_pair: "book_leibniz_equiv domain app V (stock n) (?k n) (h n)"
    by (simp only: fresh_value; rule at_n)
  have second: "book_leibniz_equiv domain app V \<tau> (denote ?k M) (denote (?k(n := h n)) M)"
    by (rule book_leibniz_denote_update[OF rich kt language updated_pair])
  have combined: "book_leibniz_equiv domain app V \<tau> (denote g M) (denote (?k(n := h n)) M)"
    by (rule book_leibniz_trans[OF first second])
  show ?case using combined by (simp only: book_paste_insert)
qed

theorem book_leibniz_denote_assignments:
  fixes V :: "'v \<Rightarrow> bool"
  assumes rich: "sg_rich stock"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and language: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and related: "\<And>n. n \<in> named_fv M \<Longrightarrow> book_leibniz_equiv domain app V (stock n) (g n) (h n)"
  shows "book_leibniz_equiv domain app V \<tau> (denote g M) (denote h M)"
proof -
  let ?k = "book_paste_assignment (named_fv M) h g"
  have finite_changes: "book_leibniz_equiv domain app V \<tau> (denote g M) (denote ?k M)"
    by (rule book_leibniz_denote_finite_changes[OF named_fv_finite rich gt ht language related])
  have kt: "book_env_typed domain stock ?k" by (rule book_paste_typed[OF ht gt])
  have agree: "?k n = h n" if free: "n \<in> named_fv M" for n
    by (rule book_paste_agrees_left[where X="named_fv M" and g=h and h=g, OF free])
  have locality: "denote ?k M = denote h M"
    by (rule book_denote_locality[OF UNIV_I language kt ht agree])
  show ?thesis using finite_changes by (simp only: locality)
qed

end

end
