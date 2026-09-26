theory Bacon_Book_Lambda_I_Universal_Closure_Theories
  imports Bacon_Book_Lambda_I_Universal_Closure Bacon_Book_Lambda_I_Conversion
begin

section \<open>Replacing arbitrary premises by their universal closures\<close>

text \<open>
  S and UC(S) have exactly the same theory consequences, where UC(S)
  applies universal closure separately to each premise. Each formula has
  finitely many free variables; S itself need not be finite, countable,
  closed, or bounded in its free-variable names.

  Source role: Definition 15.2, p.317, and the preparation for the
  arbitrary-theory endpoint of Theorem 15.3, pp.320–321. This theorem
  justifies passing to closed PREMISES without narrowing that endpoint.
  It does not assert that the closed fragment is itself a theory under
  Definition 5.1: such a theory also contains open axiom instances.
\<close>

theorem book_lambda_I_universal_closures_equivalent:
  assumes rich: "sg_rich G"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) S) B
    \<longleftrightarrow> book_lambda_I_derivable \<Sigma> G S B"
proof
  assume derivation: "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) S) B"
  show "book_lambda_I_derivable \<Sigma> G S B"
  proof (rule book_lambda_I_derivable_cut[OF derivation])
    fix C
    assume member: "C \<in> image (book_lambda_I_universal_closure G) S"
    obtain A where original: "A \<in> S" and shape: "C = book_lambda_I_universal_closure G A"
      using member by blast
    have al: "book_lambda_I_formula \<Sigma> G A" by (rule language[OF original])
    have assumption: "book_lambda_I_derivable \<Sigma> G S A"
      by (rule book_lambda_I_derivable.Assumption[OF original al])
    show "book_lambda_I_derivable \<Sigma> G S C"
      using assumption by (simp only: shape book_lambda_I_universal_closure_iff[OF rich al, symmetric])
  qed
next
  assume derivation: "book_lambda_I_derivable \<Sigma> G S B"
  show "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) S) B"
  proof (rule book_lambda_I_derivable_cut[OF derivation])
    fix A
    assume member: "A \<in> S"
    have al: "book_lambda_I_formula \<Sigma> G A" by (rule language[OF member])
    have closed_member: "book_lambda_I_universal_closure G A \<in> image (book_lambda_I_universal_closure G) S"
      by (rule imageI[OF member])
    have closed_language: "book_lambda_I_formula \<Sigma> G (book_lambda_I_universal_closure G A)"
      by (rule book_lambda_I_universal_closure_language[OF al])
    have assumption: "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) S)
      (book_lambda_I_universal_closure G A)"
      by (rule book_lambda_I_derivable.Assumption[OF closed_member closed_language])
    show "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) S) A"
      using assumption by (simp only: book_lambda_I_universal_closure_iff[OF rich al])
  qed
qed

theorem book_lambda_I_universal_closures_closed_fragment:
  assumes rich: "sg_rich G" and theory_ok: "book_lambda_I_higher_order_theory \<Sigma> G T"
  shows "image (book_lambda_I_universal_closure G) T = {A\<in>T. named_fv A = {}}"
proof
  show "image (book_lambda_I_universal_closure G) T \<subseteq> {A\<in>T. named_fv A = {}}"
  proof
    fix C
    assume member: "C \<in> image (book_lambda_I_universal_closure G) T"
    obtain A where original: "A \<in> T" and shape: "C = book_lambda_I_universal_closure G A"
      using member by blast
    have al: "book_lambda_I_formula \<Sigma> G A"
      using theory_ok original unfolding book_lambda_I_higher_order_theory_def by blast
    have assumption: "book_lambda_I_derivable \<Sigma> G T A"
      by (rule book_lambda_I_derivable.Assumption[OF original al])
    have derived: "book_lambda_I_derivable \<Sigma> G T (book_lambda_I_universal_closure G A)"
      using assumption by (simp only: book_lambda_I_universal_closure_iff[OF rich al, symmetric])
    have in_theory: "book_lambda_I_universal_closure G A \<in> T"
      by (rule book_lambda_I_contains_derivation[OF theory_ok derived subset_refl])
    show "C \<in> {A\<in>T. named_fv A = {}}"
      using in_theory by (simp add: shape book_lambda_I_universal_closure_closed)
  qed
next
  show "{A\<in>T. named_fv A = {}} \<subseteq> image (book_lambda_I_universal_closure G) T"
  proof
    fix A
    assume member: "A \<in> {A\<in>T. named_fv A = {}}"
    have original: "A \<in> T" and closed: "named_fv A = {}" using member by auto
    have in_image: "book_lambda_I_universal_closure G A \<in> image (book_lambda_I_universal_closure G) T"
      by (rule imageI[OF original])
    show "A \<in> image (book_lambda_I_universal_closure G) T"
      using in_image by (simp only: book_lambda_I_universal_closure_of_closed[OF closed])
  qed
qed

corollary book_lambda_I_closed_fragment_equivalent:
  assumes rich: "sg_rich G" and theory_ok: "book_lambda_I_higher_order_theory \<Sigma> G T"
  shows "book_lambda_I_derivable \<Sigma> G {A\<in>T. named_fv A = {}} B
    \<longleftrightarrow> book_lambda_I_derivable \<Sigma> G T B"
proof -
  have language: "book_lambda_I_formula \<Sigma> G A" if "A \<in> T" for A
    using theory_ok that unfolding book_lambda_I_higher_order_theory_def by blast
  have equivalence: "book_lambda_I_derivable \<Sigma> G (image (book_lambda_I_universal_closure G) T) B
    \<longleftrightarrow> book_lambda_I_derivable \<Sigma> G T B"
    by (rule book_lambda_I_universal_closures_equivalent[OF rich language])
  show ?thesis using equivalence
    by (simp only: book_lambda_I_universal_closures_closed_fragment[OF rich theory_ok])
qed

end
