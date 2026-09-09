theory Bacon_Book_ZF_Model_Operations
  imports Bacon_Book_ZF_Model_Data
begin

section \<open>The prescribed operations of Definition 18.1\<close>

type_synonym book_ZF_domains = "otype \<Rightarrow> ZF \<Rightarrow> ZF"
type_synonym book_ZF_counterparts = "otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF"

definition book_ZF_k :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> book_ZF_counterparts \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_k W R D i root \<sigma> \<tau> = Lambda (book_ZF_pairs W R (D \<sigma>) root)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D \<tau>) (Fst p)) (\<lambda>q. i \<sigma> (Fst p) (Fst q) (Snd p)))"

definition book_ZF_s :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_s W R D root \<sigma> \<tau> \<rho> = Lambda (book_ZF_pairs W R (D (Arr \<sigma> (Arr \<tau> \<rho>))) root)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D (Arr \<sigma> \<tau>)) (Fst p))
      (\<lambda>q. Lambda (book_ZF_pairs W R (D \<sigma>) (Fst q))
        (\<lambda>r. app (app (Snd p) (Opair (Fst r) (Snd r)))
          (Opair (Fst r) (app (Snd q) (Opair (Fst r) (Snd r)))))))"

definition book_ZF_if_future :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> book_ZF_counterparts \<Rightarrow> ZF \<Rightarrow> ZF" where
  "book_ZF_if_future W R D i root = Lambda (book_ZF_pairs W R (D Prop) root)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D Prop) (Fst p))
      (\<lambda>q. book_ZF_collect W R (Fst q)
        (\<lambda>u. \<not> Elem u (i Prop (Fst p) (Fst q) (Snd p)) \<or> Elem u (Snd q))))"

definition book_ZF_all :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_all W R D root \<sigma> = Lambda (book_ZF_pairs W R (D (Arr \<sigma> Prop)) root)
    (\<lambda>p. book_ZF_collect W R (Fst p)
      (\<lambda>v. \<forall>a\<in>explode (D \<sigma> v). Elem v (app (Snd p) (Opair v a))))"

definition book_ZF_eq :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> book_ZF_counterparts \<Rightarrow> ZF \<Rightarrow> otype \<Rightarrow> ZF" where
  "book_ZF_eq W R D i root \<sigma> = Lambda (book_ZF_pairs W R (D \<sigma>) root)
    (\<lambda>p. Lambda (book_ZF_pairs W R (D \<sigma>) (Fst p))
      (\<lambda>q. book_ZF_collect W R (Fst q) (\<lambda>u. i \<sigma> (Fst p) u (Snd p) = i \<sigma> (Fst q) u (Snd q))))"

fun book_ZF_logical_root :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> book_ZF_domains \<Rightarrow> book_ZF_counterparts \<Rightarrow> ZF \<Rightarrow> book_minimal_logical \<Rightarrow> ZF" where
  "book_ZF_logical_root W R D i root SImp = book_ZF_if_future W R D i root"
| "book_ZF_logical_root W R D i root (SBAll \<sigma>) = book_ZF_all W R D root \<sigma>"

lemma book_ZF_k_value:
  assumes first: "Elem (Opair w a) (book_ZF_pairs W R (D \<sigma>) root)"
    and second: "Elem (Opair v b) (book_ZF_pairs W R (D \<tau>) w)"
  shows "app (app (book_ZF_k W R D i root \<sigma> \<tau>) (Opair w a)) (Opair v b) = i \<sigma> w v a"
  by (simp only: book_ZF_k_def Lambda_app[OF first] Fst Snd Lambda_app[OF second])

lemma book_ZF_s_value:
  assumes first: "Elem (Opair w f) (book_ZF_pairs W R (D (Arr \<sigma> (Arr \<tau> \<rho>))) root)"
    and second: "Elem (Opair v g) (book_ZF_pairs W R (D (Arr \<sigma> \<tau>)) w)"
    and third: "Elem (Opair u a) (book_ZF_pairs W R (D \<sigma>) v)"
  shows "app (app (app (book_ZF_s W R D root \<sigma> \<tau> \<rho>) (Opair w f)) (Opair v g)) (Opair u a) =
    app (app f (Opair u a)) (Opair u (app g (Opair u a)))"
  by (simp only: book_ZF_s_def Lambda_app[OF first] Fst Snd Lambda_app[OF second] Lambda_app[OF third])

lemma book_ZF_if_future_value:
  assumes first: "Elem (Opair w p) (book_ZF_pairs W R (D Prop) root)"
    and second: "Elem (Opair v q) (book_ZF_pairs W R (D Prop) w)"
  shows "app (app (book_ZF_if_future W R D i root) (Opair w p)) (Opair v q) =
    book_ZF_collect W R v (\<lambda>u. \<not> Elem u (i Prop w v p) \<or> Elem u q)"
  by (simp only: book_ZF_if_future_def Lambda_app[OF first] Fst Snd Lambda_app[OF second])

lemma book_ZF_all_value:
  assumes first: "Elem (Opair w f) (book_ZF_pairs W R (D (Arr \<sigma> Prop)) root)"
  shows "app (book_ZF_all W R D root \<sigma>) (Opair w f) =
    book_ZF_collect W R w (\<lambda>v. \<forall>a\<in>explode (D \<sigma> v). Elem v (app f (Opair v a)))"
  by (simp only: book_ZF_all_def Lambda_app[OF first] Fst Snd)

lemma book_ZF_eq_value:
  assumes first: "Elem (Opair w a) (book_ZF_pairs W R (D \<sigma>) root)"
    and second: "Elem (Opair v b) (book_ZF_pairs W R (D \<sigma>) w)"
  shows "app (app (book_ZF_eq W R D i root \<sigma>) (Opair w a)) (Opair v b) =
    book_ZF_collect W R v (\<lambda>u. i \<sigma> w u a = i \<sigma> v u b)"
  by (simp only: book_ZF_eq_def Lambda_app[OF first] Fst Snd Lambda_app[OF second])

text \<open>
  These are actual set-theoretic function graphs, defined for arbitrary
  W,R,D,i. Modelhood will require their membership in the chosen
  domains; no such membership is built into these definitions.
  Implication uses the explicitly documented future restriction of
  the printed W-complement. All comprehensions and application
  domains retain their future guards. No interpreter is supplied.
\<close>

end
