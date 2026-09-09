theory Bacon_Book_Two_Abstractions
  imports Bacon_Book_Full_Environment
begin

section \<open>Two actual abstraction applications at arbitrary types\<close>

text \<open>
  ((λx.λy.M)A)B denotes M under successive updates x ↦ ⟦A⟧ᵍ and
  y ↦ ⟦B⟧ᵍ. Both argument values are evaluated at the original g.
  Source: the application and environment conditions of Definition 14.13,
  p.302. No raw substitution of A or B, Functionality or proposition-only
  restriction is used. Repeated binder names are allowed by this general
  equation; later uses requiring both values retained prove distinctness.
\<close>

context book_full_environment
begin

lemma book_two_argument_updates_typed:
  assumes typed: "book_env_typed domain stock g"
    and A: "book_in_language logical_type logical_signature signature stock A (stock x)"
    and B: "book_in_language logical_type logical_signature signature stock B (stock y)"
  shows "book_env_typed domain stock ((g(x := denote g A))(y := denote g B))"
proof -
  have am: "denote g A \<in> domain (stock x)" by (rule denote_type[OF UNIV_I A typed])
  have bm: "denote g B \<in> domain (stock y)" by (rule denote_type[OF UNIV_I B typed])
  show ?thesis by (rule book_env_update[OF book_env_update[OF typed am] bm])
qed

theorem book_two_abstractions_denote:
  assumes typed: "book_env_typed domain stock g"
    and body: "book_in_language logical_type logical_signature signature stock M \<tau>"
    and A: "book_in_language logical_type logical_signature signature stock A (stock x)"
    and B: "book_in_language logical_type logical_signature signature stock B (stock y)"
  shows "denote g (NApp (NApp (NLam x (NLam y M)) A) B) =
    denote ((g(x := denote g A))(y := denote g B)) M"
proof -
  let ?F = "NLam x (NLam y M)"
  have inner: "book_in_language logical_type logical_signature signature stock (NLam y M) (Arr (stock y) \<tau>)"
    by (rule book_language_Lam[OF body])
  have head: "book_in_language logical_type logical_signature signature stock ?F (Arr (stock x) (Arr (stock y) \<tau>))"
    by (rule book_language_Lam[OF inner])
  have partial: "book_in_language logical_type logical_signature signature stock (NApp ?F A) (Arr (stock y) \<tau>)"
    by (rule book_language_App[OF head A])
  have am: "denote g A \<in> domain (stock x)" by (rule denote_type[OF UNIV_I A typed])
  have bm: "denote g B \<in> domain (stock y)" by (rule denote_type[OF UNIV_I B typed])
  have updated: "book_env_typed domain stock (g(x := denote g A))"
    by (rule book_env_update[OF typed am])
  have first_app: "denote g (NApp ?F A) =
    app (stock x) (Arr (stock y) \<tau>) (denote g ?F) (denote g A)"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I head A typed])
  have second_app: "denote g (NApp (NApp ?F A) B) =
    app (stock y) \<tau> (denote g (NApp ?F A)) (denote g B)"
    by (rule denote_app[OF UNIV_I UNIV_I UNIV_I partial B typed])
  have first_beta: "app (stock x) (Arr (stock y) \<tau>) (denote g ?F) (denote g A) =
    denote (g(x := denote g A)) (NLam y M)"
    by (rule book_full_lambda_application[OF inner typed am])
  have second_beta: "app (stock y) \<tau> (denote (g(x := denote g A)) (NLam y M)) (denote g B) =
    denote ((g(x := denote g A))(y := denote g B)) M"
    by (rule book_full_lambda_application[OF body updated bm])
  show ?thesis by (simp only: second_app first_app first_beta second_beta)
qed

end

end
