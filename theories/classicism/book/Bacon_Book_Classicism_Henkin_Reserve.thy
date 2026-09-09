theory Bacon_Book_Classicism_Henkin_Reserve
  imports Bacon_Book_Classicism_Henkin_Extension
begin

section \<open>An explicit infinite reserve outside the constructed signature\<close>

lemma book_henkin_open_payload_never_declared:
  assumes open_payload: "named_fv F \<noteq> {}"
  shows "BookWitness n \<sigma> F \<notin> book_henkin_signature \<Sigma> G k \<tau>"
  using open_payload by (induction k) auto

lemma book_henkin_open_payload_outside_full:
  assumes open_payload: "named_fv F \<noteq> {}"
  shows "BookWitness n \<sigma> F \<notin> book_henkin_full_signature \<Sigma> G \<tau>"
  using book_henkin_open_payload_never_declared[OF open_payload]
  unfolding book_henkin_full_signature_def by blast

definition book_henkin_reserved_name :: "otype \<Rightarrow> nat \<Rightarrow> 'c book_henkin_name" where
  "book_henkin_reserved_name \<sigma> n = BookWitness n \<sigma> (NVar 0)"

lemma book_henkin_reserved_name_injective:
  "inj (book_henkin_reserved_name \<sigma> :: nat \<Rightarrow> 'c book_henkin_name)"
  by (rule injI; simp add: book_henkin_reserved_name_def)

lemma book_henkin_reserved_name_unused:
  "book_henkin_reserved_name \<sigma> n \<notin> book_henkin_full_signature \<Sigma> G \<tau>"
  unfolding book_henkin_reserved_name_def
  by (rule book_henkin_open_payload_outside_full; simp)

theorem book_henkin_unused_names_infinite:
  "infinite (UNIV - book_henkin_full_signature \<Sigma> G \<tau>)"
proof -
  have reserve: "infinite (range (book_henkin_reserved_name \<tau> :: nat \<Rightarrow> 'c book_henkin_name))"
    by (simp add: finite_image_iff[OF book_henkin_reserved_name_injective])
  have subset: "range (book_henkin_reserved_name \<tau>) \<subseteq> UNIV - book_henkin_full_signature \<Sigma> G \<tau>"
    using book_henkin_reserved_name_unused by blast
  show ?thesis using reserve subset finite_subset by blast
qed

text \<open>
  Witness-name payloads are parts of nonlogical names, not quotations
  in the object language. The signature construction declares names
  only for CLOSED predicate payloads. Names whose payload is NVar 0
  are therefore never declared, at any stage or in the union; their
  natural-number index gives an explicit injection into the complement.

  This proves an actual infinite reserve in the name carrier of this
  constructed extension. It does not yet transport repeated extensions
  into one fixed ambient carrier, prove countability of that ambient
  language, or supply all canonical successor worlds there.
\<close>

end
