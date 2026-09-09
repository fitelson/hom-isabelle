theory Bacon_Book_Henkin_Name_Stages
  imports Bacon_Book_Minimal_Formula_Syntax
begin

section \<open>A fixed carrier for successive closed-predicate witness names\<close>

text \<open>
  Embed c∈Σσ as Original(c). At stage n+1, add a distinct name
  Witness(n,σ,F) for every closed F:σ→t in the stage-n language.
  Source role: supplying fresh names for the witness extensions of
  Bacon, Proposition 15.4, p.319, without enumerating predicates.

  Representation. The nested datatype uses the existing named-term BNF.
  Its predicate payload is part of a nonlogical NAME, not an object-language
  quotation or an additional term constructor. Object-language occurrences,
  typing and free variables continue to treat NConst(name,σ) as atomic.
  The natural-number index counts signature stages only. One stage may
  add arbitrarily many names; no countability assumption is imposed on Σ
  or the original name carrier.

  Scope. Only names and signatures are constructed. There are no witness
  formulas, consistency assertions, completed theories or model claims.
  These structural facts do not require a rich variable stock.
\<close>

datatype 'c book_henkin_name =
    BookOriginal 'c
  | BookWitness nat otype "('c book_henkin_name) book_named_term"

primrec book_henkin_signature ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> nat \<Rightarrow> ('c book_henkin_name) ssignature" where
  "book_henkin_signature \<Sigma> G 0 = (\<lambda>\<tau>. image BookOriginal (\<Sigma> \<tau>))"
| "book_henkin_signature \<Sigma> G (Suc n) = (\<lambda>\<tau>.
    book_henkin_signature \<Sigma> G n \<tau> \<union>
    {BookWitness n \<tau> F |F. named_fv F = {} \<and>
      book_in_language book_minimal_logical_type UNIV
        (book_henkin_signature \<Sigma> G n) G F (Arr \<tau> Prop)})"

section \<open>Increasing signatures and unchanged original-name membership\<close>

lemma book_henkin_signature_step:
  "book_henkin_signature \<Sigma> G n \<tau> \<subseteq> book_henkin_signature \<Sigma> G (Suc n) \<tau>"
  by (simp only: book_henkin_signature.simps; rule Un_upper1)

theorem book_henkin_signature_mono:
  assumes order: "m \<le> n"
  shows "book_henkin_signature \<Sigma> G m \<tau> \<subseteq> book_henkin_signature \<Sigma> G n \<tau>"
  using order
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  have equality: "m = 0" using zero.prems by simp
  show ?case by (simp only: equality; rule subset_refl)
next
  case (Suc n)
  show ?case
  proof (cases "m = Suc n")
    case True
    show ?thesis by (simp only: True; rule subset_refl)
  next
    case False
    have earlier: "m \<le> n" using Suc.prems False by arith
    have contained: "book_henkin_signature \<Sigma> G m \<tau> \<subseteq> book_henkin_signature \<Sigma> G n \<tau>"
      by (rule Suc.IH[OF earlier])
    show ?thesis by (rule subset_trans[OF contained book_henkin_signature_step])
  qed
qed

theorem book_henkin_signature_original_iff:
  "BookOriginal c \<in> book_henkin_signature \<Sigma> G n \<tau> \<longleftrightarrow> c \<in> \<Sigma> \<tau>"
  by (induction n) auto

corollary book_henkin_signature_original:
  assumes declared: "c \<in> \<Sigma> \<tau>"
  shows "BookOriginal c \<in> book_henkin_signature \<Sigma> G n \<tau>"
  by (simp only: book_henkin_signature_original_iff; rule declared)

lemma book_henkin_signature_witness:
  assumes closed: "named_fv F = {}"
    and predicate: "book_in_language book_minimal_logical_type UNIV
      (book_henkin_signature \<Sigma> G n) G F (Arr \<sigma> Prop)"
  shows "BookWitness n \<sigma> F \<in> book_henkin_signature \<Sigma> G (Suc n) \<sigma>"
  using closed predicate by auto

section \<open>The stage index proves freshness at every type\<close>

theorem book_henkin_signature_witness_index:
  assumes member: "BookWitness m \<sigma> F \<in> book_henkin_signature \<Sigma> G n \<tau>"
  shows "m < n"
  using member
proof (induction n rule: nat.induct[case_names zero Suc])
  case zero
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof (cases "BookWitness m \<sigma> F \<in> book_henkin_signature \<Sigma> G n \<tau>")
    case True
    have old_index: "m < n" by (rule Suc.IH[OF True])
    show ?thesis by (rule less_SucI[OF old_index])
  next
    case False
    have new_index: "m = n" using Suc.prems False by auto
    show ?thesis by (simp only: new_index; rule lessI)
  qed
qed

corollary book_henkin_signature_witness_fresh:
  "BookWitness n \<sigma> F \<notin> book_henkin_signature \<Sigma> G n \<tau>"
proof
  assume member: "BookWitness n \<sigma> F \<in> book_henkin_signature \<Sigma> G n \<tau>"
  have impossible: "n < n" by (rule book_henkin_signature_witness_index[OF member])
  show False using impossible by simp
qed

corollary book_henkin_signature_future_witness_fresh:
  assumes future: "n \<le> m"
  shows "BookWitness m \<sigma> F \<notin> book_henkin_signature \<Sigma> G n \<tau>"
proof
  assume member: "BookWitness m \<sigma> F \<in> book_henkin_signature \<Sigma> G n \<tau>"
  have earlier: "m < n" by (rule book_henkin_signature_witness_index[OF member])
  show False using future earlier by arith
qed

end
