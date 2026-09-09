theory Bacon_Source_ZF_Pure_Action_Completeness
  imports Bacon_Source_ZF_Action_Completeness "HOL-Library.Countable_Set"
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Pure_Classicism_Completeness
begin

section \<open>Pure Classicism needs no signature-size hypothesis\<close>

theorem paper_ZF_pure_classicism_action_iff:
  fixes A :: "'c paper_named_term"
  assumes rich: "paper_R_rich G" and language: "paper_R_in_language (\<lambda>_. {}) G A Prop"
  shows "paper_R_classicism_proves (\<lambda>_. {}) G A \<longleftrightarrow> paper_ZF_record_action_valid (\<lambda>_. {}) G A"
  by (rule paper_ZF_classicism_action_iff[where B=HOLZF.Nat,
    OF paper_ZF_nat_values_infinite paper_R_empty_signature_cardinal_bound rich language])

section \<open>Countably many declared names also fit the actual set Nat\<close>

lemma paper_ZF_countable_set_Nat_bound:
  fixes S :: "'a set"
  assumes countable: "countable S"
  shows "card_of S \<le>o card_of (explode HOLZF.Nat)"
proof -
  obtain f where injective: "inj_on (f :: 'a \<Rightarrow> nat) S" by (rule countableE[OF countable])
  show ?thesis
  proof (rule card_of_ordLeqI[where f="\<lambda>x. nat2Nat (f x)"])
    show "inj_on (\<lambda>x. nat2Nat (f x)) S"
    proof (rule inj_onI)
      fix x y
      assume sx: "x \<in> S" and sy: "y \<in> S" and equal: "nat2Nat (f x) = nat2Nat (f y)"
      have codes: "f x = f y" by (rule injD[OF inj_nat2Nat equal])
      show "x = y" by (rule inj_onD[OF injective codes sx sy])
    qed
  next
    fix x
    assume "x \<in> S"
    show "nat2Nat (f x) \<in> explode HOLZF.Nat" by (simp only: explode_Elem; rule Elem_nat2Nat_Nat)
  qed
qed

corollary paper_ZF_countable_classicism_action_iff:
  assumes names: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and rich: "paper_R_rich G" and language: "paper_R_in_language \<Sigma> G A Prop"
  shows "paper_R_classicism_proves \<Sigma> G A \<longleftrightarrow> paper_ZF_record_action_valid \<Sigma> G A"
  by (rule paper_ZF_classicism_action_iff[where B=HOLZF.Nat,
    OF paper_ZF_nat_values_infinite paper_ZF_countable_set_Nat_bound[OF names] rich language])

text \<open>
  In the pure language the empty nonlogical signature has the required
  bound automatically. With countably many declared names, compose an
  injection of that declared set into nat with nat2Nat. Neither corollary
  assumes a countable ambient name type. Both use the actual HOL-ZF set
  Nat, and retain the R-rich stock and formula-language guard.
  No model, root, arrow coding map, or representation certificate is a
  premise. The universal validity predicate still ranges over all action
  data on its explicitly stated world-index carrier.
\<close>

end
