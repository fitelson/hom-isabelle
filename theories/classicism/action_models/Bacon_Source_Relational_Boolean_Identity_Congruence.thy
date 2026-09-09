theory Bacon_Source_Relational_Boolean_Identity_Congruence
  imports Bacon_Source_Relational_Application_Congruence
begin

lemma paper_R_boolean_binary_operator_language:
  assumes operator_type: "paper_logical_type l = Arr Prop (Arr Prop Prop)"
  shows "paper_R_in_language \<Sigma> G (NLogical l) (Arr Prop (Arr Prop Prop))"
proof -
  have rt: "paper_R_type (paper_logical_type l)" by (simp add: operator_type)
  have typed: "paper_R_has_type G (NLogical l) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G and l=l, OF rt] by (simp only: operator_type)
  show ?thesis unfolding paper_R_in_language_def by (rule conjI[OF typed]; simp)
qed

lemma paper_R_named_identity_boolean_binary:
  assumes rich: "paper_R_rich G" and operator_type: "paper_logical_type l = Arr Prop (Arr Prop Prop)"
    and al: "paper_R_in_language \<Sigma> G A Prop" and a'l: "paper_R_in_language \<Sigma> G A' Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop" and b'l: "paper_R_in_language \<Sigma> G B' Prop"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop A A')"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop B B')"
  shows "paper_R_named_derivable \<Sigma> G S
    (named_paper_eq Prop (NApp (NApp (NLogical l) A) B) (NApp (NApp (NLogical l) A') B'))"
proof -
  have op: "paper_R_in_language \<Sigma> G (NLogical l) (Arr Prop (Arr Prop Prop))"
    by (rule paper_R_boolean_binary_operator_language[OF operator_type])
  have left: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A) (Arr Prop Prop)" by (rule paper_R_language_App[OF op al])
  have right: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A') (Arr Prop Prop)" by (rule paper_R_language_App[OF op a'l])
  have heads: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (Arr Prop Prop) (NApp (NLogical l) A) (NApp (NLogical l) A'))"
    by (rule paper_R_named_identity_App_argument[OF rich op al a'l first])
  show ?thesis by (rule paper_R_named_identity_App[OF rich left right bl b'l heads second])
qed

lemma paper_R_named_identity_boolean_and:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and a'l: "paper_R_in_language \<Sigma> G A' Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and b'l: "paper_R_in_language \<Sigma> G B' Prop"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop A A')"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop B B')"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop (named_paper_and A B) (named_paper_and A' B'))"
  unfolding named_paper_and_def
  by (rule paper_R_named_identity_boolean_binary[OF rich _ al a'l bl b'l first second]; simp)

lemma paper_R_named_identity_boolean_or:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and a'l: "paper_R_in_language \<Sigma> G A' Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and b'l: "paper_R_in_language \<Sigma> G B' Prop"
    and first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop A A')"
    and second: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop B B')"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop (named_paper_or A B) (named_paper_or A' B'))"
  unfolding named_paper_or_def
  by (rule paper_R_named_identity_boolean_binary[OF rich _ al a'l bl b'l first second]; simp)

lemma paper_R_named_identity_boolean_not:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A Prop"
    and bl: "paper_R_in_language \<Sigma> G B Prop"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop A B)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq Prop (named_paper_not A) (named_paper_not B))"
proof -
  have typed: "paper_R_has_type G (NLogical SNot) (Arr Prop Prop)"
    using paper_R_has_type.Logical[where G=G and l=SNot] by simp
  have op: "paper_R_in_language \<Sigma> G (NLogical SNot) (Arr Prop Prop)"
    unfolding paper_R_in_language_def by (rule conjI[OF typed]; simp)
  show ?thesis unfolding named_paper_not_def by (rule paper_R_named_identity_App_argument[OF rich op al bl equality])
qed

text \<open>
  These are native Ref/LL/application consequences for the literal
  Boolean terms. They transport GIVEN object-language identities;
  they do not infer identity merely from a shared truth value.
  Source: the scalar Boolean identity calculations of pp.16–17,
  used in the modal step of p.52 n.73. No Top, A.3, modal rule,
  semantic Boolean algebra or model premise occurs.
\<close>

end
