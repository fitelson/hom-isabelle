theory Goodman_H_Preservation_Regression
  imports Goodman_H_Proof_Preservation
begin

section \<open>Proof-only foreign constants do not leak into the target signature\<close>

theorem gi_H_foreign_constant_regression:
  fixes G :: sgcontext
  assumes rich: "sg_rich G" and nt: "G n = Prop"
  shows "book_H ((\<lambda>_. {}) :: 'c ssignature) G (book_imp (NVar n) (NVar n))"
proof -
  let ?F = "Const ''proof_only_foreign'' Prop"
  let ?T = "Imp ?F ?F"
  let ?A = "Imp (Var 0) (Var 0)"
  have foreign: "[Prop] \<turnstile>\<^sub>H ?T"
    by (rule H_proves.PC; auto simp: prop_tautology_def)
  have bridge_type: "[Prop] \<turnstile> Imp ?T ?A : Prop"
    by (rule infer_type_sound; simp add: lookup_def)
  have bridge: "[Prop] \<turnstile>\<^sub>H Imp ?T ?A"
    by (rule H_proves.PC; simp add: prop_tautology_def bridge_type)
  have conclusion: "[Prop] \<turnstile>\<^sub>H ?A" by (rule H_proves.MP[OF foreign bridge])
  let ?k = "\<lambda>(_::string) (_::otype). (undefined :: 'c)"
  have transferred: "book_H (\<lambda>_. {}) G (gi_to_book G [n] ?k ?A)"
  proof (rule gi_H_preservation[OF rich conclusion])
    show "map G [n] = [Prop]" by (simp add: nt)
    show "distinct [n]" by simp
    show "gi_constants_admitted ?k (\<lambda>_. {}) ?A" by simp
  qed
  show ?thesis using transferred by simp
qed

text \<open>
  The displayed old derivation uses a foreign propositional constant in
  both premises of its final MP. The target signature is empty. This is
  a regression for the actual signature-elimination route, not a proof
  that the foreign constant is mathematically necessary for the conclusion.
  The arbitrary name map is irrelevant to the constant-free conclusion.
\<close>

end
