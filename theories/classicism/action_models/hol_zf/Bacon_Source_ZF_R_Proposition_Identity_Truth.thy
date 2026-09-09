theory Bacon_Source_ZF_R_Proposition_Identity_Truth
  imports Bacon_Source_ZF_R_Truth_Profile_Coding
begin

section \<open>Identity membership recovers original truth\<close>

text \<open>
  idM∈fₜM(p) iff VM(p), for p∈Mₜ. Only the identity's
  on-domain equation is used; selected homomorphisms need not preserve
  truth. Source: Definition 3.10, p.50, and Proposition 3.22, p.72.
  This statement needs neither quasi-Fregeanness nor a type decoder.
\<close>

context paper_ZF_R_profile_encoding
begin

lemma paper_ZF_R_proposition_identity_truth:
  assumes object: "M \<in> objects" and member: "p \<in> paper_bbk_domain M Prop"
  shows "Elem (Encoding.coded_identity M) (proposition_code M p) = paper_bbk_valuation M p"
proof -
  have arrow: "paper_typed_identity paper_bbk_domain M \<in> arrows"
    by (rule Encoding.identity_arrow[OF object])
  have fixed: "paper_arrow_map (paper_typed_identity paper_bbk_domain M) Prop p = p"
    by (rule paper_typed_identity_map_on[where D=paper_bbk_domain and A=M and \<sigma>=Prop, OF member])
  show ?thesis
    by (simp only: paper_ZF_recode_identity_def paper_ZF_R_truth_profile_code_on[OF arrow]
      paper_bbk_truth_profile_on_member arrow paper_typed_identity_endpoints fixed; simp)
qed

end

end
