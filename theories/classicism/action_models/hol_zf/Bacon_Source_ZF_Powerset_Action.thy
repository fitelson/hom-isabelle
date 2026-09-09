theory Bacon_Source_ZF_Powerset_Action
  imports Bacon_Source_ZF_Powerset_Coding
begin

section \<open>Separation constructs powerset transport\<close>

text \<open>
  For f:W→V, define fᴾ(p)={i∈out(V) | i∘f∈p}.
  Source: Example 3.15, p.54. The displayed internal separation
  decodes to precisely the generic powerset transport.

  Typing and decoding are properties of the actual set constructor.
  Identity and composition are proved below from a supplied category
  whose arrows are explode(A). No extra action or model field is
  assumed, and no independent X/Y fibers enter this base action.
\<close>

definition paper_ZF_powerset_transport_code ::
  "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> (ZF \<Rightarrow> ZF \<Rightarrow> ZF) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_powerset_transport_code A source target compose f p =
    Sep (paper_ZF_outgoing_code A source (target f)) (\<lambda>i. Elem (compose i f) p)"

lemma paper_ZF_powerset_transport_code_type:
  "paper_ZF_powerset_transport_code A source target compose f p \<in>
    explode (paper_ZF_powerset_code A source (target f))"
  by (auto simp: paper_ZF_powerset_transport_code_def paper_ZF_powerset_code_def
    explode_Elem Power subset_def Sep)

theorem paper_ZF_decode_powerset_transport:
  "explode (paper_ZF_powerset_transport_code A source target compose f p) =
    paper_powerset_transport (explode A) source target compose f (explode p)"
  by (auto simp only: paper_ZF_powerset_transport_code_def explode_Elem Sep
    paper_ZF_outgoing_code_member paper_powerset_transport_member)

theorem paper_ZF_powerset_transport_identity:
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and object: "W \<in> Obj" and member: "p \<in> explode (paper_ZF_powerset_code A source W)"
  shows "paper_ZF_powerset_transport_code A source target compose (identity W) p = p"
proof -
  interpret Category: paper_category Obj "explode A" source target compose identity by (rule category)
  have decoded: "explode p \<in> paper_powerset_fiber (explode A) source W"
    by (rule paper_ZF_decode_powerset_type[OF member])
  have equality: "explode (paper_ZF_powerset_transport_code A source target compose (identity W) p) = explode p"
    by (simp only: paper_ZF_decode_powerset_transport;
      rule Category.paper_powerset_transport_identity[OF object decoded])
  show ?thesis by (rule injD[OF inj_explode equality])
qed

theorem paper_ZF_powerset_transport_compose:
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and first: "f \<in> explode A" and second: "g \<in> explode A" and meeting: "target f = source g"
  shows "paper_ZF_powerset_transport_code A source target compose (compose g f) p =
    paper_ZF_powerset_transport_code A source target compose g
      (paper_ZF_powerset_transport_code A source target compose f p)"
proof -
  interpret Category: paper_category Obj "explode A" source target compose identity by (rule category)
  have equality: "explode (paper_ZF_powerset_transport_code A source target compose (compose g f) p) =
    explode (paper_ZF_powerset_transport_code A source target compose g
      (paper_ZF_powerset_transport_code A source target compose f p))"
    by (simp only: paper_ZF_decode_powerset_transport;
      rule Category.paper_powerset_transport_compose[OF first second meeting])
  show ?thesis by (rule injD[OF inj_explode equality])
qed

section \<open>The internal powerset codes form an actual action\<close>

text \<open>
  The action laws concern legitimate category arrows and fiber members.
  They are proved from the decoded laws and injectivity of explode,
  not imposed on the coded transport. This is one constructed base
  action relative to HOL-ZF, not an all-R carrier recursion or an
  action-model interpretation.
\<close>

theorem paper_ZF_powerset_action:
  assumes category: "paper_category Obj (explode A) source target compose identity"
  shows "paper_action Obj (explode A) source target compose identity
    (\<lambda>W. explode (paper_ZF_powerset_code A source W))
    (paper_ZF_powerset_transport_code A source target compose)"
proof -
  interpret Category: paper_category Obj "explode A" source target compose identity by (rule category)
  show ?thesis
  proof unfold_locales
    fix f p
    assume "f \<in> explode A" and "p \<in> explode (paper_ZF_powerset_code A source (source f))"
    show "paper_ZF_powerset_transport_code A source target compose f p \<in>
      explode (paper_ZF_powerset_code A source (target f))"
      by (rule paper_ZF_powerset_transport_code_type)
  next
    fix W p
    assume object: "W \<in> Obj" and member: "p \<in> explode (paper_ZF_powerset_code A source W)"
    show "paper_ZF_powerset_transport_code A source target compose (identity W) p = p"
      by (rule paper_ZF_powerset_transport_identity[OF category object member])
  next
    fix f g p
    assume first: "f \<in> explode A" and second: "g \<in> explode A" and meeting: "target f = source g"
      and "p \<in> explode (paper_ZF_powerset_code A source (source f))"
    show "paper_ZF_powerset_transport_code A source target compose (compose g f) p =
      paper_ZF_powerset_transport_code A source target compose g
        (paper_ZF_powerset_transport_code A source target compose f p)"
      by (rule paper_ZF_powerset_transport_compose[OF category first second meeting])
  qed
qed

end
