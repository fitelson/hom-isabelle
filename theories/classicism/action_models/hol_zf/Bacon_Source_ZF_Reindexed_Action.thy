theory Bacon_Source_ZF_Reindexed_Action
  imports Bacon_Source_ZF_Encoded_Category
    Bacon_Classicism_Action_Development.Bacon_Source_Action
begin

section \<open>Arrow recoding leaves the action's values unchanged\<close>

text \<open>
  Replacing each arrow h by its code e(h) reindexes an action:
  e(h)*(x)=h*(x). The object fibers are retained verbatim.
  Source role: Definition 3.13, p.53, and the bounded carrier
  representation for Proposition 3.22, pp.57 and 72.

  This construction changes arrow codes only. It does not encode
  individual values, propositions, or function values. The resulting
  category and action are proved from the originals and the explicit
  bounded injection, not assumed as interpretation interfaces.
\<close>

definition paper_ZF_recode_transport ::
  "'a set \<Rightarrow> ('a \<Rightarrow> ZF) \<Rightarrow> ('a \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ZF \<Rightarrow> 'v \<Rightarrow> 'v" where
  "paper_ZF_recode_transport Arrows e t z x = t (inv_into Arrows e z) x"

lemma paper_ZF_recode_transport_on:
  assumes injective: "inj_on e Arrows" and arrow: "h \<in> Arrows"
  shows "paper_ZF_recode_transport Arrows e t (e h) x = t h x"
  by (simp only: paper_ZF_recode_transport_def inv_into_f_f[where A=Arrows and f=e, OF injective arrow])

theorem paper_ZF_reindex_action:
  assumes action: "paper_action Obj Arrows source target compose identity D t"
    and injective: "inj_on e Arrows" and bound: "image e Arrows \<subseteq> explode B"
  shows "paper_action Obj (explode (paper_ZF_image_code B e Arrows))
    (paper_ZF_recode_source Arrows e source) (paper_ZF_recode_target Arrows e target)
    (paper_ZF_recode_compose Arrows e compose) (paper_ZF_recode_identity e identity)
    D (paper_ZF_recode_transport Arrows e t)"
proof -
  interpret Original: paper_action Obj Arrows source target compose identity D t by (rule action)
  interpret Encoding: paper_ZF_category_encoding Obj Arrows source target compose identity e B
    by unfold_locales (rule injective, rule bound)
  interpret Coded: paper_category Obj Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity by (rule Encoding.paper_ZF_encoded_category)
  show ?thesis
  proof unfold_locales
    fix f x
    assume arrow: "f \<in> Encoding.coded_arrows" and member: "x \<in> D (Encoding.coded_source f)"
    have original_arrow: "Encoding.decode_arrow f \<in> Arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
    have source_member: "x \<in> D (source (Encoding.decode_arrow f))"
      using member by (simp only: paper_ZF_recode_source_def)
    have transported: "t (Encoding.decode_arrow f) x \<in> D (target (Encoding.decode_arrow f))"
      by (rule Original.transport_type[OF original_arrow source_member])
    show "paper_ZF_recode_transport Arrows e t f x \<in> D (Encoding.coded_target f)"
      using transported by (simp only: paper_ZF_recode_transport_def paper_ZF_recode_target_def)
  next
    fix W x
    assume object: "W \<in> Obj" and member: "x \<in> D W"
    show "paper_ZF_recode_transport Arrows e t (Encoding.coded_identity W) x = x"
      by (simp only: paper_ZF_recode_transport_def Encoding.paper_ZF_decode_coded_identity[OF object];
        rule Original.transport_identity[OF object member])
  next
    fix f g x
    assume fa: "f \<in> Encoding.coded_arrows" and ga: "g \<in> Encoding.coded_arrows"
      and meeting: "Encoding.coded_target f = Encoding.coded_source g" and member: "x \<in> D (Encoding.coded_source f)"
    have source_member: "x \<in> D (source (Encoding.decode_arrow f))"
      using member by (simp only: paper_ZF_recode_source_def)
    show "paper_ZF_recode_transport Arrows e t (Encoding.coded_compose g f) x =
        paper_ZF_recode_transport Arrows e t g (paper_ZF_recode_transport Arrows e t f x)"
      by (simp only: paper_ZF_recode_transport_def Encoding.paper_ZF_decode_coded_compose[OF fa ga meeting];
        rule Original.transport_compose[OF Encoding.paper_ZF_decode_arrow_type[OF fa]
          Encoding.paper_ZF_decode_arrow_type[OF ga] Encoding.paper_ZF_decoded_meeting[OF meeting] source_member])
  qed
qed

end
