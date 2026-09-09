theory Bacon_Source_ZF_Embedded_Carriers
  imports Bacon_Source_ZF_Subset_Carriers
begin

section \<open>Subsets of an explicitly represented HOL carrier\<close>

text \<open>
  Suppose e is injective on U and e[U]⊆explode(A), for an actual
  HOL-ZF set A. Each S⊆U then has the concrete code
  Sep A (λz.z∈e[S]); its elements are exactly e[S].
  This supplies bounded carrier representations for Definition 3.18
  and Proposition 3.22, pp.55 and 72, without identifying arbitrary
  HOL sets with ZF sets.

  Representation: paper_ZF_image_code constructs the set by separation.
  The inverse is inv_into U e, whose laws are proved below on the
  displayed domains. The injection and set bound are explicit premises,
  not an assumed universe-wide decoder. Relative only to standard HOL-ZF;
  no Goodman, BBK-model, or action-model assumption is imported.
\<close>

definition paper_ZF_image_code :: "ZF \<Rightarrow> ('a \<Rightarrow> ZF) \<Rightarrow> 'a set \<Rightarrow> ZF" where
  "paper_ZF_image_code A e S = paper_ZF_encode_subset A (image e S)"

lemma paper_ZF_image_code_elements:
  assumes bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
  shows "explode (paper_ZF_image_code A e S) = image e S"
proof -
  have image_subset: "image e S \<subseteq> image e U" by (rule image_mono[OF subset])
  have represented: "image e S \<subseteq> explode A" by (rule subset_trans[OF image_subset bound])
  show ?thesis unfolding paper_ZF_image_code_def by (rule paper_ZF_decode_encode_subset[OF represented])
qed

lemma paper_ZF_image_code_member:
  assumes bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
  shows "Elem z (paper_ZF_image_code A e S) \<longleftrightarrow> (\<exists>x\<in>S. z = e x)"
  using paper_ZF_image_code_elements[OF bound subset]
  by (auto simp: explode_Elem[symmetric])

lemma paper_ZF_image_code_type:
  "paper_ZF_image_code A e S \<in> explode (Power A)"
  unfolding paper_ZF_image_code_def by (rule paper_ZF_encode_subset_type)

theorem paper_ZF_image_code_bijection:
  assumes injective: "inj_on e U" and bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
  shows "bij_betw e S (explode (paper_ZF_image_code A e S))"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on e S" by (rule inj_on_subset[OF injective subset])
  show "image e S = explode (paper_ZF_image_code A e S)"
    by (rule paper_ZF_image_code_elements[OF bound subset, symmetric])
qed

lemma paper_ZF_image_inverse_left:
  assumes injective: "inj_on e U" and subset: "S \<subseteq> U" and member: "x \<in> S"
  shows "inv_into U e (e x) = x"
  by (rule inv_into_f_f[where f=e and A=U and x=x, OF injective subsetD[OF subset member]])

lemma paper_ZF_image_inverse_type:
  assumes injective: "inj_on e U" and bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
    and member: "z \<in> explode (paper_ZF_image_code A e S)"
  shows "inv_into U e z \<in> S"
proof -
  have image_member: "z \<in> image e S" using member by (simp only: paper_ZF_image_code_elements[OF bound subset])
  obtain x where xm: "x \<in> S" and shape: "z = e x" using image_member by blast
  show ?thesis by (simp only: shape paper_ZF_image_inverse_left[OF injective subset xm]; rule xm)
qed

lemma paper_ZF_image_inverse_right:
  assumes bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
    and member: "z \<in> explode (paper_ZF_image_code A e S)"
  shows "e (inv_into U e z) = z"
proof -
  have image_member: "z \<in> image e S" using member by (simp only: paper_ZF_image_code_elements[OF bound subset])
  have original_image: "z \<in> image e U" by (rule subsetD[OF image_mono[OF subset] image_member])
  show ?thesis by (rule f_inv_into_f[where f=e and A=U and y=z, OF original_image])
qed

theorem paper_ZF_image_inverse_bijection:
  assumes injective: "inj_on e U" and bound: "image e U \<subseteq> explode A" and subset: "S \<subseteq> U"
  shows "bij_betw (inv_into U e) (explode (paper_ZF_image_code A e S)) S"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (inv_into U e) (explode (paper_ZF_image_code A e S))"
  proof (rule inj_onI)
    fix z w
    assume zm: "z \<in> explode (paper_ZF_image_code A e S)" and wm: "w \<in> explode (paper_ZF_image_code A e S)"
      and equal: "inv_into U e z = inv_into U e w"
    have images: "e (inv_into U e z) = e (inv_into U e w)" by (simp only: equal)
    show "z = w" using images
      by (simp only: paper_ZF_image_inverse_right[OF bound subset zm] paper_ZF_image_inverse_right[OF bound subset wm])
  qed
next
  show "image (inv_into U e) (explode (paper_ZF_image_code A e S)) = S"
  proof
    show "image (inv_into U e) (explode (paper_ZF_image_code A e S)) \<subseteq> S"
      using paper_ZF_image_inverse_type[OF injective bound subset] by blast
    show "S \<subseteq> image (inv_into U e) (explode (paper_ZF_image_code A e S))"
    proof
      fix x
      assume member: "x \<in> S"
      have coded: "e x \<in> explode (paper_ZF_image_code A e S)"
        by (simp only: paper_ZF_image_code_elements[OF bound subset]; rule imageI[OF member])
      have image_member: "inv_into U e (e x) \<in> image (inv_into U e) (explode (paper_ZF_image_code A e S))"
        by (rule imageI[OF coded])
      show "x \<in> image (inv_into U e) (explode (paper_ZF_image_code A e S))"
        using image_member by (simp only: paper_ZF_image_inverse_left[OF injective subset member])
    qed
  qed
qed

section \<open>Composing carrier injections\<close>

lemma paper_ZF_composed_carrier_embedding:
  assumes first: "inj_on i Obj" and maps: "image i Obj \<subseteq> U"
    and second: "inj_on e U" and bound: "image e U \<subseteq> explode A"
  shows "inj_on (e \<circ> i) Obj \<and> image (e \<circ> i) Obj \<subseteq> explode A"
proof (rule conjI)
  show "inj_on (e \<circ> i) Obj"
  proof (rule inj_onI)
    fix x y
    assume xm: "x \<in> Obj" and ym: "y \<in> Obj" and equal: "(e \<circ> i) x = (e \<circ> i) y"
    have ix: "i x \<in> U" by (rule subsetD[OF maps imageI[OF xm]])
    have iy: "i y \<in> U" by (rule subsetD[OF maps imageI[OF ym]])
    have coded: "e (i x) = e (i y)" using equal by (simp only: o_apply)
    have originals: "i x = i y" by (rule inj_onD[OF second coded ix iy])
    show "x = y" by (rule inj_onD[OF first originals xm ym])
  qed
  show "image (e \<circ> i) Obj \<subseteq> explode A" using maps bound by auto
qed

text \<open>
  Category objects can be encoded through their identity arrows. The
  next theorem uses only the two identity/source equations needed for
  this step, not an imported category or action-model predicate.
  Arrow representability is still an explicit premise.
\<close>

theorem paper_ZF_identity_object_encoding:
  assumes identities: "\<And>x. x \<in> Obj \<Longrightarrow> ident x \<in> Arrows"
    and sources: "\<And>x. x \<in> Obj \<Longrightarrow> source (ident x) = x"
    and injective: "inj_on encode Arrows" and bound: "image encode Arrows \<subseteq> explode A"
  shows "bij_betw (encode \<circ> ident) Obj
    (explode (paper_ZF_image_code A (encode \<circ> ident) Obj))"
proof -
  have identity_inj: "inj_on ident Obj"
  proof (rule inj_onI)
    fix x y
    assume xm: "x \<in> Obj" and ym: "y \<in> Obj" and equal: "ident x = ident y"
    have endpoints: "source (ident x) = source (ident y)" by (simp only: equal)
    show "x = y" using endpoints by (simp only: sources[OF xm] sources[OF ym])
  qed
  have identity_image: "image ident Obj \<subseteq> Arrows" using identities by blast
  have composed: "inj_on (encode \<circ> ident) Obj \<and> image (encode \<circ> ident) Obj \<subseteq> explode A"
    by (rule paper_ZF_composed_carrier_embedding[OF identity_inj identity_image injective bound])
  show ?thesis by (rule paper_ZF_image_code_bijection[OF conjunct1[OF composed] conjunct2[OF composed] subset_refl])
qed

end
