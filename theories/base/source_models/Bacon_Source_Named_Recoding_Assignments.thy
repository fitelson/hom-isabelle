theory Bacon_Source_Named_Recoding_Assignments
  imports Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Assignments
begin

section \<open>Recoding typed partial assignments along an injective carrier map\<close>

text \<open>
  Send each Dσ to f[Dσ] and each defined g(n)=a to f(a), leaving
  undefined names undefined. For injective f, pulling back by inv f
  recovers every original assignment. Conversely, recoding a pullback
  recovers every assignment typed in the image domains.
  Source role: typed collections and adequate assignments in Bacon–Dorr
  Definition 3.1, pp.43–44, for later carrier recoding.

  Representation. Inverse values outside range f are unconstrained.
  Image-domain typing supplies the range condition wherever it is used.
  The f-after-inv identity on image values requires no injectivity; the
  inv-after-f identity and typed pullback do require it. These generic
  facts assume no model, nonempty domains, richness, countability, or
  special carrier type. They do not change names, syntax, or adequacy.
\<close>

definition named_image_domain :: "('v \<Rightarrow> 'w) \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow> otype \<Rightarrow> 'w set" where
  "named_image_domain f D \<sigma> = f ` D \<sigma>"

lemma named_image_domain_member:
  "a \<in> D \<sigma> \<Longrightarrow> f a \<in> named_image_domain f D \<sigma>"
  unfolding named_image_domain_def by (rule imageI; assumption)

lemma named_image_domain_member_obtain:
  assumes member: "b \<in> named_image_domain f D \<sigma>"
  obtains a where "b = f a" and "a \<in> D \<sigma>"
  using member unfolding named_image_domain_def by (elim imageE)

lemma named_image_domain_nonempty:
  "D \<sigma> \<noteq> {} \<Longrightarrow> named_image_domain f D \<sigma> \<noteq> {}"
  by (simp add: named_image_domain_def)

lemma named_image_domain_inv_member:
  assumes injective: "inj f" and member: "b \<in> named_image_domain f D \<sigma>"
  shows "inv f b \<in> D \<sigma>"
proof -
  obtain a where encoded: "b = f a" and original: "a \<in> D \<sigma>"
    by (rule named_image_domain_member_obtain[OF member])
  show ?thesis by (simp only: encoded inv_f_f[OF injective]; rule original)
qed

lemma named_image_domain_recode_inverse:
  assumes member: "b \<in> named_image_domain f D \<sigma>"
  shows "f (inv f b) = b"
proof -
  have in_range: "b \<in> f ` UNIV" using member unfolding named_image_domain_def by auto
  show ?thesis by (rule f_inv_into_f[where A=UNIV, OF in_range])
qed

definition named_map_assignment :: "('v \<Rightarrow> 'w) \<Rightarrow> 'v named_assignment \<Rightarrow> 'w named_assignment" where
  "named_map_assignment f g n = map_option f (g n)"

lemma named_map_assignment_value:
  assumes assigned: "g n = Some a"
  shows "named_map_assignment f g n = Some (f a)"
  by (simp add: named_map_assignment_def assigned)

lemma named_map_assignment_value_obtain:
  assumes assigned: "named_map_assignment f g n = Some b"
  obtains a where "g n = Some a" and "b = f a"
  using assigned unfolding named_map_assignment_def by (cases "g n") auto

lemma named_map_assignment_domain:
  "dom (named_map_assignment f g) = dom g"
  by (auto simp: dom_def named_map_assignment_def split: option.splits)

lemma named_map_assignment_adequate:
  "named_adequate (named_map_assignment f g) A \<longleftrightarrow> named_adequate g A"
  by (simp only: named_adequate_def named_map_assignment_domain)

lemma named_map_assignment_update:
  "named_map_assignment f (g(n := Some a)) = (named_map_assignment f g)(n := Some (f a))"
  by (rule ext, rename_tac k, case_tac "k = n") (simp_all add: named_map_assignment_def)

lemma named_map_assignment_comp:
  "named_map_assignment h (named_map_assignment f g) = named_map_assignment (h \<circ> f) g"
  by (rule ext, rename_tac n, case_tac "g n") (simp_all add: named_map_assignment_def)

lemma named_map_assignment_id:
  "named_map_assignment id g = g"
  by (rule ext, rename_tac n, case_tac "g n") (simp_all add: named_map_assignment_def)

lemma named_map_assignment_empty:
  "named_map_assignment f Map.empty = Map.empty"
  by (rule ext) (simp add: named_map_assignment_def)

subsection \<open>Typing and the two inverse equations\<close>

theorem named_map_assignment_typed:
  assumes typed: "named_env_typed D G g"
  shows "named_env_typed (named_image_domain f D) G (named_map_assignment f g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n b
  assume assigned: "named_map_assignment f g n = Some b"
  obtain a where original: "g n = Some a" and encoded: "b = f a"
    by (rule named_map_assignment_value_obtain[OF assigned])
  have member: "a \<in> D (G n)" by (rule named_env_value[OF typed original])
  show "b \<in> named_image_domain f D (G n)"
    by (simp only: encoded; rule named_image_domain_member[where f=f and D=D and \<sigma>="G n" and a=a, OF member])
qed

theorem named_map_assignment_inv_typed:
  assumes injective: "inj f" and typed: "named_env_typed (named_image_domain f D) G g"
  shows "named_env_typed D G (named_map_assignment (inv f) g)"
proof (unfold named_env_typed_def, intro allI impI)
  fix n a
  assume assigned: "named_map_assignment (inv f) g n = Some a"
  obtain b where original: "g n = Some b" and decoded: "a = inv f b"
    by (rule named_map_assignment_value_obtain[OF assigned])
  have member: "b \<in> named_image_domain f D (G n)" by (rule named_env_value[OF typed original])
  show "a \<in> D (G n)" by (simp only: decoded; rule named_image_domain_inv_member[OF injective member])
qed

theorem named_map_inv_map:
  assumes injective: "inj f"
  shows "named_map_assignment (inv f) (named_map_assignment f g) = g"
  by (rule ext, rename_tac n, case_tac "g n")
    (simp_all add: named_map_assignment_def inv_f_f[OF injective])

theorem named_map_map_inv:
  assumes typed: "named_env_typed (named_image_domain f D) G g"
  shows "named_map_assignment f (named_map_assignment (inv f) g) = g"
proof (rule ext)
  fix n
  show "named_map_assignment f (named_map_assignment (inv f) g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp add: named_map_assignment_def None)
  next
    case (Some b)
    have member: "b \<in> named_image_domain f D (G n)" by (rule named_env_value[OF typed Some])
    have inverse: "f (inv f b) = b" by (rule named_image_domain_recode_inverse[OF member])
    show ?thesis by (simp add: named_map_assignment_def Some inverse)
  qed
qed

end
