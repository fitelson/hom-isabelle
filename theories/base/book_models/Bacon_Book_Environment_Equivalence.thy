theory Bacon_Book_Environment_Equivalence
  imports Bacon_Book_Environment
begin

section \<open>The intersection environment condition and its separated clauses\<close>

text \<open>
  The book requires Jg(A) = Jh(B) when A ≡βη B and g,h agree on
  FV(A) ∩ FV(B) (Definition 14.13, p.302). This is equivalent to
  locality for a single term together with same-assignment βη invariance.
  For the nontrivial direction, paste g on FV(A) with h elsewhere.
  Agreement on the intersection makes the pasted assignment agree with
  h on FV(B), as well as with g on FV(A).

  Representation. Both endpoints retain admission and language guards,
  and both original assignments are total and typed. Pasting preserves
  that typing without any separate nonemptiness or richness assumption.
  The equivalence is packaged as ordinary locale-predicate theorems,
  not mutually interpreting sublocales. No paper BBK field is changed.
\<close>

locale book_environment_separated = book_interpretation_structure +
  assumes separated_locality:
    "A \<in> admitted \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock A \<sigma> \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> book_env_typed domain stock h \<Longrightarrow>
     (\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n) \<Longrightarrow> denote g A = denote h A"
    and separated_conversion:
    "A \<in> admitted \<Longrightarrow> B \<in> admitted \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock A \<sigma> \<Longrightarrow>
     book_in_language logical_type logical_signature signature stock B \<sigma> \<Longrightarrow>
     named_raw_beta_eta logical_type stock \<sigma> A B \<Longrightarrow>
     book_env_typed domain stock g \<Longrightarrow> denote g A = denote g B"

context book_environment_conditions
begin

theorem book_environment_to_separated:
  "book_environment_separated domain app logical_type logical_signature signature stock admitted denote"
  apply unfold_locales
   apply (rule book_denote_locality; assumption)
  apply (rule book_denote_conversion; assumption)
  done

end

context book_environment_separated
begin

lemma book_separated_intersection_environment:
  assumes aa: "A \<in> admitted" and ba: "B \<in> admitted"
    and al: "book_in_language logical_type logical_signature signature stock A \<sigma>"
    and bl: "book_in_language logical_type logical_signature signature stock B \<sigma>"
    and conversion: "named_raw_beta_eta logical_type stock \<sigma> A B"
    and gt: "book_env_typed domain stock g" and ht: "book_env_typed domain stock h"
    and overlap: "\<And>n. n \<in> named_fv A \<inter> named_fv B \<Longrightarrow> g n = h n"
  shows "denote g A = denote h B"
proof -
  let ?k = "book_paste_assignment (named_fv A) g h"
  have kt: "book_env_typed domain stock ?k" by (rule book_paste_typed[OF gt ht])
  have left_agree: "g n = ?k n" if free: "n \<in> named_fv A" for n
    by (rule sym[OF book_paste_agrees_left[where X="named_fv A" and g=g and h=h, OF free]])
  have right_agree: "?k n = h n" if free: "n \<in> named_fv B" for n
    by (rule book_paste_agrees_right[where X="named_fv A" and Y="named_fv B" and g=g and h=h,
      OF overlap free])
  have left: "denote g A = denote ?k A"
    by (rule separated_locality[OF aa al gt kt left_agree])
  have middle: "denote ?k A = denote ?k B"
    by (rule separated_conversion[OF aa ba al bl conversion kt])
  have right: "denote ?k B = denote h B"
    by (rule separated_locality[OF ba bl kt ht right_agree])
  show ?thesis by (rule trans[OF left trans[OF middle right]])
qed

theorem book_separated_to_environment:
  "book_environment_conditions domain app logical_type logical_signature signature stock admitted denote"
  apply unfold_locales
  apply (rule book_separated_intersection_environment; assumption)
  done

end

theorem book_environment_conditions_iff_separated:
  "book_environment_conditions D app L \<Lambda> \<Sigma> G admitted J \<longleftrightarrow>
    book_environment_separated D app L \<Lambda> \<Sigma> G admitted J"
proof
  assume conditions: "book_environment_conditions D app L \<Lambda> \<Sigma> G admitted J"
  interpret Env: book_environment_conditions D app L \<Lambda> \<Sigma> G admitted J by (rule conditions)
  show "book_environment_separated D app L \<Lambda> \<Sigma> G admitted J"
    by (rule Env.book_environment_to_separated)
next
  assume separated: "book_environment_separated D app L \<Lambda> \<Sigma> G admitted J"
  interpret Sep: book_environment_separated D app L \<Lambda> \<Sigma> G admitted J by (rule separated)
  show "book_environment_conditions D app L \<Lambda> \<Sigma> G admitted J"
    by (rule Sep.book_separated_to_environment)
qed

end
