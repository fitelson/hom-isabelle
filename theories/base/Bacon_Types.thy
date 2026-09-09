theory Bacon_Types
  imports Main
begin

section \<open>Object-language types\<close>

text \<open>
  These are the simple types of the object language, not Isabelle/HOL types.
  The base type \<open>Ind\<close> is for individuals and \<open>Prop\<close> is for propositions.

  In Bacon's notation, \<open>Ind\<close> is \<open>e\<close>, \<open>Prop\<close> is \<open>t\<close>, and
  \<open>Arr \<sigma> \<tau>\<close> is \<open>\<sigma> \<rightarrow> \<tau>\<close>.  Since \<open>Arr\<close> is unrestricted, this is
  Bacon's full simple-type system F, not the relational subsystem R used by
  default in parts of Bacon and Dorr's paper.  The function \<open>order\<close> is an
  Isabelle bookkeeping rank; it is not an additional object-language notion.
\<close>

datatype otype =
    Ind
  | Prop
  | Arr otype otype

notation Arr (infixr "\<rightarrow>\<^sub>o" 200)

fun order :: "otype \<Rightarrow> nat" where
  "order Ind = 0"
| "order Prop = 0"
| "order (\<sigma> \<rightarrow>\<^sub>o \<tau>) = max (Suc (order \<sigma>)) (order \<tau>)"

lemma order_nonzero_if_arrow:
  "order (\<sigma> \<rightarrow>\<^sub>o \<tau>) > 0"
  by simp

end
