theory Bacon_Book_Name_Countability
  imports Bacon_Book_Classicism_Henkin_Reserve "HOL-Library.Countable_Set"
begin

section \<open>Countable syntax carriers for the book's countable-language construction\<close>

instance otype :: countable
  by countable_datatype

instance book_minimal_logical :: countable
  by countable_datatype

instance named_term :: (countable, countable) countable
  by countable_datatype

instance book_henkin_name :: (countable) countable
  by countable_datatype

theorem book_henkin_name_carrier_countable:
  "countable (UNIV :: (('c::countable) book_henkin_name) set)"
  by simp

text \<open>
  The nested witness-name datatype is countable when the original
  name carrier is countable. These are proved datatype instances,
  not cardinality assumptions added to the earlier arbitrary-carrier
  Henkin extension theorem. The book's displayed construction begins
  with a countable signature (p.398). Transport from countably many
  declared names in a larger carrier remains a separate guarded step.
\<close>

end
