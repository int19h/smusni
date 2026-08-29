theory Smoke
  imports Main
begin

datatype raw_content = Rep_A | Rep_A' | Rep_B

fun content_class :: "raw_content \<Rightarrow> nat" where
  "content_class Rep_A = 0"
| "content_class Rep_A' = 0"
| "content_class Rep_B = 1"

definition content_rel :: "raw_content \<Rightarrow> raw_content \<Rightarrow> bool" where
  "content_rel left right \<longleftrightarrow> content_class left = content_class right"

lemma content_rel_equiv: "equivp content_rel"
  unfolding equivp_def reflp_def symp_def transp_def content_rel_def fun_eq_iff
  by auto

quotient_type content = raw_content / content_rel
  by (rule content_rel_equiv)

lift_definition class_of :: "content \<Rightarrow> nat" is content_class
  unfolding content_rel_def by simp

lemma class_of_nontrivial: "\<exists>left right :: content. class_of left \<noteq> class_of right"
  by (transfer, rule exI[of _ Rep_A], rule exI[of _ Rep_B], simp)

lemma "\<forall>left right :: content. left = right"
  nitpick [expect = genuine]
  oops

end
