theory TS_To_XC_aux
  imports XC_Definition "../../poly-reductions/Lib/SAT_Definition"
begin
  
datatype index = Fst | Snd | Thd

datatype 'a xc_element = V 'a | C "'a lit set" | L "'a lit" "'a lit set"

fun var :: "'a lit \<Rightarrow> 'a" where 
"var (Neg a) = a" | "var (Pos a) = a"

fun vars :: "'a three_sat \<Rightarrow> 'a set" where
"vars [] = {}" |
"vars (x#xs) = (var ` x) \<union> vars xs"

lemma vars_correct:
"x \<in> vars F \<longleftrightarrow> x \<in> (var) ` \<Union> (set F)"
by (induction F) auto

fun comp_literals :: "'a three_sat \<Rightarrow> 'a xc_element set \<Rightarrow> 'a xc_element set" where
"comp_literals [] acc = acc" |
"comp_literals (x # xs) acc = comp_literals xs ({L a x | a. a \<in> x} \<union> acc)"

lemma sat_tail:
  "sat (x#xs) \<Longrightarrow> sat xs"
  apply (induction xs)
  apply (auto simp add: sat_def models_def)
  done 

lemma comp_literals_mono:
  "acc \<le> comp_literals F acc"
  apply (induction F arbitrary: acc)
  apply (auto simp add: three_cnf_sat_def sat_tail, force)
  done

lemma comp_literals_correct[simp]:
  "comp_literals F acc = acc \<union> {L l c| l c. c \<in> set F \<and> l \<in> c}" 
  apply (induction F arbitrary: acc)
  using comp_literals_mono 
  by fastforce+


section "splitting of the sat"

definition vars_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where
"vars_of_sat F = {V v |v. v \<in> vars F}"

definition clauses_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where 
"clauses_of_sat F = {C c| c. c\<in> set F}"

lemma clauses_of_sat_correct[simp]:
  "c \<in> set F \<Longrightarrow> C c \<in> clauses_of_sat F"
unfolding clauses_of_sat_def by blast

definition literals_of_sat :: "'a three_sat \<Rightarrow> 'a xc_element set" where
"literals_of_sat F = comp_literals F {}"

lemma literals_of_sat_correct[simp]:
  "\<lbrakk>c \<in> set F; l \<in> c\<rbrakk> \<Longrightarrow> L l c \<in> literals_of_sat F"
  unfolding literals_of_sat_def by simp


end