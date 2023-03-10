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

fun comp_literals :: "'a three_sat \<Rightarrow> 'a xc_element set \<Rightarrow> 'a xc_element set" where
"comp_literals [] acc = acc" |
"comp_literals (x # xs) acc = (
    if card x = 3 then comp_literals xs ({L a x | a. a \<in> x} \<union> acc)
    else {})"

lemma sat_tail:
  "sat (x#xs) \<Longrightarrow> sat xs"
  apply (induction xs)
  apply (auto simp add: sat_def models_def)
  done 

lemma comp_literals_mono:
  "F \<in> three_cnf_sat \<Longrightarrow> acc \<le> comp_literals F acc"
  apply (induction F arbitrary: acc)
  apply (auto simp add: three_cnf_sat_def sat_tail, force)
  done 

end