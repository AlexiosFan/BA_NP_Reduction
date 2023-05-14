theory weighted_problems_aux
  imports "../XC_To_SS/XC_To_SS_aux"
begin

section "A few NP-hard combinatorics problems"

definition "subset_sum_int_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"

definition "ss_lift_to_int \<equiv> (\<lambda>(as, s). ((map int as), int s))"

definition "size_ss_int_list \<equiv> \<lambda>(as, s). length as + 1"

definition "part \<equiv> {as::nat list. \<exists>xs. (\<forall>i < length xs. xs!i \<in> {0, 1}) \<and> length as = length xs 
  \<and> 2 * (\<Sum>i < length as. as ! i * xs ! i) =( \<Sum>i < length as. as ! i)}"

definition ss_list_to_part :: "nat list * nat \<Rightarrow> nat list" where
"ss_list_to_part \<equiv> \<lambda>(as, s). (if s \<le> (\<Sum> i < length as. as ! i) then ((\<Sum>i < length as. as ! i) + 1 - s) # (s + 1) # as else [1])"

definition "size_part \<equiv> length"

definition "knapsack \<equiv> {(S, w, b, W, B). finite S \<and> (\<exists>S' \<subseteq> S. sum w S' \<le> W \<and> sum b S' \<ge> B)}"

definition "ss_to_ks \<equiv> (\<lambda>(S, w, B). (S, w, w, B, B))"

definition "size_ks \<equiv> \<lambda>(S, w, b, W, B). card S"


subsection "a type lifting from natural numbers to integers for subset sum"

lemma subset_sum_nat_to_int_sound:
assumes "(as, s) \<in> subset_sum_list"
shows "(map int as, int s) \<in> subset_sum_int_list"
proof -
  from assms obtain xs where 
  "(\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as"
    unfolding subset_sum_list_def
    by blast 
  hence "(\<forall>i<length (map int xs).(map int xs)! i \<in> {0,1}) 
    \<and> (\<Sum>i<length (map int as). (map int as)! i * (map int xs) ! i) = int s 
    \<and> length (map int xs) = length (map int as)"
    by force
  then show ?thesis
    unfolding subset_sum_int_list_def
    by blast
qed 

lemma subset_sum_nat_to_int_complete:
assumes "(map int as, int s) \<in> subset_sum_int_list"
shows "(as, s) \<in> subset_sum_list"
proof -
  from assms obtain xs where xs_def:
  "(\<forall>i<length xs. xs ! i \<in> {0,1})"
    "(\<Sum>i<length (map int as). (map int as)! i * xs ! i) = int s"
    "length xs = length (map int as)"
    unfolding subset_sum_int_list_def
    by fast 
  from this(1) have "\<exists>ys. map int ys = xs"
    proof (induction xs)
      case (Cons a xs)
      then obtain ys where "map int ys = xs"
        by fastforce 
      moreover from Cons(2) have "a = 1 \<or> a = 0"
        by auto
      ultimately have "map int ((if a = 1 then 1 :: nat else 0 )# ys) = a # xs"
        by fastforce
      then show ?case
        by metis
    qed simp
  then obtain ys where "map int ys = xs"
    by blast
  with xs_def have "(\<forall>i<length ys. ys! i \<in> {0,1}) 
    \<and> (\<Sum>i<length as. as! i * ys ! i) = s 
    \<and> length ys = length as"
    by (auto, smt (verit) of_nat_eq_iff of_nat_mult of_nat_sum sum.cong)
  then show ?thesis 
    unfolding subset_sum_list_def
    by blast
qed 

lemma is_reduction_ss_lift_to_int:
"is_reduction ss_lift_to_int subset_sum_list subset_sum_int_list"
  unfolding is_reduction_def ss_lift_to_int_def
  using subset_sum_nat_to_int_sound subset_sum_nat_to_int_complete
  by auto


end 